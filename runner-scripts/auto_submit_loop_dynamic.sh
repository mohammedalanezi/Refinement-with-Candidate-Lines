#!/bin/bash
# auto_submit_loop_dynamic.sh
#
# Repeatedly runs submit_batch_dynamic.sh, waits for that round's array job to drain down to at most MAX_INFLIGHT_TO_TOP_UP pending/running tasks, then submits the next round. 
# Stops automatically once submit_batch_dynamic.sh reports "Nothing left to do" for the full range.
#
# Usage:
#   ./auto_submit_loop_dynamic.sh --account def-stevens --start 0 --end 6964 --time 03:00:00
#
# Top up as soon as the queue depth drops to 100 (instead of waiting for a full drain):
#   MAX_INFLIGHT_TO_TOP_UP=100 ./auto_submit_loop_dynamic.sh --account def-stevens --start 0 --end 6964 --time 03:00:00
#
# Any extra arguments are passed straight through to submit_batch_dynamic.sh, so all of its flags (--outputdir, --max-inflight, --throttle, --all, ...) work here too
#
# Stop it any time with Ctrl-C, or by deleting the lock file's PID from the system (SIGTERM/SIGINT are trapped and exit cleanly between rounds)

set -uo pipefail

WORKDIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SUBMIT_SCRIPT="$WORKDIR/submit_batch_dynamic.sh"

# ---------------------------------------------------------------------
# Tunables
# ---------------------------------------------------------------------
JOBNAME="tpls_refine"                 # must match #SBATCH --job-name in run_array_task_dynamic.sh
POLL_INTERVAL=1200                    # seconds between squeue checks while a round is in flight (20 min, jobs run for hours, no need to check more often)
POST_ROUND_SLEEP=30                   # short cooldown after a round drains before the next submit_batch_dynamic.sh call
MAX_INFLIGHT_TO_TOP_UP="${MAX_INFLIGHT_TO_TOP_UP:-0}"   # X: submit the next round once pending/running '$JOBNAME' tasks drop to <= this many (0 = old behavior, wait for a full drain)
LOCKFILE="$WORKDIR/.auto_submit_loop_dynamic.lock"
LOOPLOG="$WORKDIR/auto_submit_loop_dynamic.log"
# Per-round submit_batch_dynamic.sh output, kept for later debugging. In scratch since it can accumulate a lot of files 
# over a long run and scratch has more space/throughput. Falls back to WORKDIR if $SCRATCH isn't set for some reason (e.g. testing off-cluster)
ROUND_OUTPUT_DIR="${SCRATCH:-$WORKDIR}/sat_solver/auto_submit_rounds_dynamic"
MAX_CONSECUTIVE_FAILURES=5            # give up after this many submit_batch_dynamic.sh failures in a row

mkdir -p "$ROUND_OUTPUT_DIR"

# ---------------------------------------------------------------------
# Prevent overlapping instances of this wrapper
# ---------------------------------------------------------------------
exec 9>"$LOCKFILE"
if ! flock -n 9; then
    stale_pid=$(cat "$LOCKFILE" 2>/dev/null || true)
    echo "Another auto_submit_loop_dynamic.sh appears to be running (lock: $LOCKFILE, pid: ${stale_pid:-unknown})." >&2
    if [[ -n "${stale_pid:-}" ]] && ! kill -0 "$stale_pid" 2>/dev/null; then
        echo "That PID ($stale_pid) is not actually running -- the lock should have been released automatically." >&2
        echo "If this persists, check for a leftover $LOCKFILE from an unusual shutdown and remove it manually." >&2
    fi
    exit 1
fi
echo $$ >&9

# ---------------------------------------------------------------------
# Logging: mirror everything to a persistent log with timestamps
# ---------------------------------------------------------------------
log() {
    echo "[$(date '+%Y-%m-%d %H:%M:%S')] $*"
}
exec > >(tee -a "$LOOPLOG") 2>&1

# ---------------------------------------------------------------------
# Clean shutdown on Ctrl-C / SIGTERM: finish logging, don't leave the lock in a weird state 
# ---------------------------------------------------------------------
STOP=0
on_signal() {
    log "Received stop signal -- will exit after current step finishes."
    STOP=1
}
trap on_signal INT TERM

wait_for_queue_below_threshold() {
    local threshold="$MAX_INFLIGHT_TO_TOP_UP"
    if (( threshold > 0 )); then
        log "Waiting for '$JOBNAME' queue depth to drop to <= $threshold (polling every ${POLL_INTERVAL}s)..."
    else
        log "Waiting for '$JOBNAME' jobs to drain from the queue (polling every ${POLL_INTERVAL}s)..."
    fi
    while true; do
        (( STOP )) && return 1
        n=$(squeue -u "$USER" -h -r -n "$JOBNAME" -t PD,R -o "%i" 2>/dev/null | wc -l)
        if (( n <= threshold )); then
            log "Queue at $n pending/running '$JOBNAME' task(s), at or below threshold ($threshold) -- proceeding."
            return 0
        fi
        log "  still $n pending/running task(s) (threshold $threshold) -- sleeping ${POLL_INTERVAL}s"
        sleep "$POLL_INTERVAL" &
        wait $!
    done
}

log "=========================================================="
log "auto_submit_loop_dynamic.sh starting. Args to submit_batch_dynamic.sh: $*"
log "=========================================================="

# If we're restarting after an outage (e.g. login node reboot) and jobs  from a previous round are still queued/running, wait for those to
# drain first instead of immediately re-scanning, submit_batch_dynamic.sh will just find nothing new to do anyway, and this avoids a wasted I/O-heavy pass right at startup
n_inflight_at_start=$(squeue -u "$USER" -h -r -n "$JOBNAME" -t PD,R -o "%i" 2>/dev/null | wc -l)
if (( n_inflight_at_start > MAX_INFLIGHT_TO_TOP_UP )); then
    log "Found $n_inflight_at_start '$JOBNAME' task(s) already in the queue at startup"
    log "(likely from before a restart) -- waiting for those to drop to <= $MAX_INFLIGHT_TO_TOP_UP before submitting more."
    wait_for_queue_below_threshold || { log "Stopped while waiting at startup."; exit 0; }
fi

consecutive_failures=0
round=0

while (( ! STOP )); do
    round=$(( round + 1 ))
    log "---- Round $round: invoking submit_batch_dynamic.sh ----"

    # Capture output so we can inspect it for the terminal "nothing left" message, while still streaming it live to the log via tee. Kept afterwards (not deleted) as a per-round file 
    # for later debugging, this makes it easy to jump straight to "what did round N do"
    out_file="$ROUND_OUTPUT_DIR/round_$(printf '%04d' "$round")_$(date '+%Y%m%d_%H%M%S').log"
    "$SUBMIT_SCRIPT" "$@" > >(tee "$out_file") 2>&1
    rc=$?

    if (( rc != 0 )) && grep -q "AssocMaxSubmitJobLimit" "$out_file"; then
        log "Hit AssocMaxSubmitJobLimit (Slurm's own submit-count cap) -- this isn't a real failure,"
        log "just means our queue-depth count was momentarily stale. Waiting for room, not counting as a failure."
        wait_for_queue_below_threshold || break
        sleep "$POST_ROUND_SLEEP"
        continue
    fi

    if (( rc != 0 )); then
        consecutive_failures=$(( consecutive_failures + 1 ))
        log "submit_batch_dynamic.sh exited with code $rc (failure $consecutive_failures/$MAX_CONSECUTIVE_FAILURES)."
        if (( consecutive_failures >= MAX_CONSECUTIVE_FAILURES )); then
            log "Too many consecutive failures, giving up."
            exit 1
        fi
        log "Backing off ${POST_ROUND_SLEEP}s before retrying."
        sleep "$POST_ROUND_SLEEP"
        continue
    fi
    consecutive_failures=0

    if grep -q "Nothing left to do in" "$out_file"; then
        log "submit_batch_dynamic.sh reports everything in the range is complete. Done!"
        break
    fi

    if grep -q "No room in the queue right now" "$out_file"; then
        log "Queue was already full; nothing new was submitted this round."
        # Still worth waiting, some of those in-flight jobs belong to this workflow and finishing them will free room next round
        wait_for_queue_below_threshold || break
        sleep "$POST_ROUND_SLEEP"
        continue
    fi

    if grep -qE "^Nothing eligible at --time=" "$out_file"; then
        log "Remaining indices all need more time than --time= currently allows."
        log "This loop won't increase --time automatically, stopping."
        log "Re-run with a larger --time to pick up the deferred indices."
        break
    fi

    # Normal case: a batch was submitted. Wait for the queue depth to drop to the top-up threshold before checking again
    wait_for_queue_below_threshold || break

    (( STOP )) && break
    log "Cooling down ${POST_ROUND_SLEEP}s before next round."
    sleep "$POST_ROUND_SLEEP"
done

log "auto_submit_loop_dynamic.sh exiting."