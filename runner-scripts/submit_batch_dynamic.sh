#!/bin/bash
# submit_batch_dynamic.sh
#
# Submits (or tops up) a SLURM job array that runs
#     ./template_dynamic i --r R --cube-start S --cube-end E --job-id JOBID
# for whichever indices i in [--start,--end] are not already completed and not already queued/running, fit as many under the account's job limit.
#
# Scripts (this file, run_array_task_dynamic.sh, lib_dynamic.sh, ranges.conf) live in your project space.
# All generated output (logs, solutions, proofs, dynamic clauses, slurm output) goes to $SCRATCH/sat_solver/runs_dynamic/ on the cluster.
#
# This is safe to re-run any time: it always recomputes what's left to do straight from the log files and from squeue, so there's no shared
# state between runs to get out of sync, and no long-lived coordinator process is required. Each array task is fully independent.
#
# Typical usage:
#   ./submit_batch_dynamic.sh --account def-yourpi
#   ./submit_batch_dynamic.sh --account def-yourpi --time 02:00:00   # round 1 (default)
#   ./submit_batch_dynamic.sh --account def-yourpi --time 04:00:00   # round 2: retries + longer-r ranges
#
# Re-run it as many times as you like (e.g. once whenever you check in, or from a tmux loop) until it reports "Nothing left to do."
#
set -uo pipefail

# ---------------------------------------------------------------------
# Defaults
# ---------------------------------------------------------------------
WORKDIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

RANGES_CONF="$WORKDIR/ranges.conf"
ARRAY_SCRIPT="$WORKDIR/run_array_task_dynamic.sh"
JOBNAME="tpls_refine"

# Where idxmap files are kept (safe to keep in project space -- small files).
IDXMAP_DIR="$WORKDIR/idxmaps_dynamic"

# Root output directory in scratch. Completion detection, Slurm output, and all per-template files live here. Must be the same value on both
# the login node (for completion scanning) and compute nodes (for writing). Defaults to $SCRATCH/sat_solver/runs_dynamic if not overridden via --outputdir.
OUTPUTDIR="${SCRATCH:-}/sat_solver/runs_dynamic"

START=0
END=6964
TIME_LIMIT="02:00:00"
MAX_INFLIGHT=900     # stay safely under the ~1000 pending+running job cap most Alliance Canada general-purpose clusters apply per account.
THROTTLE=""           # optional: cap concurrently RUNNING tasks this round, e.g. --throttle 100 -> sbatch --array=1-K%100
SUBMIT_ALL=0          # if 1 (--all flag), submit all eligible tasks at once ignoring MAX_INFLIGHT. Use with --throttle to let
                      # Slurm manage drip-feeding instead of re-running this script manually.
ACCOUNT=""

# Log file for all submit_batch_dynamic.sh runs. Each invocation appends a timestamped block so you have a full history of what was submitted when.
# Kept in project space alongside the scripts (not scratch) so it survives the 60-day scratch purge.
SUBMITLOG="$WORKDIR/submit_history_dynamic.log"
# ---------------------------------------------------------------------

source "$WORKDIR/lib_dynamic.sh"

while [[ $# -gt 0 ]]; do
    case "$1" in
        --account)      ACCOUNT="$2";    shift 2 ;;
        --time)         TIME_LIMIT="$2"; shift 2 ;;
        --start)        START="$2";      shift 2 ;;
        --end)          END="$2";        shift 2 ;;
        --outputdir)    OUTPUTDIR="$2";  shift 2 ;;
        --max-inflight) MAX_INFLIGHT="$2"; shift 2 ;;
        --throttle)     THROTTLE="$2";   shift 2 ;;
        --all)          SUBMIT_ALL=1;    shift 1 ;;
        --submitlog)    SUBMITLOG="$2";  shift 2 ;;
        -h|--help)
            grep '^#' "$0" | sed 's/^# \{0,1\}//'
            exit 0 ;;
        *) echo "Unknown argument: $1" >&2; exit 1 ;;
    esac
done

if [[ -z "$ACCOUNT" ]]; then
    echo "ERROR: --account is required (your RAP, e.g. def-yourpi or rrg-yourpi)." >&2
    exit 1
fi

if [[ -z "$OUTPUTDIR" ]]; then
    echo "ERROR: \$SCRATCH is not set and --outputdir was not given." >&2
    echo "       Run this on the cluster (where \$SCRATCH is set) or pass --outputdir explicitly." >&2
    exit 1
fi

mkdir -p "$IDXMAP_DIR" "$OUTPUTDIR"

# From this point on, all stdout is mirrored to the submit log.
# Each run appends a timestamped block so you have a full history of what was submitted when, without losing terminal output.
exec > >(tee -a "$SUBMITLOG") 2>&1
echo ""
echo "========================================================"
echo "submit_batch_dynamic.sh  $(date '+%Y-%m-%d %H:%M:%S')"
echo "  account=$ACCOUNT  time=$TIME_LIMIT  range=$START-$END"
echo "========================================================"

ROUND_SECONDS=$(parse_hms_to_seconds "$TIME_LIMIT")

echo "Output directory:      $OUTPUTDIR"
echo "Submit log:            $SUBMITLOG"

# ---- 1. What's already completed? (one pass over the output directory) ----
declare -A completed
build_completed_set "$OUTPUTDIR" completed

# ---- 2. What's currently queued or running from earlier submissions? ----
# Keyed "i:start:end" so distinct sections of the same template i are tracked independently.
declare -A inflight
while read -r jobtask; do
    [[ "$jobtask" == *_* ]] || continue
    jobid="${jobtask%%_*}"
    taskid="${jobtask##*_}"
    map="$IDXMAP_DIR/${jobid}.txt"
    [[ -f "$map" ]] || continue
    line=$(sed -n "${taskid}p" "$map" 2>/dev/null)
    [[ -n "$line" ]] || continue
    read -r real_i real_s real_e <<< "$line"
    [[ -n "${real_i:-}" ]] && inflight["${real_i}:${real_s:-0}:${real_e:-0}"]=1
done < <(squeue -u "$USER" -h -r -n "$JOBNAME" -t PD,R -o "%i" 2>/dev/null)

# ---- 3. Build this round's eligible candidate list ----
# Each candidate is "i start end", end=0 means an ordinary unsectioned job (the whole template); a nonzero end means one section of a
# template whose tuned estimate exceeded the 5-day split threshold (see list_pending_sections in lib_dynamic.sh).
candidates=()
deferred_needs_more_time=0
for i in $(seq "$START" "$END"); do
    key=$(printf "%04d" "$i")   # "0038"
    key="${key##0}"             # "038"  (matches lib_dynamic.sh)
    [[ -v completed[$key] ]] && continue
 
    template_dir="$OUTPUTDIR/template_$(printf '%04d' "$i")"
    pending=()
    if [[ -d "$template_dir" ]]; then
        while read -r s e; do
            [[ -z "${s:-}" ]] && continue
            pending+=("$s $e")
        done < <(list_pending_sections "$template_dir")
    else
        # Never attempted: one ordinary unsectioned job. (Whether it needs splitting is only knowable after its first tuning run.)
        pending+=("0 0")
    fi
 
    for se in "${pending[@]}"; do
        read -r s e <<< "$se"
        [[ -v inflight["${i}:${s}:${e}"] ]] && continue
 
        read -r r hours < <(lookup_params "$i" "$RANGES_CONF")
        need_seconds=$(( hours * 3600 ))
 
        if (( need_seconds > ROUND_SECONDS )); then
            deferred_needs_more_time=$(( deferred_needs_more_time + 1 ))
            continue
        fi
        candidates+=("$i $s $e")
    done
done

# ---- 4. How much room is there in the queue right now? ----
current_total=$(squeue -u "$USER" -h -r 2>/dev/null | wc -l)   # -r: one line per array task, which is how the submit cap counts
room=$(( MAX_INFLIGHT - current_total ))
 
n_candidates=${#candidates[@]}
echo "Range:                 $START-$END  ($(( END - START + 1 )) total)"
set +u
echo "Already completed:      ${#completed[@]}"
echo "Already queued/running: ${#inflight[@]}"
set -u
echo "Deferred (need > --time=$TIME_LIMIT): $deferred_needs_more_time"
echo "Eligible this round:    $n_candidates"
if (( SUBMIT_ALL )); then
    echo "Your jobs right now:    $current_total  (--all mode, ignoring MAX_INFLIGHT cap)"
else
    echo "Your jobs right now:    $current_total  (cap $MAX_INFLIGHT -> room for $room more)"
fi

if (( ! SUBMIT_ALL && room <= 0 )); then
    echo "No room in the queue right now -- re-run this script later."
    exit 0
fi

if (( n_candidates == 0 )); then
    if (( deferred_needs_more_time > 0 )); then
        echo "Nothing eligible at --time=$TIME_LIMIT, but $deferred_needs_more_time"
        echo "indices/sections need more time per ranges.conf (or the 5-day section"
        echo "budget). Re-run with a larger --time to pick those up."
    else
        echo "Nothing left to do in [$START,$END]. All done!"
    fi
    exit 0
fi

if (( SUBMIT_ALL )); then
    # Submit all eligible tasks at once; Slurm drip-feeds them via %THROTTLE.
    # Warn if no throttle is set -- submitting thousands of tasks with no concurrency cap is inconsiderate to other cluster users.
    if [[ -z "$THROTTLE" ]]; then
        echo "WARNING: --all used without --throttle. Consider adding --throttle 900" >&2
        echo "         so Slurm limits concurrent tasks automatically." >&2
    fi
    take=$n_candidates
else
    take=$room
    (( take > n_candidates )) && take=$n_candidates
fi

idxmap_tmp="$IDXMAP_DIR/pending_$$.txt"
printf '%s\n' "${candidates[@]:0:take}" > "$idxmap_tmp"
 
array_spec="1-${take}"
[[ -n "$THROTTLE" ]] && array_spec="${array_spec}%${THROTTLE}"

# Pass OUTPUTDIR into every compute node via --export so run_array_task_dynamic.sh writes to the same scratch path regardless of what $SCRATCH expands to on each node.
submit_out=$(sbatch --parsable \
    --job-name="$JOBNAME" \
    --account="$ACCOUNT" \
    --time="$TIME_LIMIT" \
    --array="$array_spec" \
    --export="ALL,JOB_TIME_SECONDS=$ROUND_SECONDS,OUTPUTDIR=$OUTPUTDIR,PROJECTDIR=$WORKDIR" \
    --output="$OUTPUTDIR/slurm_%A_%a.out" \
    "$ARRAY_SCRIPT" "$idxmap_tmp") || {
        echo "sbatch submission failed." >&2
        rm -f "$idxmap_tmp"
        exit 1
    }
 
jobid="${submit_out%%;*}"
cp "$idxmap_tmp" "$IDXMAP_DIR/${jobid}.txt"
 
echo "Submitted array job $jobid with $take task(s)."
echo "$(( n_candidates - take )) more were eligible but didn't fit this round --"
echo "re-run this script to submit them once queue space frees up."
