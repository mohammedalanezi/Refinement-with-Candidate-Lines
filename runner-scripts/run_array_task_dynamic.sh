#!/bin/bash
#SBATCH --job-name=tpls_refine
#SBATCH --cpus-per-task=1
#SBATCH --mem-per-cpu=1G
#
# --account, --time, --array, --output and --export are supplied on the sbatch command line by submit_batch_dynamic.sh and override the
# placeholders below. They're only here so this script is also sbatch-able by itself while testing on a single index.
#SBATCH --account=__SET_ME__
#SBATCH --time=00:10:00
#SBATCH --array=1-1
#
# Expects ONE argument: the idxmap file; line N holds "i start_cube end_cube" for array task N (written by submit_batch_dynamic.sh).

set -uo pipefail

# ---------------------------------------------------------------------
# EDIT THESE for your layout on the clusters
# ---------------------------------------------------------------------
WORKDIR="${PROJECTDIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}"

BINDIR="$HOME/projects/def-stevens/mo13/Refinement-with-Candidate-Lines"
BINARY="${BINARY:-./template_dynamic}"     # compiled with ISCLUSTER=1, lives in BINDIR

RANGES_CONF="$WORKDIR/ranges.conf"

# Optional overrides, passed to the binary only when set (otherwise its compiled-in ISCLUSTER=1 defaults are used).
BIN_FILE="${BIN_FILE:-}"       # --bin   (templates.bin)
MARCH_CU="${MARCH_CU:-}"       # --march-cu

OUTPUTDIR="${OUTPUTDIR:-${SCRATCH:?SCRATCH is not set -- are you on the cluster?}/sat_solver/runs_dynamic}"

# Time left under the SLURM limit for the graceful stop. SIGTERM is sent at (limit - MARGIN); the binary then finishes its current cube.
# SIGKILL follows KILL_GRACE seconds later. MARGIN must be > KILL_GRACE. Raise both if your cubes can run longer than ~5 minutes.
MARGIN="${MARGIN:-600}"
KILL_GRACE="${KILL_GRACE:-420}"
# ---------------------------------------------------------------------

source "$WORKDIR/lib_dynamic.sh"

module load gcc/13.3

IDXMAP="${1:?usage: sbatch run_array_task_dynamic.sh <idxmap_file>}"

read -r i start_cube_arg end_cube_arg < <(sed -n "${SLURM_ARRAY_TASK_ID}p" "$IDXMAP")
if [[ -z "${i:-}" ]]; then
    echo "Array task $SLURM_ARRAY_TASK_ID has no entry in $IDXMAP -- nothing to do."
    exit 0
fi
start_cube_arg="${start_cube_arg:-0}"
end_cube_arg="${end_cube_arg:-0}"
is_sectioned=0
(( end_cube_arg > 0 )) && is_sectioned=1

TEMPLATE_DIR="$OUTPUTDIR/template_$(printf '%04d' "$i")"
mkdir -p "$TEMPLATE_DIR"

jobid="${SLURM_ARRAY_JOB_ID:-manual}_${SLURM_ARRAY_TASK_ID:-0}"
logfile="$TEMPLATE_DIR/dynamic_${jobid}.log"

if is_section_completed "$TEMPLATE_DIR" "$end_cube_arg"; then
    echo "i=$i section [start=$start_cube_arg,end=$end_cube_arg) already has a completed log -- skipping."
    exit 0
fi

read -r r hours < <(lookup_params "$i" "$RANGES_CONF")

budget=$(( ${JOB_TIME_SECONDS:-$((hours * 3600))} - MARGIN ))
(( budget < 60 )) && budget=60

[[ -x "$BINDIR/${BINARY#./}" ]] || { echo "Binary $BINDIR/${BINARY#./} not found or not executable" >&2; exit 1; }
cd "$BINDIR" || { echo "Cannot cd to $BINDIR" >&2; exit 1; }

# ---------------------------------------------------------------------
# Decide r_arg (signed) and start_cube.
#   r_arg > 0 : binary generates cubes with march_cu and tunes r starting from there
#   r_arg < 0 : binary reuses the existing cubes file (no march_cu, no tuning)
# ---------------------------------------------------------------------
r_arg="$r"
start_cube="$start_cube_arg"

prev_log=$(latest_incomplete_log "$TEMPLATE_DIR" "$end_cube_arg")
tuning_log=$(find_tuning_log "$TEMPLATE_DIR")

if [[ -n "$prev_log" ]]; then
    prev_r=$(log_effective_r "$prev_log")
    if [[ "$prev_r" == -* ]]; then
        r_arg="$prev_r"
        start_cube=$(next_cube_to_run "$TEMPLATE_DIR" "$end_cube_arg" "$start_cube_arg")
        echo "=== i=$i: resuming from $prev_log: reusing cubes (r=$r_arg), starting at cube $start_cube ==="
    elif [[ -n "$prev_r" ]]; then
        # Tuning had not settled, so no cube index from that attempt can be trusted: retune, continuing from the r it had reached.
        r_arg="$prev_r"
        echo "=== i=$i: previous attempt died while tuning; retuning from r=$r_arg, cube $start_cube ==="
    else
        echo "=== i=$i: incomplete log has no r information -- fresh start with r=$r_arg ==="
    fi
elif (( is_sectioned )); then
    if [[ -z "$tuning_log" ]]; then
        # Without a settled tuning there is no cubes file to share. Letting each section retune would make them overwrite one another's
        # cubes_<i>.icnf (the filename does not include the job id), so refuse rather than risk inconsistent cube boundaries.
        echo "ERROR: i=$i requested section [start=$start_cube_arg,end=$end_cube_arg) but no settled tuning log exists in $TEMPLATE_DIR." >&2
        exit 1
    fi
    read -r _est _cubes tuned_r _mismatch < <(get_tuning_estimate "$tuning_log")
    r_arg="-${tuned_r}"
    echo "=== i=$i: section [start=$start_cube,end=$end_cube_arg): reusing cubes from tuned r=$tuned_r ($tuning_log) ==="
else
    echo "=== i=$i: no incomplete log -- fresh start with r=$r_arg ==="
fi

# Sanity checks whenever cubes are being reused.
if [[ "$r_arg" == -* ]]; then
    fc=$(cubes_file_count "$TEMPLATE_DIR" "$i")
    if (( fc == 0 )); then
        echo "ERROR: i=$i: r=$r_arg asks to reuse cubes but $TEMPLATE_DIR/cubes_${i}.icnf is missing or empty." >&2
        exit 1
    fi
    if [[ -n "$tuning_log" ]]; then
        read -r _est logged_cubes _r mismatch < <(get_tuning_estimate "$tuning_log")
        if (( mismatch )) && (( ! is_sectioned )) && (( start_cube > 0 )); then
            # Tuning reverted to an earlier r, so the file on disk is NOT the partition the earlier attempt's cube indices refer to.
            echo "WARNING: i=$i: cubes file has $fc cubes but the tuning log's final r produced a different count; cube indices from the earlier attempt are meaningless. Restarting from cube 0 on the cubes file as it is now (earlier solutions files for this template are redundant)." >&2
            start_cube=0
        fi
    fi
    if (( end_cube_arg > fc )); then
        echo "ERROR: i=$i: section end $end_cube_arg exceeds the $fc cubes in the cubes file." >&2
        exit 1
    fi
fi

# ---------------------------------------------------------------------
# Run. Runner header/footer go into the same log file the binary's stdout+stderr are appended to.
# ---------------------------------------------------------------------
echo "=== runner: template=$i jobid=$jobid section_start=$start_cube_arg section_end=$end_cube_arg r=$r_arg cube_start=$start_cube host=$(hostname) date=$(date +%Y-%m-%dT%H:%M:%S) ===" > "$logfile"

extra=()
[[ -n "$BIN_FILE" ]] && extra+=(--bin "$BIN_FILE")
[[ -n "$MARCH_CU" ]] && extra+=(--march-cu "$MARCH_CU")

# SCRATCH is overridden for the binary only: it builds its output dir as $SCRATCH/template_NNNN, so this puts everything in $OUTPUTDIR.
SCRATCH="$OUTPUTDIR" timeout --kill-after="${KILL_GRACE}s" "${budget}s" \
    "$BINARY" "$i" \
        --r "$r_arg" --cube-start "$start_cube" --cube-end "$end_cube_arg" --job-id "$jobid" \
        ${extra[@]+"${extra[@]}"} >> "$logfile" 2>&1
rc=$?

echo "=== runner: exit code $rc ===" >> "$logfile"

if log_is_complete "$logfile"; then
    echo "i=$i: section [start=$start_cube_arg,end=$end_cube_arg) completed. Output in $TEMPLATE_DIR"
else
    echo "i=$i: section [start=$start_cube_arg,end=$end_cube_arg) DID NOT complete (rc=$rc) -- will be retried next time submit_batch_dynamic.sh is run." >&2
    case "$rc" in
        124|143) echo "      (stopped by the time budget; binary exits 143 after finishing its current cube)" >&2 ;;
        137)     echo "      (SIGKILL: the cube in flight did not finish within KILL_GRACE=${KILL_GRACE}s; last solutions_*.bin may end in a partial record)" >&2 ;;
    esac
fi

# Move Slurm's own .out into the template directory now that this script is finishing.
slurm_out="$OUTPUTDIR/slurm_${SLURM_ARRAY_JOB_ID:-}_${SLURM_ARRAY_TASK_ID:-}.out"
if [[ -f "$slurm_out" ]]; then
    mv "$slurm_out" "$TEMPLATE_DIR/slurm_${jobid}.out"
fi
