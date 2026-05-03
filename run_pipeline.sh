#  SAT1 (all_net_encoding) -> SAT2 (refinement_from_partial_list)
#  pipeline runner
#
#  Usage:  ./run_pipeline.sh <template_id>
#
#  All other parameters are controlled by the variables below.

set -euo pipefail

SCRIPT_START=$(date +%s)

SYM_TRANSVERSALS=10        # symbol transversals to observe (1-10)
OBSERVE_A=1                # partial on A (1=yes, 0=no)
OBSERVE_B=0                # partial on B (1=yes, 0=no)
COMMON_TRANSVERSALS=0      # common disjoint transversals (0-10)

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SAT1_SCRIPT="$SCRIPT_DIR/all_net_encoding.py"
SAT2_BIN="$SCRIPT_DIR/refinement_from_partial_list"

SAT1_TIMING_TAIL=5 # SAT1 output lines to re-echo as a timing summary (tail -N)

# ---- Argument check ----------------------------------------
if [[ $# -lt 1 ]]; then
    echo "Usage: $0 <template_id>"
    exit 1
fi

TEMPLATE_ID="$1"

# Solution file is placed alongside the SAT1 script so both programs resolve it the same way.
SOLUTION_FILE="${TEMPLATE_ID}-${SYM_TRANSVERSALS}-${OBSERVE_A}-${OBSERVE_B}-${COMMON_TRANSVERSALS}-solutions.txt"
SOLUTION_PATH="$SCRIPT_DIR/$SOLUTION_FILE" # could we smart to change this to home path so WSL read/write overhead is avoided

SAT1_LOG="$(mktemp)" # Temporary file to capture SAT1 stdout for timing extraction
trap 'rm -f "$SAT1_LOG"' EXIT

# ============================================================
echo "============================================================"
echo " Pipeline: template=${TEMPLATE_ID}  symT=${SYM_TRANSVERSALS} observe_A=${OBSERVE_A}  observe_B=${OBSERVE_B} common_T=${COMMON_TRANSVERSALS}"
echo " Solution file: $SOLUTION_FILE"
echo "============================================================"
echo

# ---- SAT 1 -------------------------------------------------
echo ">>> [SAT 1] Running all_net_encoding.py ..."
echo "------------------------------------------------------------"
SAT1_START=$(date +%s%N)

# we use a tee so you see live output AND we capture it for the summary
python3 "$SAT1_SCRIPT" "$SOLUTION_FILE" "$TEMPLATE_ID" "$SYM_TRANSVERSALS" "$OBSERVE_A" "$OBSERVE_B" "$COMMON_TRANSVERSALS" 2>&1 | tee "$SAT1_LOG"

SAT1_EXIT="${PIPESTATUS[0]}"
SAT1_END=$(date +%s%N)
SAT1_WALL=$(echo "scale=3; ($SAT1_END - $SAT1_START) / 1000000000" | bc)

echo "------------------------------------------------------------"
echo ">>> [SAT 1] Finished  (wall time: ${SAT1_WALL}s)"
echo

if [[ "$SAT1_EXIT" -ne 0 ]]; then
    echo "ERROR: SAT 1 exited with code $SAT1_EXIT, aborting pipeline."
    exit "$SAT1_EXIT"
fi

# --- Clean duplicate lines ---
DEDUP_START=$(date +%s%N)
echo ">>> Deduplicating solution file ..."
if [[ -s "$SOLUTION_PATH" ]]; then
    sort -u "$SOLUTION_PATH" -o "$SOLUTION_PATH"
else
    echo "WARNING: Solution file empty, nothing to deduplicate."
fi

DEDUP_END=$(date +%s%N)
DEDUP_WALL=$(echo "scale=3; ($DEDUP_END - $DEDUP_START) / 1000000000" | bc)

echo "------------------------------------------------------------"
echo ">>> Dedup finished  (wall time: ${DEDUP_WALL}s)"
echo

if [[ ! -s "$SOLUTION_PATH" ]]; then
    echo "WARNING: Solution file is empty or missing, SAT 2 may find nothing."
fi


# ---- SAT 2 -------------------------------------------------
echo ">>> [SAT 2] Running refinement_from_partial_list ..."
echo "------------------------------------------------------------"
SAT2_START=$(date +%s%N)

"$SAT2_BIN" "$TEMPLATE_ID" "$SOLUTION_PATH"

SAT2_EXIT=$?
SAT2_END=$(date +%s%N)
SAT2_WALL=$(echo "scale=3; ($SAT2_END - $SAT2_START) / 1000000000" | bc)

echo "------------------------------------------------------------"
echo ">>> [SAT 2] Finished  (wall time: ${SAT2_WALL}s)"
echo

if [[ "$SAT2_EXIT" -ne 0 ]]; then
    echo "ERROR: SAT 2 exited with code $SAT2_EXIT."
    exit "$SAT2_EXIT"
fi

# Re-echo the timing lines from SAT1 for easy comparison
echo "--- SAT 1 timing summary (last ${SAT1_TIMING_TAIL} lines) ---"
tail -n "$SAT1_TIMING_TAIL" "$SAT1_LOG"
echo "------------------------------------------------------------"
echo

# ---- Total -------------------------------------------------
TOTAL_WALL=$(echo "scale=3; $SAT1_WALL + $DEDUP_WALL + $SAT2_WALL" | bc)

echo "============================================================"
echo " TOTAL PIPELINE TIMING"
echo "   SAT 1 wall time : ${SAT1_WALL}s"
echo "   Dedup wall time : ${DEDUP_WALL}s"
echo "   SAT 2 wall time : ${SAT2_WALL}s"
echo "   Total wall time : ${TOTAL_WALL}s"
echo "============================================================"

SCRIPT_END=$(date +%s)
echo "=== Total script runtime: $((SCRIPT_END - SCRIPT_START)) seconds ==="