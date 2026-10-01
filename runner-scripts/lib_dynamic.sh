#!/bin/bash
# lib_dynamic.sh: shared helpers for the template_dynamic SLURM workflow. Sourced by submit_batch_dynamic.sh and run_array_task_dynamic.sh. Not meant to be run directly.

LOG_GLOB="dynamic_*.log"
SPLIT_THRESHOLD_SECONDS=$((5 * 24 * 3600))   # 5 days

# Strings printed by template_dynamic.cpp
SUMMARY_MARKER="===== A/refinement enumeration ====="
INTERRUPT_MARKER="RUN INTERRUPTED"
STOPREQ_MARKER="[cubing] Stop requested"
CUBES_DONE_MARKER="[cubing] Cube-solving wall time:"

# log_header_field <logfile> <field>   e.g. log_header_field f section_end  -> "5000"
log_header_field() {
    grep -m1 '^=== runner:' "$1" 2>/dev/null | grep -oP "(^|\s)$2=\K[^\s]+" | head -1
}

# log_section_end <logfile>   section_end from the runner header (0 = unsectioned)
log_section_end() {
    local v; v=$(log_header_field "$1" section_end)
    echo "${v:-0}"
}

# log_is_complete <logfile>
# True iff the binary reached its end-of-run summary, was not interrupted, and (for cubed runs) actually finished the cube loop.
# "No cubes generated" (march_cu failure / UNSAT during cubing) prints the summary but never "Cube-solving wall time", so it is NOT complete.
log_is_complete() {
    local f="$1"
    grep -qF "$SUMMARY_MARKER" "$f" 2>/dev/null || return 1
    grep -qF "$INTERRUPT_MARKER" "$f" 2>/dev/null && return 1
    grep -qF "$STOPREQ_MARKER" "$f" 2>/dev/null && return 1
    grep -qF "$CUBES_DONE_MARKER" "$f" 2>/dev/null || return 1
    return 0
}

# log_last_r <logfile>  -> last signed "[r-tuning] r_parameter: N" (negative = tuning settled)
log_last_r() {
    grep -oP '\[r-tuning\] r_parameter:\s*\K-?[0-9]+' "$1" 2>/dev/null | tail -1
}

# log_tuning_done <logfile>  (true iff tuning settled: last r_parameter line is negative AND "[r-tuning] DONE" printed)
log_tuning_done() {
    local r; r=$(log_last_r "$1")
    [[ "$r" == -* ]] || return 1
    grep -qF "[r-tuning] DONE" "$1"
}

# get_tuning_estimate <logfile>
# Succeeds only for a log whose r-tuning settled. Echoes "ESTIMATE_SECONDS TOTAL_CUBES |r|".
# The estimate line is taken for the FINAL r, so if tuning reverted to an earlier r we still read that r's cube count.
get_tuning_estimate() {
    local log="$1" r_signed r_abs line est cubes est_int
    log_tuning_done "$log" || return 1
    r_signed=$(log_last_r "$log")
    r_abs="${r_signed#-}"

    line=$(grep -F "[r-tuning] Estimated total solve time at r=${r_abs}:" "$log" | tail -1)
    [[ -n "$line" ]] || return 1

    est=$(echo "$line" | grep -oP "r=${r_abs}:\s*\K[0-9.eE+-]+(?=s)")
    cubes=$(echo "$line" | grep -oP '\(\K[0-9]+(?= cubes)')
    [[ -n "$est" && -n "$cubes" ]] || return 1

    est_int=$(awk -v e="$est" 'BEGIN{printf "%d", e}')

    local dir tid fc mismatch=0
    dir="$(cd "$(dirname "$log")" && pwd)"; tid="${dir##*/template_}"
    [[ "$tid" =~ ^[0-9]+$ ]] || tid=0
    tid=$((10#$tid))
    fc=$(cubes_file_count "$dir" "$tid")
    if (( fc > 0 && fc != cubes )); then cubes=$fc; mismatch=1; fi

    echo "$est_int $cubes $r_abs $mismatch"
}

# find_tuning_log <template_dir>  -> path of the first log whose tuning settled
find_tuning_log() {
    local dir="$1" f
    shopt -s nullglob
    for f in "$dir"/$LOG_GLOB; do
        if get_tuning_estimate "$f" >/dev/null; then
            echo "$f"; shopt -u nullglob; return 0
        fi
    done
    shopt -u nullglob
    return 1
}

# cubes_file_count <template_dir> <template_id>  -> number of cubes in the on-disk cubes file (0 if missing)
cubes_file_count() {
    local f="$1/cubes_$2.icnf"
    [[ -f "$f" ]] || { echo 0; return; }
    grep -c '^a ' "$f"
}

# log_effective_r <logfile>  -> signed r this attempt ended with: last tuning line if any, else the r the runner passed (resumed/section runs
# use a negative r and print no tuning lines).
log_effective_r() {
    local r; r=$(log_last_r "$1")
    [[ -n "$r" ]] || r=$(log_header_field "$1" r)
    echo "$r"
}

# log_cubes_trustworthy <logfile>: cube indices printed in this log refer to the final cubes file (tuning settled, or a reuse-mode run).
log_cubes_trustworthy() {
    local hr; hr=$(log_header_field "$1" r)
    [[ "$hr" == -* ]] && return 0
    log_tuning_done "$1"
}

# latest_incomplete_log <template_dir> <section_end>  -> newest not-completed log belonging to that section
latest_incomplete_log() {
    local dir="$1" end="${2:-0}" f
    while read -r f; do
        [[ -n "$f" ]] || continue
        log_is_complete "$f" && continue
        [[ "$(log_section_end "$f")" == "$end" ]] || continue
        echo "$f"; return 0
    done < <(ls -1t "$dir"/$LOG_GLOB 2>/dev/null)
    return 1
}

# next_cube_to_run <template_dir> <section_end> <default_start>
# Highest "first cube still to do" over all incomplete, trustworthy logs of the section.
#   graceful stop (the binary finishes the cube in flight, then prints "Stop requested"): last logged cube is DONE -> resume at last+1
#   hard kill / SLURM timeout / crash: the cube line is printed after a cube finishes, but its records may still sit in an unflushed buffer ->
#   repeat the last logged cube (resume at last)
next_cube_to_run() {
    local dir="$1" end="${2:-0}" next="$3" f last hdr cand
    shopt -s nullglob
    for f in "$dir"/$LOG_GLOB; do
        log_is_complete "$f" && continue
        [[ "$(log_section_end "$f")" == "$end" ]] || continue
        log_cubes_trustworthy "$f" || continue
        hdr=$(log_header_field "$f" cube_start); hdr="${hdr:-$3}"
        last=$(grep -oP '^\[cubing\] Cube \K[0-9]+(?= \()' "$f" | sort -n | tail -1)
        if [[ -z "$last" ]]; then
            cand=$hdr
        elif grep -qF "$STOPREQ_MARKER" "$f"; then
            cand=$(( last + 1 ))
        else
            cand=$last
        fi
        (( cand > next )) && next=$cand
    done
    shopt -u nullglob
    echo "$next"
}

compute_sections() {   # <estimate_seconds> <total_cubes> -> "N CUBES_PER_SECTION"
    local est="$1" cubes="$2" n per
    if (( est <= SPLIT_THRESHOLD_SECONDS )); then echo "1 0"; return; fi
    n=$(( (est + SPLIT_THRESHOLD_SECONDS - 1) / SPLIT_THRESHOLD_SECONDS ))
    per=$(( (cubes + n - 1) / n ))
    echo "$n $per"
}

section_bounds() {     # <k> <per> <total> -> "START END" (END exclusive, clamped)
    local k="$1" per="$2" total="$3" start end
    start=$(( k * per )); end=$(( (k + 1) * per ))
    (( end > total )) && end=$total
    echo "$start $end"
}

# is_section_completed <template_dir> <end_cube>
# end=0: any completed UNSECTIONED log (runner header section_end=0). end>0: a completed log whose runner header section_end matches.
is_section_completed() {
    local dir="$1" end="${2:-0}" f
    shopt -s nullglob
    for f in "$dir"/$LOG_GLOB; do
        log_is_complete "$f" || continue
        [[ "$(log_section_end "$f")" == "$end" ]] || continue
        shopt -u nullglob; return 0
    done
    shopt -u nullglob
    return 1
}

# list_pending_sections <template_dir>  -> one "START END" line per unit of work still needed
list_pending_sections() {
    local dir="$1" tuning_log est cubes r_abs n per k s e
    tuning_log=$(find_tuning_log "$dir")
    if [[ -n "$tuning_log" ]] && read -r est cubes r_abs _ < <(get_tuning_estimate "$tuning_log"); then
        read -r n per < <(compute_sections "$est" "$cubes")
    else
        n=1
    fi
    if (( n <= 1 )); then
        is_section_completed "$dir" 0 && return
        echo "0 0"; return
    fi
    for (( k = 0; k < n; k++ )); do
        read -r s e < <(section_bounds "$k" "$per" "$cubes")
        is_section_completed "$dir" "$e" || echo "$s $e"
    done
}

# lookup_params <i> <ranges_conf>  -> "R HOURS" (last matching row wins)
lookup_params() {
    local i="$1" conf="$2" r=20 hours=2 start end rr hh
    while read -r start end rr hh _; do
        [[ -z "$start" || "$start" == \#* ]] && continue
        if (( i >= start && i <= end )); then r="$rr"; hours="$hh"; fi
    done < "$conf"
    echo "$r $hours"
}

# build_completed_set <outputdir> <assoc_array_name>  -> completed[i]=1 for every fully finished template
build_completed_set() {
    local outputdir="$1"
    local -n _out="$2"
    local dir idx tuning_log est cubes r_abs n per k s e all_done

    shopt -s nullglob
    for dir in "$outputdir"/template_*/; do
        idx="${dir%/}"; idx="${idx##*/template_}"
        idx="${idx##0}"; idx="${idx:-0}"
        [[ "$idx" =~ ^[0-9]+$ ]] || continue

        tuning_log=$(find_tuning_log "$dir")
        if [[ -n "$tuning_log" ]] && read -r est cubes r_abs _ < <(get_tuning_estimate "$tuning_log"); then
            read -r n per < <(compute_sections "$est" "$cubes")
        else
            n=1
        fi

        if (( n <= 1 )); then
            is_section_completed "$dir" 0 && _out[$idx]=1
        else
            all_done=1
            for (( k = 0; k < n; k++ )); do
                read -r s e < <(section_bounds "$k" "$per" "$cubes")
                is_section_completed "$dir" "$e" || { all_done=0; break; }
            done
            (( all_done )) && _out[$idx]=1
        fi
    done
    shopt -u nullglob
}

parse_hms_to_seconds() {
    local t="$1" d=0 h=0 m=0 s=0
    if [[ "$t" == *-* ]]; then d="${t%%-*}"; t="${t#*-}"; fi
    IFS=: read -r h m s <<< "$t"
    echo $(( ((d*24 + ${h:-0})*60 + ${m:-0})*60 + ${s:-0} ))
}
