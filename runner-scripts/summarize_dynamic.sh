#!/bin/bash
# summarize_dynamic.sh: summary table of the template_dynamic runs found in an output directory.
#
#   ./summarize_dynamic.sh [OUTPUTDIR] [--csv FILE] [--details] [--only-incomplete] [--refs-from auto|cubes|solutions|logs] [--verify] [--no-dedup]
#
# OUTPUTDIR defaults to $SCRATCH/sat_solver/runs_dynamic. Only template_NNNN folders actually present are summarized.
#
# Refineemnt flags after the number (never present for source "cubes" unless noted):
#     *  some cubes were solved in more than one run, so refinements may be counted twice      (solutions / logs source)
#     ~  a solutions file ends in a truncated record (hard kill): off by about one per such file (solutions source)
#     <  a run printed no summary: lower bound                                                (logs source)
#     ?  forced --refs-from cubes but some cubes have no count in the logs: lower bound
#     !  (--verify) cube-sum and solutions-file count disagree although no cube was repeated: refinements were counted but not all reached the
#        files (buffered output lost in a hard kill), or the folder holds solutions files from other runs.

set -uo pipefail
WORKDIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$WORKDIR/lib_dynamic.sh"

OUTPUTDIR=""; CSV=""; DETAILS=0; ONLY_INCOMPLETE=0; REFS_FROM="auto"; VERIFY=0; DEDUP=1
RUNNING_WINDOW_MIN="${RUNNING_WINDOW_MIN:-15}"   # an unfinished template whose newest log changed within this many minutes shows as Running
while (( $# )); do
    case "$1" in
        --csv) CSV="$2"; shift 2 ;;
        --details) DETAILS=1; shift ;;
        --only-incomplete) ONLY_INCOMPLETE=1; shift ;;
        --refs-from) REFS_FROM="$2"; shift 2 ;;
        --verify) VERIFY=1; shift ;;
        --no-dedup) DEDUP=0; shift ;;
        -h|--help) sed -n '2,34p' "$0"; exit 0 ;;
        *) OUTPUTDIR="$1"; shift ;;
    esac
done
OUTPUTDIR="${OUTPUTDIR:-${SCRATCH:?SCRATCH is not set; pass the output directory}/sat_solver/runs_dynamic}"
[[ "$REFS_FROM" =~ ^(auto|cubes|solutions|logs)$ ]] || { echo "--refs-from must be auto, cubes, solutions or logs" >&2; exit 1; }
[[ -d "$OUTPUTDIR" ]] || { echo "Not a directory: $OUTPUTDIR" >&2; exit 1; }

human() { numfmt --to=iec --suffix=B "${1:-0}" 2>/dev/null || echo "${1:-0}B"; }
# bytes of all files in a dir matching a glob (0 if none)
bytes_of() { local d="$1" pat="$2" t=0 f; shopt -s nullglob; for f in "$d"/$pat; do t=$(( t + $(stat -c %s "$f") )); done; shopt -u nullglob; echo "$t"; }

# Parse one log -> "cube<TAB>idx<TAB>squares<TAB>seconds" lines, plus "wall<TAB>seconds" / "refs<TAB>n" if the summary was printed.
parse_log() {
    awk '
    /^\[cubing\] Cube [0-9]+ \(/ {
        idx=$3; sq=$0; sub(/^.*lits\): /,"",sq); sub(/ complete A squares.*/,"",sq)
        s=$0; sub(/^.*took /,"",s); split(s,a,"/"); solve=a[1]+0
        c=$0; sub(/^.*solve \(/,"",c); split(c,b,"/"); create=b[1]+0
        rf="-"; if (match($0, /, [0-9]+ refinements$/)) { rf=substr($0, RSTART+2, RLENGTH-2); sub(/ refinements$/, "", rf) }
        printf "cube\t%s\t%s\t%.3f\t%s\n", idx, sq, solve+create, rf }
    /^Total wall time \(incl\. setup\):/ { w=$0; sub(/^.*: /,"",w); sub(/s$/,"",w); printf "wall\t%s\n", w }
    /^Refinements found:/ { printf "refs\t%s\n", $3 }
    ' "$1" 2>/dev/null
}

# aut_order <template_dir> -> |Aut(T)| (identity included), or "-" if unknown.
# 1) "Template Aut(T) order (verified): N" in any log (stdout, so a hard-killed run may not have flushed it);
# 2) fallback: header of a dynamic_clauses_*.bin file: magic "DYNC", then E as a little-endian uint32 at byte offset 8.
aut_order() {
    local dir="$1" v f m b0 b1 b2 b3
    v=$(grep -h -m1 -oP '^Template Aut\(T\) order \(verified\):\s*\K[0-9]+' "$dir"/$LOG_GLOB 2>/dev/null | head -1)
    if [[ -n "$v" ]]; then echo "$v"; return; fi
    for f in "$dir"/dynamic_clauses_*; do
        [[ -f "$f" ]] || continue
        m=$(head -c 4 "$f" 2>/dev/null)
        [[ "$m" == "DYNC" ]] || continue
        read -r b0 b1 b2 b3 < <(od -An -tu1 -j8 -N4 "$f" 2>/dev/null)
        [[ -n "${b3:-}" ]] || continue
        echo $(( b0 + (b1 << 8) + (b2 << 16) + (b3 << 24) )); return
    done
    echo "-"
}

# solutions_refs <template_dir> -> "REFINEMENTS TRUNCATED_FLAG" over all solutions_*.bin (see header comment for the record layout).
solutions_refs() {
    local dir="$1" f size nA body R=0 trunc=0
    for f in "$dir"/solutions_*.bin; do
        [[ -f "$f" ]] || continue
        size=$(stat -c %s "$f")
        nA=$(LC_ALL=C tr -cd '\377' < "$f" | wc -c)
        body=$(( size - 51 * nA ))
        if (( body < 0 )); then trunc=1; body=0; fi
        (( body % 50 )) && trunc=1
        R=$(( R + body / 50 ))
    done
    echo "$R $trunc"
}

# sorted_logs <template_dir> -> the template's logs, oldest run first. A run's age is the start time in its runner header (date=...), not
# the file mtime (mtime changes when folders are copied or moved); logs without a header fall back to mtime. Ties are broken by job id.
sorted_logs() {
    local dir="$1" f d
    for f in "$dir"/$LOG_GLOB; do
        d=$(log_header_field "$f" date)
        [[ -n "$d" ]] || d=$(date -r "$f" +%Y-%m-%dT%H:%M:%S)
        printf '%s\t%s\n' "$d" "$f"
    done | sort -t$'\t' -k1,1 -k2,2V | cut -f2-
}

# Deduplicating record counter (python3). Prints: "REFINEMENTS UNIQUE_A_SQUARES TOTAL_RECORDS TRUNCATED_RECORDS"
PYCOUNT=""
if (( DEDUP )) && command -v python3 >/dev/null 2>&1; then
    PYCOUNT=$(mktemp --suffix=.py)
    cat > "$PYCOUNT" <<'PYEOF2'
import sys, os, glob, mmap
seen = {}                 # hash(A block) -> refinements of that record
records = 0; truncated = 0
for path in sorted(glob.glob(os.path.join(sys.argv[1], "solutions_*.bin"))):
    size = os.path.getsize(path)
    if size == 0:
        continue
    with open(path, "rb") as f:
        mm = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
        try:
            pos = mm.find(b"\xff", 0)
            while pos != -1:
                nxt = mm.find(b"\xff", pos + 1)
                body = (size if nxt == -1 else nxt) - pos - 1
                if body < 50 or (body - 50) % 50:
                    truncated += 1                      # only the last record of a hard-killed file
                else:
                    k = (body - 50) // 50
                    key = hash(mm[pos + 1:pos + 51])    # 50-byte A block
                    records += 1
                    if seen.get(key, -1) < k:           # a repeat is identical; keep the larger if a copy was damaged
                        seen[key] = k
                pos = nxt
        finally:
            mm.close()
print(sum(seen.values()), len(seen), records, truncated)
PYEOF2
fi
if (( DEDUP )) && [[ -z "$PYCOUNT" ]]; then echo "NOTE: python3 not found; solutions are counted without deduplication (module load python?)" >&2; fi

tmp=$(mktemp); trap 'rm -f "$tmp" "$tmp.rows" "$tmp.run" "${PYCOUNT:-}"' EXIT
[[ -n "$CSV" ]] && echo "template,refinements,time_s,ref_per_s,status,runs,complete_runs,split_sections,sections_done,a_squares,log_bytes,solutions_bytes,proofs_bytes,dyn_clause_bytes,slurm_bytes,cnf_bytes,cubes_bytes,total_bytes,r,total_cubes,aut_order,dup_cubes,solutions_truncated,refinements_from_logs,refs_flags,refs_source,refinements_in_files,duplicate_records_removed" > "$CSV"

shopt -s nullglob
dirs=("$OUTPUTDIR"/template_*/)
(( ${#dirs[@]} )) || { echo "No template_* folders in $OUTPUTDIR" >&2; exit 1; }

n_total=0; n_done=0; n_marked=0; g_ref=0; g_sq=0; g_time=0; g_refs=0; g_bytes=0
declare -A n_src=()
declare -A G_TYPE=( [logs]=0 [solutions]=0 [proofs]=0 [clauses]=0 [slurm]=0 [cnf]=0 [cubes]=0 )

for dir in "${dirs[@]}"; do
    dir="${dir%/}"; name="${dir##*/}"; tid="${name#template_}"; [[ "$tid" =~ ^[0-9]+$ ]] || continue; id=$((10#$tid))
    logs=( "$dir"/$LOG_GLOB )
    runs=${#logs[@]}

    # ---- logs are read oldest run first, so for a cube solved in several logs the awk below keeps the line of the LATEST run
    #      (A squares: latest line; refinements: latest line that carries a "N refinements" count)
    sq=0; secs=0; refs=0; ncomplete=0; newest=0; nosummary=0
    : > "$tmp"
    while read -r f; do
        [[ -n "$f" ]] || continue
        log_is_complete "$f" && ncomplete=$((ncomplete+1))
        m=$(stat -c %Y "$f"); (( m > newest )) && newest=$m
        parse_log "$f" > "$tmp.run"
        wall=$(awk -F'\t' '$1=="wall"{w=$2} END{print w+0}' "$tmp.run")
        cubesecs=$(awk -F'\t' '$1=="cube"{s+=$4} END{print s+0}' "$tmp.run")
        if awk -v w="$wall" 'BEGIN{exit !(w>0)}'; then secs=$(awk -v a="$secs" -v b="$wall" 'BEGIN{print a+b}'); else secs=$(awk -v a="$secs" -v b="$cubesecs" 'BEGIN{print a+b}'); fi
        r=$(awk -F'\t' '$1=="refs"{x=$2} END{print x+0}' "$tmp.run"); refs=$((refs + r))
        grep -q '^cube' "$tmp.run" && ! grep -q '^refs' "$tmp.run" && nosummary=$((nosummary+1))
        grep '^cube' "$tmp.run" >> "$tmp"
    done < <(sorted_logs "$dir")
    rm -f "$tmp.run"
    sq=$(awk -F'\t' '{last[$2]=$3} END{for(i in last) s+=last[i]; print s+0}' "$tmp")
    read -r refs_cubes cubes_missing < <(awk -F'\t' '{ if ($5 != "-") r[$2]=$5; seen[$2]=1 } END{ s=0; m=0; for (i in seen) { if (i in r) s+=r[i]; else m++ } print s+0, m+0 }' "$tmp")
    dup_cubes=$(awk -F'\t' '{c[$2]++} END{d=0; for(i in c) if(c[i]>1) d++; print d+0}' "$tmp")
    ncubes_done=$(awk -F'\t' '{seen[$2]=1} END{n=0; for(i in seen) n++; print n}' "$tmp")

    # ---- tuning / splitting
    r_final=""; total_cubes=""; split=0; sec_done=0; sec_total=1
    tl=$(find_tuning_log "$dir")
    if [[ -n "$tl" ]]; then
        read -r est cubes r_abs mism < <(get_tuning_estimate "$tl"); r_final="$r_abs"; total_cubes="$cubes"
        read -r nsec per < <(compute_sections "$est" "$cubes")
        if (( nsec > 1 )); then
            split=1; sec_total=$nsec
            for (( k=0; k<nsec; k++ )); do read -r s e < <(section_bounds "$k" "$per" "$cubes"); is_section_completed "$dir" "$e" && sec_done=$((sec_done+1)); done
        fi
    fi

    # ---- status
    if (( split )); then (( sec_done == sec_total )) && done_flag=1 || done_flag=0
    else is_section_completed "$dir" 0 && done_flag=1 || done_flag=0; fi
    if (( done_flag )); then status="Completed"
    elif (( runs == 0 )); then status="No logs"
    elif (( $(date +%s) - newest < RUNNING_WINDOW_MIN * 60 )); then status="Running"
    elif [[ -n "$tl" ]]; then
        if (( split )); then status="Incomplete ($sec_done/$sec_total sections)"; else status="Incomplete (${ncubes_done}/${total_cubes:-?} cubes)"; fi
    else status="Incomplete (tuning)"; fi

    # ---- sizes
    b_log=$(bytes_of "$dir" "$LOG_GLOB"); b_sol=$(bytes_of "$dir" "solutions_*.bin"); b_prf=$(bytes_of "$dir" "proofs_*"); b_dyn=$(bytes_of "$dir" "dynamic_clauses_*")
    b_slr=$(bytes_of "$dir" "slurm_*.out"); b_cnf=$(bytes_of "$dir" "encoding_*.cnf"); b_cub=$(bytes_of "$dir" "cubes_*.icnf")
    b_all=$(( b_log + b_sol + b_prf + b_dyn + b_slr + b_cnf + b_cub ))
    aut=$(aut_order "$dir")

    refs_logs=$refs; refs_files="-"; src=""; trunc=0; mark=""; dup_recs="-"
    have_cubes=0; (( ncubes_done > 0 && cubes_missing == 0 )) && have_cubes=1
    case "$REFS_FROM" in
        auto)      (( have_cubes )) && src=cubes || src=solutions ;;
        *)         src="$REFS_FROM" ;;
    esac
    case "$src" in
        cubes)
            refs_final=$refs_cubes
            (( cubes_missing > 0 )) && mark+="?"
            if (( VERIFY && dup_cubes == 0 )); then
                read -r refs_files trunc < <(solutions_refs "$dir")
                (( refs_files != refs_final )) && mark+="!"
            fi ;;
        solutions)
            if [[ -n "$PYCOUNT" ]]; then
                read -r refs_final uniq_a tot_rec ntrunc < <(python3 "$PYCOUNT" "$dir")
                dup_recs=$(( tot_rec - uniq_a )); (( ntrunc > 0 )) && trunc=1
                refs_files=$refs_final
            else
                read -r refs_final trunc < <(solutions_refs "$dir"); refs_files=$refs_final
                (( dup_cubes > 0 )) && mark+="*"
            fi
            (( trunc )) && mark+="~" ;;
        logs)
            refs_final=$refs_logs
            (( dup_cubes > 0 )) && mark+="*"
            (( nosummary > 0 )) && mark+="<" ;;
    esac
    n_src[$src]=$(( ${n_src[$src]:-0} + 1 ))

    rate=$(awk -v s="$refs_final" -v t="$secs" 'BEGIN{ if (t>0) printf "%.1f", s/t; else printf "0.0" }')
    secs_i=$(awk -v t="$secs" 'BEGIN{printf "%.0f", t}')

    n_total=$((n_total+1)); (( done_flag )) && n_done=$((n_done+1))
    g_sq=$((g_sq+sq)); g_ref=$((g_ref+refs_final)); [[ -n "$mark" ]] && n_marked=$((n_marked+1)); g_time=$(awk -v a="$g_time" -v b="$secs" 'BEGIN{print a+b}'); g_refs=$((g_refs+refs)); g_bytes=$((g_bytes+b_all))
    G_TYPE[logs]=$((G_TYPE[logs]+b_log)); G_TYPE[solutions]=$((G_TYPE[solutions]+b_sol)); G_TYPE[proofs]=$((G_TYPE[proofs]+b_prf)); G_TYPE[clauses]=$((G_TYPE[clauses]+b_dyn))
    G_TYPE[slurm]=$((G_TYPE[slurm]+b_slr)); G_TYPE[cnf]=$((G_TYPE[cnf]+b_cnf)); G_TYPE[cubes]=$((G_TYPE[cubes]+b_cub))

    (( ONLY_INCOMPLETE && done_flag )) && continue
    printf '%d\t%d\t%s\t%s\t%s\t%d\t%d\t%d/%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%s\t%s\t%s\t%d\t%d\t%d\t%s\t%s\t%s\t%s\n' \
        "$id" "$refs_final" "$secs_i" "$rate" "$status" "$runs" "$ncomplete" "$sec_done" "$sec_total" "$sq" "$b_log" "$b_sol" "$b_prf" "$b_dyn" "$b_slr" "$b_cnf" "$b_cub" "$b_all" "${r_final:--}" "${total_cubes:--}" "$aut" "$dup_cubes" "$trunc" "$refs_logs" "${mark:--}" "$src" "$refs_files" "$dup_recs" >> "$tmp.rows"
    [[ -n "$CSV" ]] && echo "$id,$refs_final,$secs_i,$rate,\"$status\",$runs,$ncomplete,$split,$sec_done/$sec_total,$sq,$b_log,$b_sol,$b_prf,$b_dyn,$b_slr,$b_cnf,$b_cub,$b_all,${r_final:-},${total_cubes:-},${aut/#-/},$dup_cubes,$trunc,$refs_logs,\"${mark}\",$src,${refs_files/#-/},${dup_recs/#-/}" >> "$CSV"
done
touch "$tmp.rows"; sort -n "$tmp.rows" -o "$tmp.rows"

printf '%5s  %12s  %12s  %10s  %32s  %8s\n' "No." "Squares" "Time (s)" "Sq./sec" "Status" "|Aut(T)|"
awk -F'\t' '{m=($24=="-")?"":$24; printf "%5d  %12s  %12d  %10s  %32s  %8s\n", $1,$2 m,$3,$4,$5,$20}' "$tmp.rows"
g_rate=$(awk -v s="$g_ref" -v t="$g_time" 'BEGIN{ if (t>0) printf "%.1f", s/t; else printf "0.0" }')
printf '%5s  %12d  %12.0f  %10s  %32s  %8s\n' "Total" "$g_ref" "$g_time" "$g_rate" "$n_done/$n_total completed" ""

if (( DETAILS )); then
    echo; echo "Details (one row per template):  Runs = log files (complete in brackets), Split = sections done/total (1/1 = not split)"
    printf '%5s  %9s  %6s  %14s  %9s  %9s  %9s  %9s  %9s  %6s  %8s  %8s  %6s  %7s  %9s\n' "No." "Runs(ok)" "Split" "A squares" "Logs" "Solutions" "Proofs" "DynClause" "Total" "r" "Cubes" "|Aut(T)|" "DupCub" "DupRec" "Src"
    awk -F'\t' 'function h(b,  u,i){split("B K M G T",u," "); i=1; while(b>=1024&&i<5){b/=1024;i++} return sprintf("%.1f%s",b,u[i])}
        {split($8,sp,"/"); splitcol=(sp[2]>1)? $8 : "-"; printf "%5d  %9s  %6s  %14d  %9s  %9s  %9s  %9s  %9s  %6s  %8s  %8s  %5d  %7s  %9s\n", $1, $6"("$7")", splitcol, $9, h($10), h($11), h($12), h($13), h($17), $18, $19, $20, $21, $27, $25}' "$tmp.rows"
fi

echo
echo "Totals across $n_total template folder(s) in $OUTPUTDIR"
printf '  Refinements: %d   (source per template:' "$g_ref"; for k in cubes solutions logs; do (( ${n_src[$k]:-0} )) && printf ' %s=%d' "$k" "${n_src[$k]}"; done; echo ")"
awk -F'\t' '$27 ~ /^[0-9]+$/ {n+=$27; t++} END{ if (t>0) printf "  Duplicate solution records removed (solutions source, %d template(s)): %d\n", t, n }' "$tmp.rows"
printf '  Complete A squares (per-cube lines, deduplicated by cube index): %d\n' "$g_sq"
(( n_marked > 0 )) && echo "  Flags present: see the header of this script (* ~ < ? !)"
printf '  Compute time: %.0f s = %.1f core-hours = %.2f core-years\n' "$g_time" "$(awk -v t="$g_time" 'BEGIN{print t/3600}')" "$(awk -v t="$g_time" 'BEGIN{print t/31557600}')"
awk -F'\t' '$20 ~ /^[0-9]+$/ {a[++n]=$20+0} END{ if(n==0){print "  |Aut(T)|: not found in any log or dynamic_clauses header"; exit}
    for(i=1;i<=n;i++) for(j=i+1;j<=n;j++) if(a[j]<a[i]){t=a[i];a[i]=a[j];a[j]=t}
    s=0; for(i=1;i<=n;i++) s+=a[i]; printf "  |Aut(T)| over %d template(s): min %d, median %d, max %d, mean %.1f\n", n, a[1], a[int((n+1)/2)], a[n], s/n }' "$tmp.rows"
echo "  Disk used by file type:"
for k in logs solutions proofs clauses slurm cnf cubes; do printf '    %-10s %10s  (%d bytes)\n' "$k" "$(human "${G_TYPE[$k]}")" "${G_TYPE[$k]}"; done
printf '    %-10s %10s  (%d bytes)\n' "ALL" "$(human "$g_bytes")" "$g_bytes"
[[ -n "$CSV" ]] && echo "  CSV written to $CSV"
rm -f "$tmp.rows"