#!/bin/bash
# run_splice_table.sh
#
# Runs the four RQ.Metaprogram.Tests.* files and captures, per splice:
#   - time to instantiate implicits (ms) and remaining implicits
#   - time to fill refinements (ms) and remaining implicits
#   - time to normalize the derivation (ms)
#   - time spent in core_check_term (ms)
#   - time to prove equality (ms)
#   - total splice elapsed time (ms)
#   - number of goal lines emitted in the prove_equality dump
#
# Produces .build/results/splice_table.tsv and .build/results/splice_table.md.

set -u
trap 'trap - EXIT INT TERM HUP; kill 0' EXIT INT TERM HUP
cd "$(dirname "$0")"

TESTS=(
  RQ.Metaprogram.Tests.Examples.fst
  RQ.Metaprogram.Tests.ExamplesIO.fst
  RQ.Metaprogram.Tests.ExamplesRefs.fst
  RQ.Metaprogram.Tests.ExamplesIORefinements.fst
)

OUT=.build/results
mkdir -p "$OUT"
TSV="$OUT/splice_table.tsv"
MD="$OUT/splice_table.md"
: > "$TSV"
printf 'file\tsplice\tinst_ms\tinst_left\tfill_ms\tfill_left\tnorm_ms\tcore_ms\tprove_ms\ttotal_ms\tgoal_lines\n' >> "$TSV"

run_one() {
  local f=$1
  local log="$OUT/${f}.log"
  : > "$log"

  rm -f ".build/cache/$f.checked"

  local cache="$(pwd)/.build/cache"
  local hints="$(pwd)/.build/hints"
  local odir="$(pwd)/.build/odir"
  mkdir -p "$cache" "$hints" "$odir"

  fstar.exe "$f" > "$log" 2>&1
  local rc=$?
  if [[ $rc -ne 0 ]]; then
    echo "  FAILED ($rc): $f" >&2
  fi
}

parse_one() {
  local f=$1
  local log="$OUT/${f}.log"

  awk -v file="$f" -v tsv="$TSV" '
    function num(s,    x) { x = s; sub(/ms$/, "", x); return x+0 }

    /TAC>> SPLICE_BEGIN / {
      # TAC>> SPLICE_BEGIN <nm>
      nm = $3
      cur = nm
      if (!(nm in seen)) { order[++n] = nm; seen[nm] = 1 }
      next
    }

    # TAC>>   done instantiating implicits, <K> left, <T>ms
    /done instantiating implicits,/ {
      if (cur == "") next
      # find the "<K>" and the trailing "<T>ms"
      for (i = 1; i <= NF; ++i) {
        if ($i == "left,") inst_left[cur] = $(i-1)+0
      }
      inst_ms[cur] = num($NF)
      next
    }

    # TAC>>   done filling refinements, <K> implicits left, <T>ms
    /done filling refinements,/ {
      if (cur == "") next
      for (i = 1; i <= NF; ++i) {
        if ($i == "implicits") fill_left[cur] = $(i-1)+0
      }
      fill_ms[cur] = num($NF)
      next
    }

    # TAC>>   done normalizing derivation <T>ms
    /done normalizing derivation/ {
      if (cur == "") next
      norm_ms[cur] = num($NF)
      next
    }

    # TAC>>   done core_check_term <T>ms
    /done core_check_term/ {
      if (cur == "") next
      core_ms[cur] = num($NF)
      next
    }

    # TAC>>   done proving equality <T>ms
    /done proving equality/ {
      if (cur == "") next
      prove_ms[cur] = num($NF)
      next
    }

    # proof-state: State dump @ depth 0 (PROVE_EQ_DUMP_BEGIN <nm>):
    /PROVE_EQ_DUMP_BEGIN / {
      if (match($0, /\(PROVE_EQ_DUMP_BEGIN [^)]+\)/)) {
        nm = substr($0, RSTART + length("(PROVE_EQ_DUMP_BEGIN "),
                       RLENGTH - length("(PROVE_EQ_DUMP_BEGIN ") - 1)
        collecting = nm; lines[nm] = 0
      }
      next
    }
    /TAC>> PROVE_EQ_DUMP_END / { collecting = ""; next }
    collecting != "" { lines[collecting]++ }

    # TAC>> SPLICE_END <nm> <T>ms
    /TAC>> SPLICE_END / {
      nm = $3
      total_ms[nm] = num($4)
      cur = ""
      next
    }

    END {
      for (i = 1; i <= n; ++i) {
        nm = order[i]
        printf "%s\t%s\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n", \
          file, nm, \
          inst_ms[nm]+0, inst_left[nm]+0, \
          fill_ms[nm]+0, fill_left[nm]+0, \
          norm_ms[nm]+0, core_ms[nm]+0, prove_ms[nm]+0, \
          total_ms[nm]+0, (nm in lines ? lines[nm] : 0) >> tsv
      }
    }
  ' "$log"
}

for f in "${TESTS[@]}"; do
  echo "=== $f ==="
  run_one "$f"
  parse_one "$f"
done

# Emit markdown table sorted by total elapsed-time descending.
{
  echo '| file | splice | inst (ms) | inst left | fill (ms) | fill left | norm (ms) | core (ms) | prove (ms) | total (ms) | goal lines |'
  echo '|------|--------|----------:|----------:|----------:|----------:|----------:|----------:|-----------:|-----------:|-----------:|'
  tail -n +2 "$TSV" | sort -t$'\t' -k10,10nr | \
    awk -F'\t' '{ printf "| %s | `%s` | %s | %s | %s | %s | %s | %s | %s | %s | %s |\n", \
                  $1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11 }'
} > "$MD"

echo "Wrote $TSV and $MD"
