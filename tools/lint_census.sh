#!/bin/bash
# usage: tools/lint_census.sh OUTDIR  -> per-file Mathlib standard-linter logs in OUTDIR and a totals table
#   OUTDIR/census.tsv. Requires current .oleans (run after a green `lake build`). Sequential, taskset 0-15.
cd ~/prove2me_workspace/final/unified
O=${1:-logs/lint}; mkdir -p $O
for f in SurfaceBlowup.lean $(find SurfaceBlowup Tests -name '*.lean' | sort) Tests.lean; do
  taskset -c 0-15 lake env lean -Dweak.linter.mathlibStandardSet=true $f > $O/$(echo $f | tr / _).log 2>&1
done
grep -ho 'linter\.[A-Za-z.]*' $O/*.log | grep -v 'false`' | sort | uniq -c | sort -rn > $O/census_raw.txt
# count warnings per linter (each warning ends with a "Note: This linter can be disabled with" line)
grep -h 'can be disabled with `set_option' $O/*.log | sed 's/.*set_option \([^ ]*\) false.*/\1/' \
  | sort | uniq -c | sort -rn > $O/census.tsv
echo "files with warnings: $(grep -l 'warning' $O/*.log | wc -l)"; cat $O/census.tsv
