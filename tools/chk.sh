#!/bin/bash
# usage: tools/chk.sh ENVDIR FILE [MODULE]
#   Check FILE with Lean against the frozen olean directory ENVDIR (prepended to LEAN_PATH, so its
#   SurfaceBlowup/*.olean shadow .lake/build). If MODULE (e.g. SurfaceBlowup.Reciprocity.Defs) is given,
#   also write ENVDIR/<module path>.olean/.ilean so that later files in the same private env see it.
#   Never writes to .lake/. Example: tools/chk.sh scratch/envR SurfaceBlowup/Reciprocity/Defs.lean SurfaceBlowup.Reciprocity.Defs
#   Optional env LEANOPTS (e.g. LEANOPTS=-Dweak.linter.mathlibStandardSet=true) is passed to lean.
U=~/prove2me_workspace/final/unified
cd $U
E=$(realpath "$1"); F=$(realpath "$2"); M=$3
OPT=""
if [ -n "$M" ]; then
  P=$E/$(echo $M | tr . /)
  mkdir -p $(dirname $P)
  OPT="-R $U -o $P.olean -i $P.ilean"
fi
lake env bash -c "LEAN_PATH=$E:\$LEAN_PATH taskset -c 0-15 lean $LEANOPTS $OPT $F"
