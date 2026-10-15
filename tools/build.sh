#!/bin/bash
# usage: tools/build.sh N  -> logs/buildN.log, prints failures and first errors
cd ~/prove2me_workspace/final/unified
L=logs/build$1.log
( time timeout 5400 taskset -c 0-15 lake build 2>&1 ) > $L 2>&1
echo "built: $(grep -E '^(✔|⚠)' $L | grep -c SurfaceBlowup)  failed: $(grep -E '^✖' $L | grep -c SurfaceBlowup)"
grep -E '^✖' $L | sed 's/(.*//'
grep -E '^error: SurfaceBlowup' $L | cut -c1-220 | head -${2:-15}
grep -E 'Build completed|^real' $L
