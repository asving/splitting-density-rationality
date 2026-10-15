#!/bin/bash
# One-command release check for the unified SurfaceBlowup tree:
#   (1) full `lake build` (SurfaceBlowup + Tests), (2) `#print axioms` of the four main theorems,
#   (3) statement preservation vs the certified trees (Checks/run_checks.sh), (4) grep for forbidden tokens,
#   (5) zero build warnings. Logs go to logs/release_*.log. Exit code 0 iff everything passes.
# Shared machine: runs on cores 0-15 only; one build at a time.
cd ~/prove2me_workspace/final/unified
fail=0; ok() { echo "PASS: $1"; }; bad() { echo "FAIL: $1"; fail=1; }
echo "== (1) lake build"
( time taskset -c 0-15 lake build 2>&1 ) > logs/release_build.log 2>&1
grep -q 'Build completed successfully' logs/release_build.log && ok "$(grep 'Build completed' logs/release_build.log)" \
  || bad "build (see logs/release_build.log)"
echo "== (2) axioms"
taskset -c 0-15 lake env lean Checks/Axioms.lean > logs/release_axioms.log 2>&1
n=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" logs/release_axioms.log)
[ "$n" = 4 ] && ok "4/4 main theorems use only [propext, Classical.choice, Quot.sound]" || bad "axioms ($n/4)"
echo "== (3) statement preservation"
./Checks/run_checks.sh > logs/release_preservation.log 2>&1
k=$(grep -c '^KERNEL_OK' logs/release_preservation.log)
c=$(grep -c '^CONCLUSION_IDENTICAL' logs/release_preservation.log)
[ "$k" = 3 ] && [ "$c" = 3 ] && ok "3/3 KERNEL_OK + CONCLUSION_IDENTICAL, implication form (main_dvr, recip_main, main_field_form)" || bad "preservation ($k/3)"
echo "== (4) forbidden tokens"
g=$(grep -rnE '\bsorry\b|\bnative_decide\b|^\s*(private )?axiom\b|maxHeartbeats|(^|[;(]\s*)admit\b' \
  SurfaceBlowup Tests SurfaceBlowup.lean Tests.lean)
[ -z "$g" ] && ok "no sorry/admit/native_decide/axiom/maxHeartbeats" || { bad "forbidden tokens:"; echo "$g"; }
echo "== (5) warnings"
w=$(grep -c '^warning:' logs/release_build.log)
[ "$w" = 0 ] && ok "0 build warnings" || { bad "build warnings: $w"; grep '^warning:' logs/release_build.log | cut -c1-110; }
echo "== lines: $(cat $(find SurfaceBlowup -name '*.lean') SurfaceBlowup.lean | wc -l) (SurfaceBlowup), $(cat $(find Tests -name '*.lean') Tests.lean | wc -l) (Tests); modules: $(find SurfaceBlowup -name '*.lean' | wc -l)"
[ $fail = 0 ] && echo "RELEASE CHECK: ALL PASS" || echo "RELEASE CHECK: FAILURES"
exit $fail
