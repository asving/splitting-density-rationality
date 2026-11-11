#!/bin/bash
# Portable variant of tools/release_check.sh, for a machine that has this repository but not the
# certified one-theorem-per-file trees. Run from the repository root:
#   tools/release_check_local.sh [REFERENCE_DUMP]
#   (1) `lake build SurfaceBlowup Tests`, (2) `#print axioms` (Checks/Axioms.lean: 22 main theorems;
#   Checks/AxiomsCorollaries.lean: the 25 public theorems added in v1.2.0), (3) statement dump
#   (tools/StmtDump.lean) compared with REFERENCE_DUMP (default Checks/reference/stmt_dump_v1_1_0.tsv,
#   the dump of tag v1.1.0): every constant of the reference must be present with the same type and
#   value hashes; new constants are counted, (4) grep for forbidden tokens, (5) zero build warnings.
# Step (3) replaces the statement-preservation check against the certified trees (Checks/run_checks.sh),
# which needs those trees. It shows that no statement or definition changed since the reference release;
# it does not re-derive the certified statements. Logs go to logs/. Exit code 0 iff everything passes.
ref=${1:-Checks/reference/stmt_dump_v1_1_0.tsv}
mkdir -p logs
fail=0; ok() { echo "PASS: $1"; }; bad() { echo "FAIL: $1"; fail=1; }
echo "== (1) lake build"
lake build SurfaceBlowup Tests > logs/release_build.log 2>&1
grep -q 'Build completed successfully' logs/release_build.log && ok "$(grep 'Build completed' logs/release_build.log)" \
  || bad "build (see logs/release_build.log)"
echo "== (2) axioms"
lake env lean Checks/Axioms.lean > logs/release_axioms.log 2>&1
n=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" logs/release_axioms.log)
t=$(grep -c "depends on axioms\|does not depend on any axioms" logs/release_axioms.log)
[ "$n" = 22 ] && [ "$t" = 22 ] && ok "22/22 main theorems use only [propext, Classical.choice, Quot.sound]" || bad "axioms ($n/22)"
lake env lean Checks/AxiomsCorollaries.lean > logs/release_axioms_corollaries.log 2>&1
n=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" logs/release_axioms_corollaries.log)
t=$(grep -c "depends on axioms\|does not depend on any axioms" logs/release_axioms_corollaries.log)
[ "$n" = 25 ] && [ "$t" = 25 ] && ok "25/25 public theorems added in v1.2.0 use only [propext, Classical.choice, Quot.sound]" || bad "axioms of the v1.2.0 theorems ($n/25)"
echo "== (3) statements unchanged since $(basename "$ref")"
STMT_DUMP=logs/release_stmt_dump.tsv lake env lean tools/StmtDump.lean > logs/release_stmt_dump.log 2>&1
r=$(wc -l < "$ref" | tr -d ' ')
same=$(comm -12 <(sort "$ref") <(sort logs/release_stmt_dump.tsv) | wc -l | tr -d ' ')
new=$(comm -13 <(cut -f2 "$ref" | sort) <(cut -f2 logs/release_stmt_dump.tsv | sort) | wc -l | tr -d ' ')
[ -s logs/release_stmt_dump.tsv ] && [ "$same" = "$r" ] \
  && ok "$same/$r constants of the reference have identical type and value hashes; $new new constants" \
  || bad "statement dump: $same/$r reference constants unchanged"
echo "== (4) forbidden tokens"
g=$(grep -rnE '\bsorry\b|\bnative_decide\b|^\s*(private )?axiom\b|maxHeartbeats|(^|[;(]\s*)admit\b' \
  SurfaceBlowup Tests SurfaceBlowup.lean Tests.lean)
[ -z "$g" ] && ok "no sorry/admit/native_decide/axiom/maxHeartbeats" || { bad "forbidden tokens:"; echo "$g"; }
echo "== (5) warnings"
w=$(grep -c '^warning:' logs/release_build.log)
[ "$w" = 0 ] && ok "0 build warnings" || { bad "build warnings: $w"; grep '^warning:' logs/release_build.log | cut -c1-110; }
echo "== lines: $(cat $(find SurfaceBlowup -name '*.lean') SurfaceBlowup.lean | wc -l | tr -d ' ') (SurfaceBlowup), $(cat $(find Tests -name '*.lean') Tests.lean | wc -l | tr -d ' ') (Tests); modules: $(find SurfaceBlowup -name '*.lean' | wc -l | tr -d ' ')"
[ $fail = 0 ] && echo "RELEASE CHECK (local): ALL PASS" || echo "RELEASE CHECK (local): FAILURES"
exit $fail
