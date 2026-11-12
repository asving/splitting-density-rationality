#!/bin/bash
# HISTORICAL (2026-11-12): this check cannot be run any more. It needs the original workspace and the
# certified one-theorem-per-file trees (monolith_gen, monolith_recip, monolith) below it. They no
# longer exist. Its last successful run is recorded for v1.0.0: 3x KERNEL_OK (CHANGELOG.md, cycle 4d).
# Since then statements are compared from release to release by tools/release_check_local.sh.
#
# Statement preservation: run from anywhere. Requires `lake build` of unified to be green.
set -e
U=~/prove2me_workspace/final/unified
F=~/prove2me_workspace/final
mk() { # name certImport certThm newThm tree
  sed -e "s|@CERT_IMPORT@|$2|; s|@CERT_THM@|$3|g; s|@NEW_THM@|$4|g; s|@CERT_TREE@|$5|g" $U/Checks/template.lean > $U/Checks/$1.lean
}
mk SPMainDvr Theorems.Thm_Gen_MainDvr SurfaceBlowupV2Gen.main_dvr SurfaceBlowup.main_dvr monolith_gen
mk SPRecip Theorems.Thm_SurfaceBlowupV2_recip_main SurfaceBlowupV2.recip_main SurfaceBlowup.recip_main monolith_recip
mk SPFieldForm Theorems.Thm_SurfaceBlowupV2_main_field_form SurfaceBlowupV2.main_field_form SurfaceBlowup.main_field_form monolith
cd $U
run() { # file certTree
  echo "== $1 vs $2"
  lake env bash -c "LEAN_PATH=\$LEAN_PATH:$F/$2/.lake/build/lib/lean taskset -c 0-15 lean $U/Checks/$1.lean"
}
run SPMainDvr monolith_gen
run SPRecip monolith_recip
run SPFieldForm monolith
