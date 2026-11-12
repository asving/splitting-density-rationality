import SurfaceBlowup
import Tests

/-! Axiom audit of the public theorems added on 2026-11-12 (`SurfaceBlowup/Corollaries/AdicCompact.lean`
and `Tests/Ramified.lean`), and read-back of the headline statements. Run with
`lake env lean Checks/AxiomsAdic.lean`. -/

#print axioms SurfaceBlowup.isTopologicalRing_of_isAdic
#print axioms SurfaceBlowup.finite_quotient_maximalIdeal_pow
#print axioms SurfaceBlowup.t2Space_of_isAdic
#print axioms SurfaceBlowup.compactSpace_of_isAdic
#print axioms SurfaceBlowup.secondCountableTopology_of_isAdic
#print axioms SurfaceBlowup.main_dvr_of_isAdic
#print axioms SurfaceBlowup.main_dvr_adic
#print axioms SurfaceBlowup.main_field_form_ramified_adic
#print axioms SurfaceBlowup.Tests.not_isSquare_p
#print axioms SurfaceBlowup.Tests.irreducible_sqrtPoly
#print axioms SurfaceBlowup.Tests.isIntegral_root
#print axioms SurfaceBlowup.Tests.not_padicUnramified
#print axioms SurfaceBlowup.Tests.main_field_form_sqrtP

#check @SurfaceBlowup.main_dvr_adic
#check @SurfaceBlowup.main_field_form_ramified_adic
#check @SurfaceBlowup.Tests.not_padicUnramified
