import SurfaceBlowup
import Tests

/-! Axiom audit of every public theorem added in v1.2.0 (`SurfaceBlowup/Corollaries/*.lean` and
`Tests/PadicInt.lean`; the list is generated from the sources), and read-back of the elaborated
statements of the headline ones. Run with `lake env lean Checks/AxiomsCorollaries.lean`. -/

#print axioms SurfaceBlowup.divisorCount_eval_nonneg
#print axioms SurfaceBlowup.globalLaw_coeff_eval_nonneg
#print axioms SurfaceBlowup.monicExpr_eval_nonneg
#print axioms SurfaceBlowup.projectiveExpr_eval_nonneg
#print axioms SurfaceBlowup.clusterExpr_eval_nonneg
#print axioms SurfaceBlowup.main_dvr_toReal
#print axioms SurfaceBlowup.main_dvr_cluster_toReal
#print axioms SurfaceBlowup.Expr.rational_eval_of_safe
#print axioms SurfaceBlowup.clusterExpr_allSafe
#print axioms SurfaceBlowup.cluster_rational_eval
#print axioms SurfaceBlowup.universal_type_laws
#print axioms SurfaceBlowup.rational_subst_inv_lawCoeff
#print axioms SurfaceBlowup.lawWf_rootLaw
#print axioms SurfaceBlowup.lawCoef_globalLaw_false_zero
#print axioms SurfaceBlowup.lawCoef_rootLaw_zero
#print axioms SurfaceBlowup.lawCoef_globalLaw_false_eq_recipCoef_rootLaw
#print axioms SurfaceBlowup.reciprocity_recipRat
#print axioms SurfaceBlowup.clusterExpr_subst_inv_rational
#print axioms SurfaceBlowup.recip_main_all_degrees
#print axioms SurfaceBlowup.reciprocity_ringHom
#print axioms SurfaceBlowup.Tests.isAdic_maximalIdeal_padicInt
#print axioms SurfaceBlowup.Tests.card_residueField_padicInt
#print axioms SurfaceBlowup.Tests.main_dvr_padicInt
#print axioms SurfaceBlowup.Tests.universal_type_laws_padicInt
#print axioms SurfaceBlowup.Tests.monicDensity_padicInt_two_ramified

#check @SurfaceBlowup.universal_type_laws
#check @SurfaceBlowup.reciprocity_ringHom
#check @SurfaceBlowup.Tests.main_dvr_padicInt
#check @SurfaceBlowup.Tests.universal_type_laws_padicInt
