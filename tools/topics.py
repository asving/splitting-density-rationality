"""Topic assignment for the unified hierarchy (cycle 1, mechanical)."""
import re

DEF_TOPIC = {
 # statement-level definitions (trust boundary): Basic
 'Types':'Basic','Expressions':'Basic','State':'Basic','Patterns':'Basic','Weights':'Basic','Law':'Basic',
 'Recursion':'Basic','Density':'Basic','OrigDensity':'Basic','Core':'Basic','PadicField':'Basic',
 # combinatorics of the recursion
 'StateContact':'Formula',
 # algebra / types
 'AlgebraType':'Algebra','OrderDefect':'Algebra',
 # measure
 'AdicDigits':'Measure','CylinderFamily':'Measure','IdealCoordinates':'Measure','Normalizer':'Measure',
 'IdealAtlas':'Measure','IdealChartSigma':'Measure','UnramifiedMeasure':'Measure',
 # unramified / factor cells
 'UnramifiedExtension':'Unramified','FactorCells':'Unramified','FrobeniusDescent':'Unramified',
 'BinaryForms':'Unramified','ProjectiveCells':'Unramified','HomogeneousCells':'Unramified',
 # surfaces
 'ResidueIdeals':'Surfaces','ConcreteSurfaces':'Surfaces','SuccessorCharts':'Surfaces','KillX':'Surfaces',
 'SurfaceData':'Surfaces','TwoTermCokernels':'Surfaces','LinearTowers':'Surfaces',
 # blowup geometry
 'BlowupCharts':'Blowup','FiniteBlowupCharts':'Blowup','PrincipalPowerLayers':'Blowup','ActualCechLevels':'Blowup',
 'ActualCechThreads':'Blowup','SurfaceSections':'Blowup','GluedGenerators':'Blowup','CurveSections':'Blowup',
 'CompletedLocalPoints':'Blowup','FiniteSupport':'Blowup','TwoChartCurveData':'Blowup','CurveDataDegree':'Blowup',
 'CurveOrderLimit':'Blowup','ChildOrder':'Blowup','ClosedDirections':'Blowup','DivisorPoints':'Blowup',
 'ChildIdealSets':'Blowup','StrictNormalization':'Blowup','StrictChartCoordinates':'Blowup','StrictPullback':'Blowup',
 'TangentCells':'Blowup','DivisorPatterns':'Blowup',
 # recursion
 'CellAssignments':'Recursion','CellChildData':'Recursion','ConcreteMembers':'Recursion','MeasuredSurfaces':'Recursion',
 'RecursionEvents':'Recursion','RootCellLaw':'Assembly','TypeEvents':'Assembly',
 # reciprocity
 'RecipRational':'Reciprocity','RecipCoef':'Reciprocity','RecipSeries':'Reciprocity','RecipQuantum':'Reciprocity',
}

BATCH_TOPIC = [
 (r'^reciprocity', 'Reciprocity'),
 (r'^(l92_|g6_02|classical_degree|captain_pattern_count|captain_cycle12)', 'Formula'),
 (r'^(g7b_b_haar|lattice_measure|atlas_measure|ideal_atlas|captain_state_measure|g3$|meas_0[0-2]|meas_0[45]|captain_cycle9_sigma|captain_cycle11)', 'Measure'),
 (r'^(g7_|g7b_|local_descent|g0g1_g1|g1$)', 'Unramified'),
 (r'^g0g1_g0', 'FieldForm'),
 (r'^(g2_|g2s_|splits_|captain_completeness|captain_concrete_atlas|captain_concrete_points)', 'Surfaces'),
 (r'^(g6_01)', 'Algebra'),
 (r'^(g6_|term_|captain_cycle8|meas_03|captain_cycle9_exports|captain_cycle6)', 'Recursion'),
 (r'.', 'Blowup'),
]

KEYWORD_TOPIC = [
 (r'^recip_', 'Reciprocity'),
 (r'(hensel|cylinder|_mass$|_count$|quotient_card|fiber_length|kills|volume|orbit)', 'Measure'),
 (r'(expression|law_|_law$|type_degree|finite_types|state_|rank_|tri_|weight|geometric|children|child_|terminal|global_|prime_power|safe|normalizer|divisor_probability|polynomial_degree|polynomial_type|projective_normalizer)', 'Formula'),
]

GEN_TOPIC = {
 'Thm_Gen_Ascent':'Algebra','Thm_Gen_ClosureTransfer':'Algebra','Thm_Gen_SepHelpers':'Algebra','Thm_Gen_TypeDvd':'Algebra',
 'Thm_Gen_UnramifiedAscent':'Unramified','Thm_Gen_FiniteClosureLeaves':'Algebra',
 'Thm_Gen_PolyZeroNull':'Measure','Thm_Gen_InseparableNull':'Measure','Thm_Gen_ProjBridge':'Assembly',
 'Thm_Gen_MainDvr':'Main',
}

def topic(mod, batch):
    if mod.startswith('Def_SurfaceBlowupV2_'):
        return DEF_TOPIC[mod[len('Def_SurfaceBlowupV2_'):]]
    if mod in GEN_TOPIC:
        return GEN_TOPIC[mod]
    slug = mod.replace('Thm_SurfaceBlowupV2_', '')
    if slug.startswith('recip_'):
        return 'Reciprocity'
    if slug.startswith('integral_closure') or 'algebra_type' in slug or 'factor_invariant' in slug:
        return 'Algebra'
    if slug.startswith('padicIntegers') or 'intrinsic' in slug or 'field_form' in slug:
        return 'FieldForm'
    if slug.startswith('monic_formula') or slug.startswith('projective_formula') or 'root_cell_law' in slug:
        return 'Assembly'
    if batch and batch not in ('NONE', 'build_blueprint') and not batch.startswith('MULTI'):
        for pat, t in BATCH_TOPIC:
            if re.search(pat, batch):
                return t
    if batch and batch.startswith('MULTI:'):
        b = batch[6:].split(',')[0]
        for pat, t in BATCH_TOPIC:
            if re.search(pat, b):
                return t
    for pat, t in KEYWORD_TOPIC:
        if re.search(pat, slug):
            return t
    return None  # decided by neighbours
