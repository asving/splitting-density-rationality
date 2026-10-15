# per-source-file textual fixups applied after the generic transform (cycle-1 merge breakages)
HB = '-- merged-module elaboration is slower than in the isolated node (more instances/simp lemmas in scope)\nset_option maxHeartbeats 1000000 in\n'
FIXUPS = {
 'Thm_SurfaceBlowupV2_two_chart_layer_correction': [
   ('theorem SurfaceBlowup.two_chart_layer_correction ', HB + 'theorem SurfaceBlowup.two_chart_layer_correction ')],
}
