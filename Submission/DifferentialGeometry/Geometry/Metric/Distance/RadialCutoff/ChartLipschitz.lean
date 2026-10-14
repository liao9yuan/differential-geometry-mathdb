import Submission.DifferentialGeometry.Geometry.Metric.ChartLipschitz.Intrinsic
import Submission.DifferentialGeometry.Geometry.Metric.Distance.RadialCutoff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian

open scoped _root_.ContDiff _root_.ENNReal _root_.NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem locallyLipschitzOn_radialDistanceCutoff_comp_extChartAt_symm
    [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (p α : M) {R : ℝ} (hR : 0 < R) :
    LocallyLipschitzOn (extChartAt I α).target
      (radialDistanceCutoff g p R ∘ (extChartAt I α).symm) := by
  let L : ℝ≥0 := ⟨1 / R, by positivity⟩
  apply locallyLipschitzOn_comp_extChartAt_symm_of_edist_le g α (L := L)
  intro x y
  have hL : ENNReal.ofReal (1 / R) = (L : ℝ≥0∞) := by
    change ENNReal.ofReal (L : ℝ) = (L : ℝ≥0∞)
    exact ENNReal.ofReal_coe_nnreal
  simpa only [hL] using edist_radialDistanceCutoff_le g p hR x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_radialDistanceCutoff_comp_extChartAt_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_radialDistanceCutoff_comp_extChartAt_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_radialDistanceCutoff_comp_extChartAt_symm ``Submission.DifferentialGeometry.Geometry.Riemannian.locallyLipschitzOn_radialDistanceCutoff_comp_extChartAt_symm

end DifferentialGeometry.Geometry.Riemannian

end
