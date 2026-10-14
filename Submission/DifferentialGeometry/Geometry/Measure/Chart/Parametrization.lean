import Submission.DifferentialGeometry.Analysis.Integration.Measure.Parametric.Evaluation
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem paramDensity_extChartAt_symm (g : SmoothRiemannianMetric I M) (x : M)
    {w : E} (hw : w ∈ (extChartAt I x).target) :
    paramDensity g (PartialDiffeomorph.extChartAt I 1 x).symm w =
      chartDensity g x ((extChartAt I x).symm w) := by
  let Φ := (PartialDiffeomorph.extChartAt I 1 x).symm
  have hsource : w ∈ Φ.source := hw
  have hx : Φ w ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet := by
    change (extChartAt I x).symm w ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet
    simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using
      (extChartAt I x).map_target hw
  have hlocal : paramChartMap x Φ =ᶠ[𝓝 w] id := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hw] with z hz
    exact (extChartAt I x).right_inv hz
  have hd : fderiv ℝ (paramChartMap x Φ) w = ContinuousLinearMap.id ℝ E := by
    rw [hlocal.fderiv_eq]
    exact fderiv_id
  have hdet : (ContinuousLinearMap.id ℝ E).det = 1 := LinearMap.det_id
  have h := paramDensity_eq_abs_det_mul_chartDensity g x Φ hsource hx
  rw [hd, hdet, abs_one, one_mul] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.paramDensity_extChartAt_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.paramDensity_extChartAt_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.paramDensity_extChartAt_symm ``Submission.DifferentialGeometry.Integral.Measure.paramDensity_extChartAt_symm

end DifferentialGeometry.Integral.Measure
