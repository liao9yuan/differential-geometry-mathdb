import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.ScalarConvergence
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import Submission.DifferentialGeometry.Geometry.Curvature.ScalarControlsRm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

theorem normSq_rm_le_of_metricCP_of_curvatureOperator_nonnegative
    (gSeq : ℕ → SmoothRiemannianMetric I M) (g r : SmoothRiemannianMetric I M)
    (x : M) (hconv : MetricCPConvergenceOn {x} 2 gSeq g r) (hdim : Module.finrank ℝ E = 3)
    (hnonneg : metricAlgebraicCurvatureTensorAt g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I)) {C : ℝ}
    (hbound : ∀ᶠ i in _root_.Filter.atTop, normSq0S (gSeq i) x 4 (metricRm04At (gSeq i) x) ≤ C) :
    normSq0S g x 4 (metricRm04At g x) ≤ 100 ^ 2 * (9 * Real.sqrt C) ^ 2 := by
  have hscal :=
    (hconv.tendstoUniformlyOn_metricScalarAt isCompact_singleton).tendsto_at (_root_.Set.mem_singleton x)
  have hscalar : |metricScalarAt g x| ≤ 9 * Real.sqrt C := by
    apply le_of_tendsto hscal.abs
    filter_upwards [hbound] with i hi
    have hh := (scalar_abs_le_rm (gSeq i) x).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hi) (sq_nonneg _))
    change |metricScalarAt (gSeq i) x| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt C at hh
    simpa only [hdim, Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num] using hh
  have hR := normSq_metricRm04_le_scalar_sq_of_curvatureOperator_nonnegative g x hdim hnonneg
  have hsq : (metricScalarAt g x) ^ 2 ≤ (9 * Real.sqrt C) ^ 2 := by
    have hB : 0 ≤ 9 * Real.sqrt C := by positivity
    nlinarith [sq_abs (metricScalarAt g x), abs_nonneg (metricScalarAt g x)]
  exact hR.trans (mul_le_mul_of_nonneg_left hsq (sq_nonneg _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.normSq_rm_le_of_metricCP_of_curvatureOperator_nonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.normSq_rm_le_of_metricCP_of_curvatureOperator_nonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.normSq_rm_le_of_metricCP_of_curvatureOperator_nonnegative ``Submission.DifferentialGeometry.CheegerGromovCompactness.normSq_rm_le_of_metricCP_of_curvatureOperator_nonnegative

end DifferentialGeometry.CheegerGromovCompactness
