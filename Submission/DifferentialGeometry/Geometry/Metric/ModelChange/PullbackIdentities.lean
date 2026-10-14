import Submission.DifferentialGeometry.Geometry.Metric.ModelChange
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.SmoothRiemannianMetric

open scoped _root_.Manifold _root_.ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem transContinuousLinearEquiv_restrictOpen
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F)
    (U : TopologicalSpace.Opens M) :
    (g.transContinuousLinearEquiv e).restrictOpen U =
      (g.restrictOpen U).transContinuousLinearEquiv e := by
  exact g.restrictOpen_transContinuousLinearEquiv e U

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.transContinuousLinearEquiv_restrictOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.transContinuousLinearEquiv_restrictOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.transContinuousLinearEquiv_restrictOpen ``Submission.DifferentialGeometry.SmoothRiemannianMetric.transContinuousLinearEquiv_restrictOpen

theorem transContinuousLinearEquiv_pullbackMetric
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
    (g : SmoothRiemannianMetric I N) (e : E ≃L[ℝ] F)
    (d : M ≃ₘ⟮I, I⟯ N)
    (dJ : M ≃ₘ⟮I.transContinuousLinearEquiv e, I.transContinuousLinearEquiv e⟯ N)
    (hd : (dJ : M → N) = (d : M → N)) :
    (Diffeomorph.pullbackMetric g d).transContinuousLinearEquiv e =
      Diffeomorph.pullbackMetric (g.transContinuousLinearEquiv e) dJ := by
  let aM := (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e).symm
  let aN := (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I N e).symm
  change Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetric g d) aM =
    Diffeomorph.pullbackMetric (Diffeomorph.pullbackMetricCross g aN) dJ
  rw [← Diffeomorph.pullbackMetricCross_eq_pullbackMetric g d,
    ← Diffeomorph.pullbackMetricCross_eq_pullbackMetric
      (Diffeomorph.pullbackMetricCross g aN) dJ,
    Diffeomorph.pullbackMetricCross_trans, Diffeomorph.pullbackMetricCross_trans]
  congr 1
  ext x
  exact (congrFun hd x).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothRiemannianMetric.transContinuousLinearEquiv_pullbackMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothRiemannianMetric.transContinuousLinearEquiv_pullbackMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothRiemannianMetric.transContinuousLinearEquiv_pullbackMetric ``Submission.DifferentialGeometry.SmoothRiemannianMetric.transContinuousLinearEquiv_pullbackMetric

end

end DifferentialGeometry.SmoothRiemannianMetric
