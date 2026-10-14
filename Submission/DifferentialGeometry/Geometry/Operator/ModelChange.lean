import Submission.DifferentialGeometry.Geometry.Metric.ModelChange
import Submission.DifferentialGeometry.Geometry.Operator.Pullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Geometry.Operator

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem normGradSqFun_transContinuousLinearEquiv
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F)
    (f : M → ℝ) (x : M) (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    normGradSqFun (g.transContinuousLinearEquiv e) f x = normGradSqFun g f x := by
  let Φ := (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e).symm
  change normGradSqFun (Diffeomorph.pullbackMetricCross g Φ) (f ∘ Φ) x = _
  rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric]
  exact normGradSqFun_localPull g Φ Φ.isLocalDiffeomorph f x hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.normGradSqFun_transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.normGradSqFun_transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.normGradSqFun_transContinuousLinearEquiv ``Submission.DifferentialGeometry.Geometry.Operator.normGradSqFun_transContinuousLinearEquiv

theorem mfderiv_gradientFun_transContinuousLinearEquiv
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F)
    (f : M → ℝ) (x : M) (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    mfderiv (I.transContinuousLinearEquiv e) I id x (gradientFun (g.transContinuousLinearEquiv e) f x) =
      gradientFun g f x := by
  let Φ := (ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e).symm
  change mfderiv (I.transContinuousLinearEquiv e) I Φ x
    (gradientFun (Diffeomorph.pullbackMetricCross g Φ) (f ∘ Φ) x) = _
  rw [gradientFun_pullbackCross g Φ f x hf,
    ← Φ.mfderivToContinuousLinearEquiv_coe (by simp)]
  exact (Φ.mfderivToContinuousLinearEquiv (by simp) x).apply_symm_apply _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.mfderiv_gradientFun_transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.mfderiv_gradientFun_transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.mfderiv_gradientFun_transContinuousLinearEquiv ``Submission.DifferentialGeometry.Geometry.Operator.mfderiv_gradientFun_transContinuousLinearEquiv

end

end DifferentialGeometry.Geometry.Operator
