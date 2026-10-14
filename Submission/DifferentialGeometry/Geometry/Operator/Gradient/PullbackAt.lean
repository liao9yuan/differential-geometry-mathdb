import Submission.DifferentialGeometry.Geometry.Operator.GradientPullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


namespace DifferentialGeometry.Geometry.Operator

open scoped _root_.Manifold _root_.ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

theorem mfderiv_gradientFun_comp_of_pullback_inner
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {φ : M → N} {x : M} (hφ : MDifferentiableAt I J φ x)
    (hinner : ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (φ x) (mfderiv I J φ x v) (mfderiv I J φ x w))
    (hsurj : Function.Surjective (mfderiv I J φ x))
    {f : N → ℝ} (hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (φ x)) :
    mfderiv I J φ x (gradientFun g (f ∘ φ) x) = gradientFun h f (φ x) := by
  apply (metricFlatEquiv h (φ x)).injective
  ext v
  obtain ⟨w, rfl⟩ := hsurj v
  rw [metricFlatEquiv_apply, metricFlatEquiv_apply, inner_gradientFun,
    ← hinner, inner_gradientFun, mvfderiv_comp_apply x hf hφ w]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.mfderiv_gradientFun_comp_of_pullback_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.mfderiv_gradientFun_comp_of_pullback_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.mfderiv_gradientFun_comp_of_pullback_inner ``Submission.DifferentialGeometry.Geometry.Operator.mfderiv_gradientFun_comp_of_pullback_inner

theorem normGradSqFun_comp_of_pullback_inner
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {φ : M → N} {x : M} (hφ : MDifferentiableAt I J φ x)
    (hinner : ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (φ x) (mfderiv I J φ x v) (mfderiv I J φ x w))
    (hsurj : Function.Surjective (mfderiv I J φ x))
    {f : N → ℝ} (hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (φ x)) :
    normGradSqFun g (f ∘ φ) x = normGradSqFun h f (φ x) := by
  change g.inner x (gradientFun g (f ∘ φ) x) (gradientFun g (f ∘ φ) x) =
    h.inner (φ x) (gradientFun h f (φ x)) (gradientFun h f (φ x))
  rw [hinner, mfderiv_gradientFun_comp_of_pullback_inner g h hφ hinner hsurj hf]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.normGradSqFun_comp_of_pullback_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.normGradSqFun_comp_of_pullback_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.normGradSqFun_comp_of_pullback_inner ``Submission.DifferentialGeometry.Geometry.Operator.normGradSqFun_comp_of_pullback_inner

end

end DifferentialGeometry.Geometry.Operator
