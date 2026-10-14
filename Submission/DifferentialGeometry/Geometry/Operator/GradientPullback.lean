import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import Submission.DifferentialGeometry.Bundle.PartialMfderiv.Composition

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
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

omit [T2Space M] in
theorem mfderiv_gradientFun_eq_of_pullback_inner
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : M → N) (x : M) (hΦ : MDifferentiableAt I J Φ x)
    (hinner : ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    (hsurj : Function.Surjective (mfderiv I J Φ x))
    (f : N → ℝ) (hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (Φ x)) :
    mfderiv I J Φ x (gradientFun g (f ∘ Φ) x) = gradientFun h f (Φ x) := by
  apply (metricFlatEquiv h (Φ x)).injective
  ext v
  obtain ⟨w, rfl⟩ := hsurj v
  rw [metricFlatEquiv_apply, metricFlatEquiv_apply, inner_gradientFun, ← hinner,
    inner_gradientFun, mvfderiv_comp_apply x hf hΦ w]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.mfderiv_gradientFun_eq_of_pullback_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.mfderiv_gradientFun_eq_of_pullback_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.mfderiv_gradientFun_eq_of_pullback_inner ``Submission.DifferentialGeometry.Geometry.Operator.mfderiv_gradientFun_eq_of_pullback_inner

omit [T2Space M] in
theorem normGradSqFun_eq_of_pullback_inner
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : M → N) (x : M) (hΦ : MDifferentiableAt I J Φ x)
    (hinner : ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    (hsurj : Function.Surjective (mfderiv I J Φ x))
    (f : N → ℝ) (hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (Φ x)) :
    normGradSqFun g (f ∘ Φ) x = normGradSqFun h f (Φ x) := by
  change g.inner x (gradientFun g (f ∘ Φ) x) (gradientFun g (f ∘ Φ) x) =
    h.inner (Φ x) (gradientFun h f (Φ x)) (gradientFun h f (Φ x))
  rw [hinner, mfderiv_gradientFun_eq_of_pullback_inner g h Φ x hΦ hinner hsurj f hf]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.normGradSqFun_eq_of_pullback_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.normGradSqFun_eq_of_pullback_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.normGradSqFun_eq_of_pullback_inner ``Submission.DifferentialGeometry.Geometry.Operator.normGradSqFun_eq_of_pullback_inner

theorem mfderiv_gradientFun_pullback
    (g : SmoothRiemannianMetric J N) (φ : M → N) (hφ : ContMDiff I J ∞ φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J φ x))
    (f : N → ℝ) (x : M) (hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (φ x))
    (hsurj : Function.Surjective (mfderiv I J φ x)) :
    mfderiv I J φ x (gradientFun (g.pullback φ hφ hinj) (f ∘ φ) x) =
      gradientFun g f (φ x) := by
  exact mfderiv_gradientFun_eq_of_pullback_inner (g.pullback φ hφ hinj) g φ x
    (hφ.mdifferentiableAt (by simp))
    (SmoothRiemannianMetric.pullback_inner g φ hφ hinj x) hsurj f hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.mfderiv_gradientFun_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.mfderiv_gradientFun_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.mfderiv_gradientFun_pullback ``Submission.DifferentialGeometry.Geometry.Operator.mfderiv_gradientFun_pullback

theorem normGradSqFun_pullback
    (g : SmoothRiemannianMetric J N) (φ : M → N) (hφ : ContMDiff I J ∞ φ)
    (hinj : ∀ x, Function.Injective (mfderiv I J φ x))
    (f : N → ℝ) (x : M) (hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (φ x))
    (hsurj : Function.Surjective (mfderiv I J φ x)) :
    normGradSqFun (g.pullback φ hφ hinj) (f ∘ φ) x = normGradSqFun g f (φ x) := by
  exact normGradSqFun_eq_of_pullback_inner (g.pullback φ hφ hinj) g φ x
    (hφ.mdifferentiableAt (by simp))
    (SmoothRiemannianMetric.pullback_inner g φ hφ hinj x) hsurj f hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.normGradSqFun_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.normGradSqFun_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.normGradSqFun_pullback ``Submission.DifferentialGeometry.Geometry.Operator.normGradSqFun_pullback

end

end DifferentialGeometry.Geometry.Operator
