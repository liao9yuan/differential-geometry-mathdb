import Submission.DifferentialGeometry.Geometry.Connection.Pullback
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

namespace CovariantDerivative
open _root_.CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [FiniteDimensional ℝ F₁]
variable {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, InnerProductSpace ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [ContMDiffVectorBundle 1 F₁ V₁ I] [IsContMDiffRiemannianBundle I 1 F₁ V₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [FiniteDimensional ℝ F₂]
variable {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, InnerProductSpace ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [ContMDiffVectorBundle 1 F₂ V₂ I] [IsContMDiffRiemannianBundle I 1 F₂ V₂]

open _root_.CovariantDerivative _root_.CovariantDerivative.IsMetricCompatible in
theorem IsMetricCompatible.pullbackFiberwiseLinearEquiv_of_inner_eq_mul
    {cov : CovariantDerivative I F₂ V₂} (hcov : cov.IsMetricCompatible)
    (φ : ∀ x, V₁ x ≃ₗ[ℝ] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) 1
      (fun p : _root_.Bundle.TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : _root_.Bundle.TotalSpace F₂ V₂)))
    (c : ℝ) (hc : c ≠ 0)
    (hinner : ∀ x v w, _root_.Inner.inner ℝ (φ x v) (φ x w) = c * _root_.Inner.inner ℝ v w) :
    (CovariantDerivative.pullbackFiberwiseLinearEquiv φ hφ cov).IsMetricCompatible := by
  classical
  unfold _root_.CovariantDerivative.IsMetricCompatible
  funext x
  ext v w X
  rw [_root_.CovariantDerivative.derivMetricTensor_apply_eq_extend]
  let σ := FiberBundle.extend F₁ v
  let τ := FiberBundle.extend F₁ w
  have hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F₁)) (T% σ) x :=
    FiberBundle.mdifferentiableAt_extend I F₁ v
  have hτ : MDifferentiableAt I (I.prod 𝓘(ℝ, F₁)) (T% τ) x :=
    FiberBundle.mdifferentiableAt_extend I F₁ w
  have hφσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F₂)) (T% (fun y => φ y (σ y))) x :=
    (hφ.mdifferentiableAt one_ne_zero).comp x hσ
  have hφτ : MDifferentiableAt I (I.prod 𝓘(ℝ, F₂)) (T% (fun y => φ y (τ y))) x :=
    (hφ.mdifferentiableAt one_ne_zero).comp x hτ
  have hmetric := hcov.mvfderiv_inner_eq
    (Function.update (fun y => (0 : TangentSpace I y)) x X) hφσ hφτ
  simp only [Function.update_self] at hmetric
  rw [← map_pullbackFiberwiseLinearEquiv_apply φ hφ cov σ x X,
    ← map_pullbackFiberwiseLinearEquiv_apply φ hφ cov τ x X] at hmetric
  simp_rw [hinner] at hmetric
  have hd := mvfderiv_smul (I := I) (a := fun _ : M => c)
    (mdifferentiableAt_const (c := c)) (hσ.inner_bundle hτ)
  simp only [mvfderiv_const, ContinuousLinearMap.zero_smulRight, add_zero] at hd
  change mvfderiv (I := I) (fun y => c * _root_.Inner.inner ℝ (σ y) (τ y)) x =
    c • mvfderiv (I := I) (fun y => _root_.Inner.inner ℝ (σ y) (τ y)) x at hd
  rw [hd, smul_apply, smul_eq_mul, ← mul_add] at hmetric
  have hcancel := mul_left_cancel₀ hc hmetric
  simp only [σ, τ, FiberBundle.extend_apply_self] at hcancel
  simp only [Pi.zero_apply, zero_apply]
  linarith

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.CovariantDerivative.IsMetricCompatible
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.IsMetricCompatible.pullbackFiberwiseLinearEquiv_of_inner_eq_mul then
    throwError "Refusing to shadow existing declaration CovariantDerivative.IsMetricCompatible.pullbackFiberwiseLinearEquiv_of_inner_eq_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.IsMetricCompatible.pullbackFiberwiseLinearEquiv_of_inner_eq_mul ``Submission.CovariantDerivative.IsMetricCompatible.pullbackFiberwiseLinearEquiv_of_inner_eq_mul


open _root_.CovariantDerivative _root_.CovariantDerivative.IsMetricCompatible in
theorem IsMetricCompatible.pullbackFiberwiseLinearEquiv
    {cov : CovariantDerivative I F₂ V₂} (hcov : cov.IsMetricCompatible)
    (φ : ∀ x, V₁ x ≃ₗ[ℝ] V₂ x)
    (hφ : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) 1
      (fun p : _root_.Bundle.TotalSpace F₁ V₁ => (⟨p.1, φ p.1 p.2⟩ : _root_.Bundle.TotalSpace F₂ V₂)))
    (hφinner : ∀ x v w, _root_.Inner.inner ℝ (φ x v) (φ x w) = _root_.Inner.inner ℝ v w) :
    (CovariantDerivative.pullbackFiberwiseLinearEquiv φ hφ cov).IsMetricCompatible := by
  apply hcov.pullbackFiberwiseLinearEquiv_of_inner_eq_mul φ hφ 1 one_ne_zero
  intro x v w
  simpa only [one_mul] using hφinner x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.IsMetricCompatible.pullbackFiberwiseLinearEquiv then
    throwError "Refusing to shadow existing declaration CovariantDerivative.IsMetricCompatible.pullbackFiberwiseLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.IsMetricCompatible.pullbackFiberwiseLinearEquiv ``Submission.CovariantDerivative.IsMetricCompatible.pullbackFiberwiseLinearEquiv

end CovariantDerivative
