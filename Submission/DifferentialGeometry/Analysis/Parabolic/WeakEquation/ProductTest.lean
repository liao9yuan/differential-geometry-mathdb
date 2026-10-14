import Submission.DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem gradientFun_const_mul_field
    (g : SmoothRiemannianMetric I M) (c : ℝ) (f : M → ℝ) (x : M) :
    gradientFun g (fun y => c * f y) x = c • gradientFun g f x := by
  by_cases hc : c = 0
  · subst c
    simp only [_root_.MulZeroClass.zero_mul, gradientFun_const, zero_smul]
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x
  · exact gradientFun_const_smul g c hf
  · have hcf : ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => c * f y) x := by
      intro hcf
      have hback := hcf.const_smul c⁻¹
      have hfun : c⁻¹ • (fun y => c * f y) = f := by
        funext y
        simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      rw [hfun] at hback
      exact hf hback
    have hfzero : gradientFun g f x = 0 :=
      gradientFun_eq_zero_of_mfderiv_eq_zero g f (mfderiv_zero_of_not_mdifferentiableAt hf)
    have hcfzero : gradientFun g (fun y => c * f y) x = 0 :=
      gradientFun_eq_zero_of_mfderiv_eq_zero g (fun y => c * f y)
        (mfderiv_zero_of_not_mdifferentiableAt hcf)
    rw [hcfzero, hfzero, smul_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.gradientFun_const_mul_field
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.gradientFun_const_mul_field target :: scope.openDecls } }

private theorem parabolic_test_residual_prod
    (g : SmoothRiemannianMetric I M) (w : ℝ) (t : ℝ) (x : M)
    (X : TangentSpace I x) (η : ℝ → ℝ) (χ : M → ℝ) :
    w * (deriv (fun s => η s * χ x) t +
      g.inner x X (gradientFun g (fun y => η t * χ y) x)) =
      deriv η t * (χ x * w) + η t * (w * g.inner x X (gradientFun g χ x)) := by
  rw [deriv_mul_const_field, gradientFun_const_mul_field,
    (g.inner x X).map_smul, smul_eq_mul]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.parabolic_test_residual_prod
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.parabolic_test_residual_prod target :: scope.openDecls } }

variable [MeasurableSpace M]

theorem integrable_and_integral_integral_parabolic_test_residual_prod
    (μ : _root_.MeasureTheory.Measure ℝ) (ν : ℝ → _root_.MeasureTheory.Measure M)
    (g : ℝ → SmoothRiemannianMetric I M) (w : ℝ × M → ℝ)
    (X : ℝ → (x : M) → TangentSpace I x)
    (η : ℝ → ℝ) (χ : M → ℝ)
    (hmassSpatial : ∀ᵐ t ∂μ,
      _root_.MeasureTheory.Integrable (fun x => deriv η t * (χ x * w (t, x))) (ν t))
    (hfluxSpatial : ∀ᵐ t ∂μ,
      _root_.MeasureTheory.Integrable (fun x => η t *
        (w (t, x) * (g t).inner x (X t x) (gradientFun (g t) χ x))) (ν t))
    (hmassTime : _root_.MeasureTheory.Integrable (fun t => deriv η t * (∫ x, χ x * w (t, x) ∂ν t)) μ)
    (hfluxTime : _root_.MeasureTheory.Integrable (fun t => η t *
      (∫ x, w (t, x) * (g t).inner x (X t x) (gradientFun (g t) χ x) ∂ν t)) μ) :
    let R := fun (t : ℝ) (x : M) => w (t, x) *
      (deriv (fun s => η s * χ x) t +
        (g t).inner x (X t x) (gradientFun (g t) (fun y => η t * χ y) x))
    (∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (R t) (ν t)) ∧
      _root_.MeasureTheory.Integrable (fun t => ∫ x, R t x ∂ν t) μ ∧
      (∫ t, ∫ x, R t x ∂ν t ∂μ) =
        (∫ t, deriv η t * (∫ x, χ x * w (t, x) ∂ν t) ∂μ) +
          ∫ t, η t *
            (∫ x, w (t, x) * (g t).inner x (X t x) (gradientFun (g t) χ x) ∂ν t) ∂μ := by
  intro R
  have hpoint (t : ℝ) (x : M) : R t x =
      deriv η t * (χ x * w (t, x)) + η t *
        (w (t, x) * (g t).inner x (X t x) (gradientFun (g t) χ x)) :=
    parabolic_test_residual_prod (g t) (w (t, x)) t x (X t x) η χ
  have hint : ∀ᵐ t ∂μ, (∫ x, R t x ∂ν t) =
      deriv η t * (∫ x, χ x * w (t, x) ∂ν t) + η t *
        (∫ x, w (t, x) * (g t).inner x (X t x) (gradientFun (g t) χ x) ∂ν t) := by
    filter_upwards [hmassSpatial, hfluxSpatial] with t htMass htFlux
    rw [_root_.MeasureTheory.integral_congr_ae (_root_.MeasureTheory.ae_of_all (ν t) (hpoint t)), _root_.MeasureTheory.integral_add htMass htFlux,
      _root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const_mul]
  refine ⟨?_, (hmassTime.add hfluxTime).congr (Filter.EventuallyEq.symm hint), ?_⟩
  · filter_upwards [hmassSpatial, hfluxSpatial] with t htMass htFlux
    exact (htMass.add htFlux).congr (_root_.MeasureTheory.ae_of_all (ν t) fun x => (hpoint t x).symm)
  · rw [_root_.MeasureTheory.integral_congr_ae hint, _root_.MeasureTheory.integral_add hmassTime hfluxTime]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.integrable_and_integral_integral_parabolic_test_residual_prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.integrable_and_integral_integral_parabolic_test_residual_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.integrable_and_integral_integral_parabolic_test_residual_prod ``Submission.DifferentialGeometry.Geometry.Operator.integrable_and_integral_integral_parabolic_test_residual_prod

end DifferentialGeometry.Geometry.Operator
