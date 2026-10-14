import Submission.DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import Submission.DifferentialGeometry.Analysis.Parabolic.WeakEquation.IntegralLinearity

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

private theorem parabolic_test_residual_eq_covector
    (g : SmoothRiemannianMetric I M) (t : ℝ) (x : M)
    (w : ℝ) (X : TangentSpace I x) (ψ : ℝ × M → ℝ) :
    w * (deriv (fun s => ψ (s, x)) t +
      g.inner x X (gradientFun g (fun y => ψ (t, y)) x)) =
      w * deriv (fun s => ψ (s, x)) t +
        (w • ContinuousLinearMap.apply ℝ ℝ X).toLinearMap
          (mvfderiv I (fun y => ψ (t, y)) x) := by
  rw [g.symm x X (gradientFun g (fun y => ψ (t, y)) x), inner_gradientFun]
  simp only [ContinuousLinearMap.coe_coe, smul_apply,
    ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.parabolic_test_residual_eq_covector
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.parabolic_test_residual_eq_covector target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem differentiableAt_time_slice_of_contMDiff
    {ψ : ℝ × M → ℝ}
    (hψ : ContMDiff ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) 1 ψ)
    (t : ℝ) (x : M) :
    DifferentiableAt ℝ (fun s => ψ (s, x)) t := by
  have ht : ContDiff ℝ 1 (fun s : ℝ => ψ (s, x)) :=
    contMDiff_iff_contDiff.mp (hψ.comp (contMDiff_id.prodMk contMDiff_const))
  exact (ht.differentiable one_ne_zero).differentiableAt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.differentiableAt_time_slice_of_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.differentiableAt_time_slice_of_contMDiff target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem mdifferentiableAt_spatial_slice_of_contMDiff
    {ψ : ℝ × M → ℝ}
    (hψ : ContMDiff ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) 1 ψ)
    (t : ℝ) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => ψ (t, y)) x :=
  (hψ.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt one_ne_zero

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.mdifferentiableAt_spatial_slice_of_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.mdifferentiableAt_spatial_slice_of_contMDiff target :: scope.openDecls } }

variable [MeasurableSpace M]

theorem integrable_and_integral_integral_parabolic_test_residual_add
    (μ : _root_.MeasureTheory.Measure ℝ) (ν : ℝ → _root_.MeasureTheory.Measure M)
    (g : ℝ → SmoothRiemannianMetric I M) (w : ℝ × M → ℝ)
    (X : ℝ → (x : M) → TangentSpace I x)
    {ψ χ : ℝ × M → ℝ}
    (hψt : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t, DifferentiableAt ℝ (fun s => ψ (s, x)) t)
    (hχt : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t, DifferentiableAt ℝ (fun s => χ (s, x)) t)
    (hψx : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t,
      MDifferentiableAt I 𝓘(ℝ) (fun y => ψ (t, y)) x)
    (hχx : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t,
      MDifferentiableAt I 𝓘(ℝ) (fun y => χ (t, y)) x)
    (hψint : ∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (fun x => w (t, x) *
      (deriv (fun s => ψ (s, x)) t +
        (g t).inner x (X t x) (gradientFun (g t) (fun y => ψ (t, y)) x))) (ν t))
    (hχint : ∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (fun x => w (t, x) *
      (deriv (fun s => χ (s, x)) t +
        (g t).inner x (X t x) (gradientFun (g t) (fun y => χ (t, y)) x))) (ν t))
    (hψtime : _root_.MeasureTheory.Integrable (fun t => ∫ x, w (t, x) *
      (deriv (fun s => ψ (s, x)) t +
        (g t).inner x (X t x) (gradientFun (g t) (fun y => ψ (t, y)) x)) ∂ν t) μ)
    (hχtime : _root_.MeasureTheory.Integrable (fun t => ∫ x, w (t, x) *
      (deriv (fun s => χ (s, x)) t +
        (g t).inner x (X t x) (gradientFun (g t) (fun y => χ (t, y)) x)) ∂ν t) μ) :
    let R := fun (u : ℝ × M → ℝ) (t : ℝ) (x : M) => w (t, x) *
      (deriv (fun s => u (s, x)) t +
        (g t).inner x (X t x) (gradientFun (g t) (fun y => u (t, y)) x))
    (∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (R (ψ + χ) t) (ν t)) ∧
      _root_.MeasureTheory.Integrable (fun t => ∫ x, R (ψ + χ) t x ∂ν t) μ ∧
      (∫ t, ∫ x, R (ψ + χ) t x ∂ν t ∂μ) =
        (∫ t, ∫ x, R ψ t x ∂ν t ∂μ) + ∫ t, ∫ x, R χ t x ∂ν t ∂μ := by
  let A := fun z : ℝ × M =>
    (w z • ContinuousLinearMap.apply ℝ ℝ (X z.1 z.2)).toLinearMap
  have hR (u : ℝ × M → ℝ) (t : ℝ) (x : M) :
      w (t, x) * (deriv (fun s => u (s, x)) t +
        (g t).inner x (X t x) (gradientFun (g t) (fun y => u (t, y)) x)) =
      w (t, x) * deriv (fun s => u (s, x)) t +
        A (t, x) (mvfderiv I (fun y => u (t, y)) x) :=
    parabolic_test_residual_eq_covector (g t) t x (w (t, x)) (X t x) u
  have h := Analysis.Parabolic.integrable_and_integral_integral_time_spatial_derivative_add
    μ ν w A (f := ψ) (h := χ) hψt hχt hψx hχx
    (by simpa only [← hR] using hψint)
    (by simpa only [← hR] using hχint)
    (by simpa only [← hR] using hψtime)
    (by simpa only [← hR] using hχtime)
  simpa only [← hR] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.integrable_and_integral_integral_parabolic_test_residual_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.integrable_and_integral_integral_parabolic_test_residual_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.integrable_and_integral_integral_parabolic_test_residual_add ``Submission.DifferentialGeometry.Geometry.Operator.integrable_and_integral_integral_parabolic_test_residual_add

theorem integrable_and_integral_integral_parabolic_test_residual_add_of_contMDiff
    (μ : _root_.MeasureTheory.Measure ℝ) (ν : ℝ → _root_.MeasureTheory.Measure M)
    (g : ℝ → SmoothRiemannianMetric I M) (w : ℝ × M → ℝ)
    (X : ℝ → (x : M) → TangentSpace I x)
    {ψ χ : ℝ × M → ℝ}
    (hψ : ContMDiff ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) 1 ψ)
    (hχ : ContMDiff ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) 1 χ)
    (hψint : ∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (fun x => w (t, x) *
      (deriv (fun s => ψ (s, x)) t +
        (g t).inner x (X t x) (gradientFun (g t) (fun y => ψ (t, y)) x))) (ν t))
    (hχint : ∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (fun x => w (t, x) *
      (deriv (fun s => χ (s, x)) t +
        (g t).inner x (X t x) (gradientFun (g t) (fun y => χ (t, y)) x))) (ν t))
    (hψtime : _root_.MeasureTheory.Integrable (fun t => ∫ x, w (t, x) *
      (deriv (fun s => ψ (s, x)) t +
        (g t).inner x (X t x) (gradientFun (g t) (fun y => ψ (t, y)) x)) ∂ν t) μ)
    (hχtime : _root_.MeasureTheory.Integrable (fun t => ∫ x, w (t, x) *
      (deriv (fun s => χ (s, x)) t +
        (g t).inner x (X t x) (gradientFun (g t) (fun y => χ (t, y)) x)) ∂ν t) μ) :
    let R := fun (u : ℝ × M → ℝ) (t : ℝ) (x : M) => w (t, x) *
      (deriv (fun s => u (s, x)) t +
        (g t).inner x (X t x) (gradientFun (g t) (fun y => u (t, y)) x))
    (∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (R (ψ + χ) t) (ν t)) ∧
      _root_.MeasureTheory.Integrable (fun t => ∫ x, R (ψ + χ) t x ∂ν t) μ ∧
      (∫ t, ∫ x, R (ψ + χ) t x ∂ν t ∂μ) =
        (∫ t, ∫ x, R ψ t x ∂ν t ∂μ) + ∫ t, ∫ x, R χ t x ∂ν t ∂μ := by
  exact integrable_and_integral_integral_parabolic_test_residual_add μ ν g w X
    (_root_.MeasureTheory.ae_of_all μ fun t => _root_.MeasureTheory.ae_of_all (ν t) fun x =>
      differentiableAt_time_slice_of_contMDiff hψ t x)
    (_root_.MeasureTheory.ae_of_all μ fun t => _root_.MeasureTheory.ae_of_all (ν t) fun x =>
      differentiableAt_time_slice_of_contMDiff hχ t x)
    (_root_.MeasureTheory.ae_of_all μ fun t => _root_.MeasureTheory.ae_of_all (ν t) fun x =>
      mdifferentiableAt_spatial_slice_of_contMDiff hψ t x)
    (_root_.MeasureTheory.ae_of_all μ fun t => _root_.MeasureTheory.ae_of_all (ν t) fun x =>
      mdifferentiableAt_spatial_slice_of_contMDiff hχ t x)
    hψint hχint hψtime hχtime

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.integrable_and_integral_integral_parabolic_test_residual_add_of_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.integrable_and_integral_integral_parabolic_test_residual_add_of_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.integrable_and_integral_integral_parabolic_test_residual_add_of_contMDiff ``Submission.DifferentialGeometry.Geometry.Operator.integrable_and_integral_integral_parabolic_test_residual_add_of_contMDiff

theorem integrable_and_integral_integral_parabolic_test_residual_const_mul
    (μ : _root_.MeasureTheory.Measure ℝ) (ν : ℝ → _root_.MeasureTheory.Measure M)
    (g : ℝ → SmoothRiemannianMetric I M) (w : ℝ × M → ℝ)
    (X : ℝ → (x : M) → TangentSpace I x)
    (c : ℝ) {ψ : ℝ × M → ℝ}
    (hψint : ∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (fun x => w (t, x) *
      (deriv (fun s => ψ (s, x)) t +
        (g t).inner x (X t x) (gradientFun (g t) (fun y => ψ (t, y)) x))) (ν t))
    (hψtime : _root_.MeasureTheory.Integrable (fun t => ∫ x, w (t, x) *
      (deriv (fun s => ψ (s, x)) t +
        (g t).inner x (X t x) (gradientFun (g t) (fun y => ψ (t, y)) x)) ∂ν t) μ) :
    let R := fun (u : ℝ × M → ℝ) (t : ℝ) (x : M) => w (t, x) *
      (deriv (fun s => u (s, x)) t +
        (g t).inner x (X t x) (gradientFun (g t) (fun y => u (t, y)) x))
    (∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (R (c • ψ) t) (ν t)) ∧
      _root_.MeasureTheory.Integrable (fun t => ∫ x, R (c • ψ) t x ∂ν t) μ ∧
      (∫ t, ∫ x, R (c • ψ) t x ∂ν t ∂μ) =
        c * ∫ t, ∫ x, R ψ t x ∂ν t ∂μ := by
  let A := fun z : ℝ × M =>
    (w z • ContinuousLinearMap.apply ℝ ℝ (X z.1 z.2)).toLinearMap
  have hR (u : ℝ × M → ℝ) (t : ℝ) (x : M) :
      w (t, x) * (deriv (fun s => u (s, x)) t +
        (g t).inner x (X t x) (gradientFun (g t) (fun y => u (t, y)) x)) =
      w (t, x) * deriv (fun s => u (s, x)) t +
        A (t, x) (mvfderiv I (fun y => u (t, y)) x) :=
    parabolic_test_residual_eq_covector (g t) t x (w (t, x)) (X t x) u
  have h := Analysis.Parabolic.integrable_and_integral_integral_time_spatial_derivative_const_mul
    μ ν w A c (f := ψ)
    (by simpa only [← hR] using hψint)
    (by simpa only [← hR] using hψtime)
  simpa only [← hR] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.integrable_and_integral_integral_parabolic_test_residual_const_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.integrable_and_integral_integral_parabolic_test_residual_const_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.integrable_and_integral_integral_parabolic_test_residual_const_mul ``Submission.DifferentialGeometry.Geometry.Operator.integrable_and_integral_integral_parabolic_test_residual_const_mul

end DifferentialGeometry.Geometry.Operator
