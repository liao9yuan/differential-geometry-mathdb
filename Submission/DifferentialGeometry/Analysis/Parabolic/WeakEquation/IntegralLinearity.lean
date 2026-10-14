import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic

open _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [MeasurableSpace M]

omit [MeasurableSpace M] in
private theorem time_spatial_derivative_add
    (w : ℝ × M → ℝ)
    (A : ∀ z : ℝ × M, (TangentSpace I z.2 →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    {f h : ℝ × M → ℝ} {t : ℝ} {x : M}
    (hft : DifferentiableAt ℝ (fun s => f (s, x)) t)
    (hht : DifferentiableAt ℝ (fun s => h (s, x)) t)
    (hfx : MDifferentiableAt I 𝓘(ℝ) (fun y => f (t, y)) x)
    (hhx : MDifferentiableAt I 𝓘(ℝ) (fun y => h (t, y)) x) :
    w (t, x) * deriv (fun s => f (s, x) + h (s, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y) + h (t, y)) x) =
    (w (t, x) * deriv (fun s => f (s, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y)) x)) +
    (w (t, x) * deriv (fun s => h (s, x)) t +
      A (t, x) (mvfderiv I (fun y => h (t, y)) x)) := by
  rw [deriv_fun_add hft hht, mvfderiv_fun_add hfx hhx, map_add]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.time_spatial_derivative_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.time_spatial_derivative_add target :: scope.openDecls } }

omit [MeasurableSpace M] in
private theorem mvfderiv_const_mul_field (c : ℝ) (f : M → ℝ) (x : M) :
    mvfderiv I (fun y => c * f y) x = c • mvfderiv I f x := by
  by_cases hc : c = 0
  · subst c
    simp only [_root_.MulZeroClass.zero_mul, mvfderiv_const, zero_smul]
  by_cases hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x
  · simpa only [smul_eq_mul, mvfderiv_const, ContinuousLinearMap.zero_smulRight, add_zero] using
      mvfderiv_fun_smul (mdifferentiableAt_const (c := c)) hf
  · have hcf : ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => c * f y) x := by
      intro hcf
      have hback := hcf.const_smul c⁻¹
      apply hf
      have hfun : c⁻¹ • (fun y => c * f y) = f := by
        funext y
        simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      rw [hfun] at hback
      exact hback
    have hfzero : mvfderiv I f x = 0 := by
      simp only [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hf,
        ContinuousLinearMap.comp_zero]
    have hcfzero : mvfderiv I (fun y => c * f y) x = 0 := by
      simp only [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hcf,
        ContinuousLinearMap.comp_zero]
    rw [hcfzero, hfzero, smul_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.mvfderiv_const_mul_field
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.mvfderiv_const_mul_field target :: scope.openDecls } }


omit [MeasurableSpace M] in
private theorem time_spatial_derivative_const_mul
    (w : ℝ × M → ℝ)
    (A : ∀ z : ℝ × M, (TangentSpace I z.2 →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (c : ℝ) (f : ℝ × M → ℝ) (t : ℝ) (x : M) :
    w (t, x) * deriv (fun s => c * f (s, x)) t +
      A (t, x) (mvfderiv I (fun y => c * f (t, y)) x) =
    c * (w (t, x) * deriv (fun s => f (s, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y)) x)) := by
  rw [deriv_const_mul_field, mvfderiv_const_mul_field, map_smul, smul_eq_mul]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.time_spatial_derivative_const_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.time_spatial_derivative_const_mul target :: scope.openDecls } }

theorem integrable_and_integral_integral_time_spatial_derivative_add
    (μ : _root_.MeasureTheory.Measure ℝ) (ν : ℝ → _root_.MeasureTheory.Measure M)
    (w : ℝ × M → ℝ)
    (A : ∀ z : ℝ × M, (TangentSpace I z.2 →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    {f h : ℝ × M → ℝ}
    (hft : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t, DifferentiableAt ℝ (fun s => f (s, x)) t)
    (hht : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t, DifferentiableAt ℝ (fun s => h (s, x)) t)
    (hfx : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t, MDifferentiableAt I 𝓘(ℝ) (fun y => f (t, y)) x)
    (hhx : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t, MDifferentiableAt I 𝓘(ℝ) (fun y => h (t, y)) x)
    (hfint : ∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (fun x => w (t, x) * deriv (fun s => f (s, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y)) x)) (ν t))
    (hhint : ∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (fun x => w (t, x) * deriv (fun s => h (s, x)) t +
      A (t, x) (mvfderiv I (fun y => h (t, y)) x)) (ν t))
    (hftime : _root_.MeasureTheory.Integrable (fun t => ∫ x, w (t, x) * deriv (fun s => f (s, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y)) x) ∂ν t) μ)
    (hhtime : _root_.MeasureTheory.Integrable (fun t => ∫ x, w (t, x) * deriv (fun s => h (s, x)) t +
      A (t, x) (mvfderiv I (fun y => h (t, y)) x) ∂ν t) μ) :
    let R := fun (u : ℝ × M → ℝ) (t : ℝ) (x : M) =>
      w (t, x) * deriv (fun s => u (s, x)) t +
        A (t, x) (mvfderiv I (fun y => u (t, y)) x)
    (∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (R (f + h) t) (ν t)) ∧
      _root_.MeasureTheory.Integrable (fun t => ∫ x, R (f + h) t x ∂ν t) μ ∧
      (∫ t, ∫ x, R (f + h) t x ∂ν t ∂μ) =
        (∫ t, ∫ x, R f t x ∂ν t ∂μ) + ∫ t, ∫ x, R h t x ∂ν t ∂μ := by
  dsimp only
  have heq : ∀ᵐ t ∂μ, (fun x => w (t, x) * deriv (fun s => (f + h) (s, x)) t +
      A (t, x) (mvfderiv I (fun y => (f + h) (t, y)) x)) =ᵐ[ν t]
    (fun x => (w (t, x) * deriv (fun s => f (s, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y)) x)) +
      (w (t, x) * deriv (fun s => h (s, x)) t +
      A (t, x) (mvfderiv I (fun y => h (t, y)) x))) := by
    filter_upwards [hft, hht, hfx, hhx] with t hftt hhtt hfxt hhxt
    filter_upwards [hftt, hhtt, hfxt, hhxt] with x hftx hhtx hfxx hhxx
    exact time_spatial_derivative_add w A hftx hhtx hfxx hhxx
  have hint : ∀ᵐ t ∂μ,
      (∫ x, w (t, x) * deriv (fun s => (f + h) (s, x)) t +
        A (t, x) (mvfderiv I (fun y => (f + h) (t, y)) x) ∂ν t) =
      (∫ x, w (t, x) * deriv (fun s => f (s, x)) t +
        A (t, x) (mvfderiv I (fun y => f (t, y)) x) ∂ν t) +
      ∫ x, w (t, x) * deriv (fun s => h (s, x)) t +
        A (t, x) (mvfderiv I (fun y => h (t, y)) x) ∂ν t := by
    filter_upwards [heq, hfint, hhint] with t ht hfi hhi
    rw [_root_.MeasureTheory.integral_congr_ae ht, _root_.MeasureTheory.integral_add hfi hhi]
  refine ⟨?_, (hftime.add hhtime).congr (Filter.EventuallyEq.symm hint), ?_⟩
  · filter_upwards [heq, hfint, hhint] with t ht hfi hhi
    exact (hfi.add hhi).congr ht.symm
  · rw [_root_.MeasureTheory.integral_congr_ae hint, _root_.MeasureTheory.integral_add hftime hhtime]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.integrable_and_integral_integral_time_spatial_derivative_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.integrable_and_integral_integral_time_spatial_derivative_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.integrable_and_integral_integral_time_spatial_derivative_add ``Submission.DifferentialGeometry.Analysis.Parabolic.integrable_and_integral_integral_time_spatial_derivative_add

theorem integrable_and_integral_integral_time_spatial_derivative_const_mul
    (μ : _root_.MeasureTheory.Measure ℝ) (ν : ℝ → _root_.MeasureTheory.Measure M)
    (w : ℝ × M → ℝ)
    (A : ∀ z : ℝ × M, (TangentSpace I z.2 →L[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (c : ℝ) {f : ℝ × M → ℝ}
    (hfint : ∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (fun x => w (t, x) * deriv (fun s => f (s, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y)) x)) (ν t))
    (hftime : _root_.MeasureTheory.Integrable (fun t => ∫ x, w (t, x) * deriv (fun s => f (s, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y)) x) ∂ν t) μ) :
    let R := fun (u : ℝ × M → ℝ) (t : ℝ) (x : M) =>
      w (t, x) * deriv (fun s => u (s, x)) t +
        A (t, x) (mvfderiv I (fun y => u (t, y)) x)
    (∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (R (c • f) t) (ν t)) ∧
      _root_.MeasureTheory.Integrable (fun t => ∫ x, R (c • f) t x ∂ν t) μ ∧
      (∫ t, ∫ x, R (c • f) t x ∂ν t ∂μ) =
        c * ∫ t, ∫ x, R f t x ∂ν t ∂μ := by
  dsimp only
  have heq : ∀ᵐ t ∂μ, (fun x => w (t, x) * deriv (fun s => (c • f) (s, x)) t +
      A (t, x) (mvfderiv I (fun y => (c • f) (t, y)) x)) =ᵐ[ν t]
    (fun x => c * (w (t, x) * deriv (fun s => f (s, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y)) x))) := by
    exact _root_.MeasureTheory.ae_of_all μ fun t => _root_.MeasureTheory.ae_of_all (ν t) fun x =>
      time_spatial_derivative_const_mul w A c f t x
  have hint : ∀ᵐ t ∂μ,
      (∫ x, w (t, x) * deriv (fun s => (c • f) (s, x)) t +
        A (t, x) (mvfderiv I (fun y => (c • f) (t, y)) x) ∂ν t) =
      c * ∫ x, w (t, x) * deriv (fun s => f (s, x)) t +
        A (t, x) (mvfderiv I (fun y => f (t, y)) x) ∂ν t := by
    filter_upwards [heq] with t ht
    rw [_root_.MeasureTheory.integral_congr_ae ht, _root_.MeasureTheory.integral_const_mul]
  refine ⟨?_, (hftime.const_mul c).congr (Filter.EventuallyEq.symm hint), ?_⟩
  · filter_upwards [heq, hfint] with t ht hfi
    exact (hfi.const_mul c).congr ht.symm
  · rw [_root_.MeasureTheory.integral_congr_ae hint, _root_.MeasureTheory.integral_const_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.integrable_and_integral_integral_time_spatial_derivative_const_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.integrable_and_integral_integral_time_spatial_derivative_const_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.integrable_and_integral_integral_time_spatial_derivative_const_mul ``Submission.DifferentialGeometry.Analysis.Parabolic.integrable_and_integral_integral_time_spatial_derivative_const_mul

end DifferentialGeometry.Analysis.Parabolic
