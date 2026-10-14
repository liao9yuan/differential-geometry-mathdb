import Submission.DifferentialGeometry.Analysis.Integration.Lp.QuadraticLowerSemicontinuity
import Submission.DifferentialGeometry.Tensor.BilinearForm.PositiveSemidefinite
import Submission.DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Set
open scoped _root_.ENNReal _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

variable {P X : Type*} [MeasurableSpace P] {μ : Measure P}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

open _root_.MeasureTheory in
private theorem integral_quadratic_sub_eq
    (B : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ x y, _root_.MeasureTheory.AEStronglyMeasurable (fun t => B t x y) μ)
    {C : ℝ} (hC : ∀ᵐ t ∂μ, ‖B t‖ ≤ C) (u v : _root_.MeasureTheory.Lp X 2 μ) :
    (∫ t, B t ((u - v) t) ((u - v) t) ∂μ) =
      (∫ t, B t (u t) (u t) ∂μ) -
        (∫ t, B t (v t) (u t) ∂μ) -
        (∫ t, B t (u t) (v t) ∂μ) +
        (∫ t, B t (v t) (v t) ∂μ) := by
  have hi (a b : _root_.MeasureTheory.Lp X 2 μ) :=
    integrable_bilinear_of_apply_aestronglyMeasurable B hB hC (Lp.memLp a) (Lp.memLp b)
  calc
    _ = ∫ t, B t (u t) (u t) - B t (v t) (u t) -
        B t (u t) (v t) + B t (v t) (v t) ∂μ := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [Lp.coeFn_sub u v] with t ht
      simp only [ht, Pi.sub_apply, map_sub, sub_apply]
      ring
    _ = _ := by
      have h₁ := _root_.MeasureTheory.integral_sub (hi u u) (hi v u)
      have h₂ := _root_.MeasureTheory.integral_sub ((hi u u).sub (hi v u)) (hi u v)
      have h₃ := _root_.MeasureTheory.integral_add (((hi u u).sub (hi v u)).sub (hi u v)) (hi v v)
      simp only [Pi.sub_apply] at h₂ h₃
      rw [h₃, h₂, h₁]

run_cmd do
  let target := ``Submission.MeasureTheory.integral_quadratic_sub_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.integral_quadratic_sub_eq target :: scope.openDecls } }

open _root_.MeasureTheory in
theorem tendsto_sum_integral_quadratic_sub_of_weak_of_ae_tendsto
    {ι : Type*} [Fintype ι]
    (B : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (B₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (B n) μ) (C : ℝ)
    (hC : ∀ n, ∀ᵐ t ∂μ, ‖B n t‖ ≤ C)
    (hconv : ∀ᵐ t ∂μ, _root_.Filter.Tendsto (fun n => B n t) _root_.Filter.atTop (𝓝 (B₀ t)))
    (u : ι → ℕ → _root_.MeasureTheory.Lp X 2 μ) (u₀ : ι → _root_.MeasureTheory.Lp X 2 μ)
    (hu : ∀ i (F : _root_.MeasureTheory.Lp X 2 μ →L[ℝ] ℝ),
      _root_.Filter.Tendsto (fun n => F (u i n)) _root_.Filter.atTop (𝓝 (F (u₀ i))))
    (henergy : _root_.Filter.Tendsto (fun n => ∑ i : ι, ∫ t, B n t (u i n t) (u i n t) ∂μ)
      _root_.Filter.atTop (𝓝 (∑ i : ι, ∫ t, B₀ t (u₀ i t) (u₀ i t) ∂μ))) :
    _root_.Filter.Tendsto (fun n => ∑ i : ι, ∫ t,
      B n t ((u i n - u₀ i) t) ((u i n - u₀ i) t) ∂μ)
      atTop (𝓝 0) := by
  classical
  have hflip : Continuous (fun A : X →L[ℝ] X →L[ℝ] ℝ => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ X X ℝ).continuous
  have hleft (i : ι) := tendsto_integral_bilinear_of_weak_of_ae_tendsto
    B B₀ hB C hC hconv (u i) (u₀ i) (u₀ i) (hu i)
  have hright (i : ι) := tendsto_integral_bilinear_of_weak_of_ae_tendsto
    (fun n t => (B n t).flip) (fun t => (B₀ t).flip)
    (fun n => hflip.comp_aestronglyMeasurable (hB n)) C
    (fun n => (hC n).mono fun t ht => by
      simpa only [ContinuousLinearMap.opNorm_flip] using ht)
    (hconv.mono fun t ht => (hflip.tendsto (B₀ t)).comp ht)
    (u i) (u₀ i) (u₀ i) (hu i)
  have hfixed (i : ι) := tendsto_integral_bilinear_of_weak_of_ae_tendsto
    B B₀ hB C hC hconv (fun _ => u₀ i) (u₀ i) (u₀ i)
    (fun _ => tendsto_const_nhds)
  have hL := tendsto_finsetSum Finset.univ fun i _ => hleft i
  have hR := tendsto_finsetSum Finset.univ fun i _ => hright i
  have hF := tendsto_finsetSum Finset.univ fun i _ => hfixed i
  have hlim := ((henergy.sub hL).sub hR).add hF
  have heq (n : ℕ) :
      (∑ i : ι, ∫ t, B n t ((u i n - u₀ i) t) ((u i n - u₀ i) t) ∂μ) =
        (∑ i : ι, ∫ t, B n t (u i n t) (u i n t) ∂μ) -
        (∑ i : ι, ∫ t, B n t (u₀ i t) (u i n t) ∂μ) -
        (∑ i : ι, ∫ t, B n t (u i n t) (u₀ i t) ∂μ) +
        (∑ i : ι, ∫ t, B n t (u₀ i t) (u₀ i t) ∂μ) := by
    simp_rw [integral_quadratic_sub_eq (B n)
      (fun x y => ((hB n).apply_continuousLinearMap x).apply_continuousLinearMap y)
      (hC n)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simpa only [ContinuousLinearMap.flip_apply, ← heq, sub_self, zero_sub, neg_add_cancel] using hlim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_sum_integral_quadratic_sub_of_weak_of_ae_tendsto then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_sum_integral_quadratic_sub_of_weak_of_ae_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_sum_integral_quadratic_sub_of_weak_of_ae_tendsto ``Submission.MeasureTheory.tendsto_sum_integral_quadratic_sub_of_weak_of_ae_tendsto

end MeasureTheory

end

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Topology



namespace DifferentialGeometry.Analysis

private theorem abs_integral_weighted_bilinear_sub_le_energy
    {P V : Type*} [MeasurableSpace P] [AddCommGroup V] [Module ℝ V]
    {μ : _root_.MeasureTheory.Measure P} (B : P → LinearMap.BilinForm ℝ V)
    (hB : ∀ᵐ p ∂μ, LinearMap.IsPosSemidef (B p))
    (x₁ x₂ y₁ y₂ : P → V) (c : P → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ᵐ p ∂μ, |c p| ≤ C)
    (hE : _root_.MeasureTheory.Integrable (fun p => B p (x₁ p) (x₁ p) + B p (x₂ p) (x₂ p)) μ)
    (hR : _root_.MeasureTheory.Integrable (fun p => B p (x₁ p - y₁ p) (x₁ p - y₁ p) +
      B p (x₂ p - y₂ p) (x₂ p - y₂ p)) μ)
    {η : ℝ} (hη : 0 < η) :
    |∫ p, c p * (B p (x₁ p) (x₂ p) - B p (y₁ p) (y₂ p)) ∂μ| ≤
      C * (η * (∫ p, B p (x₁ p) (x₁ p) + B p (x₂ p) (x₂ p) ∂μ) +
        (η⁻¹ + 1) * ∫ p, B p (x₁ p - y₁ p) (x₁ p - y₁ p) +
          B p (x₂ p - y₂ p) (x₂ p - y₂ p) ∂μ) := by
  have hi := ((hE.const_mul η).add (hR.const_mul (η⁻¹ + 1))).const_mul C
  calc
    _ ≤ ∫ p, C * (η * (B p (x₁ p) (x₁ p) + B p (x₂ p) (x₂ p)) +
        (η⁻¹ + 1) * (B p (x₁ p - y₁ p) (x₁ p - y₁ p) +
          B p (x₂ p - y₂ p) (x₂ p - y₂ p))) ∂μ := by
      rw [← Real.norm_eq_abs]
      apply _root_.MeasureTheory.norm_integral_le_of_norm_le hi
      filter_upwards [hB, hc] with p hp hcp
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_right hcp (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left
          (hp.abs_apply_sub_apply_le_energy _ _ _ _ hη) hC)
    _ = _ := by
      rw [_root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_add (hE.const_mul η) (hR.const_mul (η⁻¹ + 1)),
        _root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.abs_integral_weighted_bilinear_sub_le_energy
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.abs_integral_weighted_bilinear_sub_le_energy target :: scope.openDecls } }

private theorem tendsto_zero_of_energy_residual_bound
    {ι : Type*} {l : Filter ι} {S R E : ι → ℝ} {C K : ℝ}
    (hC : 0 ≤ C) (hR : _root_.Filter.Tendsto R l (𝓝 0)) (hE : ∀ᶠ n in l, E n ≤ K)
    (hbound : ∀ η : ℝ, 0 < η →
      ∀ᶠ n in l, |S n| ≤ C * (η * E n + (η⁻¹ + 1) * R n)) :
    Tendsto S l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / (2 * (C + 1) * (|K| + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηsmall : C * η * K < ε / 2 := by
    have hdenom : 0 < 2 * (C + 1) * (|K| + 1) := by positivity
    have hscale : η * (2 * (C + 1) * (|K| + 1)) = ε :=
      div_mul_cancel₀ ε (ne_of_gt hdenom)
    have hdiff : C * K < (C + 1) * (|K| + 1) := by
      have := mul_le_mul_of_nonneg_left (le_abs_self K) hC
      nlinarith [abs_nonneg K]
    nlinarith [mul_lt_mul_of_pos_left hdiff hη]
  have hsmall : _root_.Filter.Tendsto (fun n => C * (η⁻¹ + 1) * R n) l (𝓝 0) := by
    simpa using hR.const_mul (C * (η⁻¹ + 1))
  filter_upwards [hbound η hη, hE, Metric.tendsto_nhds.mp hsmall (ε / 2) (by positivity)]
    with n hn hnE hnR
  rw [Real.dist_eq, sub_zero] at hnR ⊢
  have hmain : C * η * E n ≤ C * η * K :=
    mul_le_mul_of_nonneg_left hnE (mul_nonneg hC (le_of_lt hη))
  have hrest := (abs_lt.mp hnR).2
  nlinarith only [hn, hmain, hηsmall, hrest]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.tendsto_zero_of_energy_residual_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.tendsto_zero_of_energy_residual_bound target :: scope.openDecls } }

private theorem tendsto_integral_weighted_bilinear_sub_of_energy_residual
    {P V ι : Type*} [MeasurableSpace P] [AddCommGroup V] [Module ℝ V]
    {μ : _root_.MeasureTheory.Measure P} {l : Filter ι} (B : ι → P → LinearMap.BilinForm ℝ V)
    (hB : ∀ n, ∀ᵐ p ∂μ, LinearMap.IsPosSemidef (B n p))
    (x₁ x₂ y₁ y₂ : ι → P → V) (c : P → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ᵐ p ∂μ, |c p| ≤ C)
    (hE : ∀ n, _root_.MeasureTheory.Integrable (fun p => B n p (x₁ n p) (x₁ n p) +
      B n p (x₂ n p) (x₂ n p)) μ)
    (hR : ∀ n, _root_.MeasureTheory.Integrable (fun p => B n p (x₁ n p - y₁ n p) (x₁ n p - y₁ n p) +
      B n p (x₂ n p - y₂ n p) (x₂ n p - y₂ n p)) μ)
    (hresidual : _root_.Filter.Tendsto (fun n => ∫ p,
      B n p (x₁ n p - y₁ n p) (x₁ n p - y₁ n p) +
      B n p (x₂ n p - y₂ n p) (x₂ n p - y₂ n p) ∂μ) l (𝓝 0))
    {K : ℝ} (hbound : ∀ᶠ n in l,
      (∫ p, B n p (x₁ n p) (x₁ n p) + B n p (x₂ n p) (x₂ n p) ∂μ) ≤ K) :
    _root_.Filter.Tendsto (fun n => ∫ p, c p * (B n p (x₁ n p) (x₂ n p) -
      B n p (y₁ n p) (y₂ n p)) ∂μ) l (𝓝 0) := by
  apply tendsto_zero_of_energy_residual_bound hC hresidual hbound
  intro η hη
  exact Eventually.of_forall fun n =>
    abs_integral_weighted_bilinear_sub_le_energy (B n) (hB n)
      (x₁ n) (x₂ n) (y₁ n) (y₂ n) c hC hc (hE n) (hR n) hη

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.tendsto_integral_weighted_bilinear_sub_of_energy_residual
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.tendsto_integral_weighted_bilinear_sub_of_energy_residual target :: scope.openDecls } }

theorem tendsto_sub_integral_weighted_bilinear_of_energy_residual
    {P V ι : Type*} [MeasurableSpace P] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {μ : _root_.MeasureTheory.Measure P} {l : Filter ι} (B : ι → P → V →L[ℝ] V →L[ℝ] ℝ)
    (hB : ∀ n, ∀ᵐ p ∂μ, LinearMap.IsPosSemidef (B n p).toBilinForm)
    (hBm : ∀ n v w, _root_.MeasureTheory.AEStronglyMeasurable (fun p => B n p v w) μ)
    {D : ι → ℝ} (hBD : ∀ n, ∀ᵐ p ∂μ, ‖B n p‖ ≤ D n)
    (x₁ x₂ y₁ y₂ : ι → P → V)
    (hx₁ : ∀ n, _root_.MeasureTheory.MemLp (x₁ n) 2 μ) (hx₂ : ∀ n, _root_.MeasureTheory.MemLp (x₂ n) 2 μ)
    (hy₁ : ∀ n, _root_.MeasureTheory.MemLp (y₁ n) 2 μ) (hy₂ : ∀ n, _root_.MeasureTheory.MemLp (y₂ n) 2 μ)
    (c : P → ℝ) (hcm : _root_.MeasureTheory.AEStronglyMeasurable c μ)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ᵐ p ∂μ, |c p| ≤ C)
    (hresidual : _root_.Filter.Tendsto (fun n => ∫ p,
      B n p (x₁ n p - y₁ n p) (x₁ n p - y₁ n p) +
      B n p (x₂ n p - y₂ n p) (x₂ n p - y₂ n p) ∂μ) l (𝓝 0))
    {K : ℝ} (hbound : ∀ᶠ n in l,
      (∫ p, B n p (x₁ n p) (x₁ n p) + B n p (x₂ n p) (x₂ n p) ∂μ) ≤ K) :
    _root_.Filter.Tendsto (fun n => (∫ p, c p * B n p (x₁ n p) (x₂ n p) ∂μ) -
      ∫ p, c p * B n p (y₁ n p) (y₂ n p) ∂μ) l (𝓝 0) := by
  have henergy : ∀ n, _root_.MeasureTheory.Integrable (fun p => B n p (x₁ n p) (x₁ n p) +
      B n p (x₂ n p) (x₂ n p)) μ := by
    intro n
    exact (integrable_bilinear_of_apply_aestronglyMeasurable
      (B n) (hBm n) (hBD n) (hx₁ n) (hx₁ n)).add
        (integrable_bilinear_of_apply_aestronglyMeasurable
          (B n) (hBm n) (hBD n) (hx₂ n) (hx₂ n))
  have hres : ∀ n, _root_.MeasureTheory.Integrable (fun p =>
      B n p (x₁ n p - y₁ n p) (x₁ n p - y₁ n p) +
      B n p (x₂ n p - y₂ n p) (x₂ n p - y₂ n p)) μ := by
    intro n
    exact (integrable_bilinear_of_apply_aestronglyMeasurable
      (B n) (hBm n) (hBD n) ((hx₁ n).sub (hy₁ n)) ((hx₁ n).sub (hy₁ n))).add
        (integrable_bilinear_of_apply_aestronglyMeasurable
          (B n) (hBm n) (hBD n) ((hx₂ n).sub (hy₂ n)) ((hx₂ n).sub (hy₂ n)))
  have ht := tendsto_integral_weighted_bilinear_sub_of_energy_residual
    (fun n p => (B n p).toBilinForm) hB x₁ x₂ y₁ y₂ c hC hc
    henergy hres hresidual hbound
  apply ht.congr'
  apply Eventually.of_forall
  intro n
  have hix := (integrable_bilinear_of_apply_aestronglyMeasurable
    (B n) (hBm n) (hBD n) (hx₁ n) (hx₂ n)).bdd_mul hcm
      (by simpa only [Real.norm_eq_abs] using hc)
  have hiy := (integrable_bilinear_of_apply_aestronglyMeasurable
    (B n) (hBm n) (hBD n) (hy₁ n) (hy₂ n)).bdd_mul hcm
      (by simpa only [Real.norm_eq_abs] using hc)
  change (∫ p, c p * (B n p (x₁ n p) (x₂ n p) - B n p (y₁ n p) (y₂ n p)) ∂μ) = _
  simp_rw [mul_sub]
  exact _root_.MeasureTheory.integral_sub hix hiy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendsto_sub_integral_weighted_bilinear_of_energy_residual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendsto_sub_integral_weighted_bilinear_of_energy_residual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendsto_sub_integral_weighted_bilinear_of_energy_residual ``Submission.DifferentialGeometry.Analysis.tendsto_sub_integral_weighted_bilinear_of_energy_residual

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.ENNReal _root_.NNReal _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

variable {P X : Type*} [MeasurableSpace P] {μ : Measure P}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

open _root_.MeasureTheory in
theorem tendsto_integral_weighted_bilinear_of_weak_of_sum_energy_tendsto
    {ι : Type*} [Fintype ι]
    (B : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (B₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (B n) μ) (C : ℝ)
    (hC : ∀ n, ∀ᵐ t ∂μ, ‖B n t‖ ≤ C)
    (hconv : ∀ᵐ t ∂μ, _root_.Filter.Tendsto (fun n => B n t) _root_.Filter.atTop (𝓝 (B₀ t)))
    (hpos : ∀ n, ∀ᵐ t ∂μ, LinearMap.IsPosSemidef (B n t).toBilinForm)
    (u : ι → ℕ → _root_.MeasureTheory.Lp X 2 μ) (u₀ : ι → _root_.MeasureTheory.Lp X 2 μ)
    (hu : ∀ i (F : _root_.MeasureTheory.Lp X 2 μ →L[ℝ] ℝ),
      _root_.Filter.Tendsto (fun n => F (u i n)) _root_.Filter.atTop (𝓝 (F (u₀ i))))
    (henergy : _root_.Filter.Tendsto (fun n => ∑ i : ι, ∫ t, B n t (u i n t) (u i n t) ∂μ)
      _root_.Filter.atTop (𝓝 (∑ i : ι, ∫ t, B₀ t (u₀ i t) (u₀ i t) ∂μ)))
    (c : P → ℝ) (hcm : _root_.MeasureTheory.AEStronglyMeasurable c μ) {K : ℝ≥0}
    (hc : ∀ᵐ t ∂μ, |c t| ≤ K) (j k : ι) :
    _root_.Filter.Tendsto (fun n => ∫ t, c t * B n t (u j n t) (u k n t) ∂μ) _root_.Filter.atTop
      (𝓝 (∫ t, c t * B₀ t (u₀ j t) (u₀ k t) ∂μ)) := by
  classical
  let E (n : ℕ) := ∑ i : ι, ∫ t, B n t (u i n t) (u i n t) ∂μ
  let R (n : ℕ) := ∑ i : ι, ∫ t,
    B n t ((u i n - u₀ i) t) ((u i n - u₀ i) t) ∂μ
  have hR : _root_.Filter.Tendsto R _root_.Filter.atTop (𝓝 0) :=
    tendsto_sum_integral_quadratic_sub_of_weak_of_ae_tendsto B B₀ hB C hC hconv u u₀ hu henergy
  have hb (n : ℕ) (x y : X) :=
    ((hB n).apply_continuousLinearMap x).apply_continuousLinearMap y
  have hi (n : ℕ) (v w : _root_.MeasureTheory.Lp X 2 μ) :=
    integrable_bilinear_of_apply_aestronglyMeasurable (B n) (hb n) (hC n)
      (Lp.memLp v) (Lp.memLp w)
  have hnonneg (n : ℕ) (v : _root_.MeasureTheory.Lp X 2 μ) : 0 ≤ ∫ t, B n t (v t) (v t) ∂μ :=
    _root_.MeasureTheory.integral_nonneg_of_ae ((hpos n).mono fun t ht => ht.nonneg _)
  have hleE (n : ℕ) (i : ι) : (∫ t, B n t (u i n t) (u i n t) ∂μ) ≤ E n :=
    Finset.single_le_sum (fun i _ => hnonneg n (u i n)) (Finset.mem_univ i)
  have hleR (n : ℕ) (i : ι) :
      (∫ t, B n t ((u i n - u₀ i) t) ((u i n - u₀ i) t) ∂μ) ≤ R n :=
    Finset.single_le_sum (fun i _ => hnonneg n (u i n - u₀ i)) (Finset.mem_univ i)
  let Rp (n : ℕ) := ∫ t,
    B n t (u j n t - u₀ j t) (u j n t - u₀ j t) +
      B n t (u k n t - u₀ k t) (u k n t - u₀ k t) ∂μ
  have hRpEq (n : ℕ) : Rp n =
      (∫ t, B n t ((u j n - u₀ j) t) ((u j n - u₀ j) t) ∂μ) +
        (∫ t, B n t ((u k n - u₀ k) t) ((u k n - u₀ k) t) ∂μ) := by
    rw [← _root_.MeasureTheory.integral_add (hi n (u j n - u₀ j) (u j n - u₀ j))
      (hi n (u k n - u₀ k) (u k n - u₀ k))]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u j n) (u₀ j), Lp.coeFn_sub (u k n) (u₀ k)] with t htj htk
    simp only [htj, htk, Pi.sub_apply]
  have hRp : _root_.Filter.Tendsto Rp _root_.Filter.atTop (𝓝 0) := by
    apply squeeze_zero (fun n => ?_) (fun n => ?_) (by simpa using hR.const_mul 2)
    · rw [hRpEq]
      exact add_nonneg (hnonneg n _) (hnonneg n _)
    · rw [hRpEq]
      linarith [hleR n j, hleR n k]
  have hEbound : ∀ᶠ n in _root_.Filter.atTop, E n ≤
      (∑ i : ι, ∫ t, B₀ t (u₀ i t) (u₀ i t) ∂μ) + 1 := by
    exact (henergy.eventually (gt_mem_nhds (lt_add_one _))).mono fun n hn => hn.le
  have hpairBound : ∀ᶠ n in _root_.Filter.atTop,
      (∫ t, B n t (u j n t) (u j n t) + B n t (u k n t) (u k n t) ∂μ) ≤
        2 * ((∑ i : ι, ∫ t, B₀ t (u₀ i t) (u₀ i t) ∂μ) + 1) := by
    filter_upwards [hEbound] with n hn
    rw [_root_.MeasureTheory.integral_add (hi n (u j n) (u j n)) (hi n (u k n) (u k n))]
    linarith [hleE n j, hleE n k]
  have hdifference := tendsto_sub_integral_weighted_bilinear_of_energy_residual
    B hpos hb hC (fun n t => u j n t) (fun n t => u k n t)
    (fun _ t => u₀ j t) (fun _ t => u₀ k t)
    (fun n => Lp.memLp (u j n)) (fun n => Lp.memLp (u k n))
    (fun _ => Lp.memLp (u₀ j)) (fun _ => Lp.memLp (u₀ k))
    c hcm K.coe_nonneg hc hRp hpairBound
  have hm : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (fun t => c t • B n t) μ :=
    fun n => hcm.smul (hB n)
  have hnorm : ∀ n, ∀ᵐ t ∂μ, ‖c t • B n t‖ ≤ (K : ℝ) * _root_.Max.max 0 C := by
    intro n
    filter_upwards [hc, hC n] with t hct hBt
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hct (hBt.trans (le_max_right 0 C)) (norm_nonneg _) K.coe_nonneg
  have hlim : ∀ᵐ t ∂μ, _root_.Filter.Tendsto (fun n => c t • B n t) _root_.Filter.atTop (𝓝 (c t • B₀ t)) :=
    hconv.mono fun t ht => ht.const_smul (c t)
  have hfixed := tendsto_integral_bilinear_of_weak_of_ae_tendsto
    (fun n t => c t • B n t) (fun t => c t • B₀ t) hm ((K : ℝ) * _root_.Max.max 0 C)
    hnorm hlim (fun _ => u₀ k) (u₀ k) (u₀ j) (fun _ => tendsto_const_nhds)
  simpa only [smul_apply, smul_eq_mul, sub_add_cancel, zero_add] using hdifference.add hfixed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_integral_weighted_bilinear_of_weak_of_sum_energy_tendsto then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_integral_weighted_bilinear_of_weak_of_sum_energy_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_integral_weighted_bilinear_of_weak_of_sum_energy_tendsto ``Submission.MeasureTheory.tendsto_integral_weighted_bilinear_of_weak_of_sum_energy_tendsto

end MeasureTheory

end
