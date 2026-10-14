import Submission.DifferentialGeometry.Analysis.Integration.Lp.OperatorConvergence
import Submission.DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.Algebra.Order.LiminfLimsup

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

variable {P X : Type*} [MeasurableSpace P] {μ : Measure P}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

open _root_.MeasureTheory in
private theorem norm_bounded_of_tendsto_dual {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (u : ℕ → Y) (v : Y)
    (hu : ∀ F : Y →L[ℝ] ℝ, _root_.Filter.Tendsto (fun n => F (u n)) _root_.Filter.atTop (𝓝 (F v))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n, ‖u n‖ ≤ D := by
  obtain ⟨D, hD⟩ := banach_steinhaus
    (g := fun n => NormedSpace.inclusionInDoubleDual ℝ Y (u n)) fun F => by
      simpa only [NormedSpace.dual_def, _root_.Set.forall_mem_range] using
        (isBounded_iff_forall_norm_le.1
          (Metric.isBounded_range_of_tendsto (fun n => F (u n)) (hu F)))
  have hb (n : ℕ) : ‖u n‖ ≤ D := by
    have hn := hD n
    change ‖NormedSpace.inclusionInDoubleDualLi ℝ (u n)‖ ≤ D at hn
    simpa only [LinearIsometry.norm_map] using hn
  exact ⟨D, (norm_nonneg (u 0)).trans (hb 0), hb⟩

run_cmd do
  let target := ``Submission.MeasureTheory.norm_bounded_of_tendsto_dual
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.norm_bounded_of_tendsto_dual target :: scope.openDecls } }

open _root_.MeasureTheory in
def integralBilinearLpRight (B : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ x y, _root_.MeasureTheory.AEStronglyMeasurable (fun t => B t x y) μ)
    {C : ℝ} (hC : ∀ᵐ t ∂μ, ‖B t‖ ≤ C) (u : _root_.MeasureTheory.Lp X 2 μ) :
    _root_.MeasureTheory.Lp X 2 μ →L[ℝ] ℝ where
  toFun v := ∫ t, B t (u t) (v t) ∂μ
  map_add' v w := by
    rw [← _root_.MeasureTheory.integral_add
      (integrable_bilinear_of_apply_aestronglyMeasurable B hB hC (Lp.memLp u) (Lp.memLp v))
      (integrable_bilinear_of_apply_aestronglyMeasurable B hB hC (Lp.memLp u) (Lp.memLp w))]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [Lp.coeFn_add v w] with t ht
    rw [ht, Pi.add_apply, map_add]
  map_smul' r v := by
    rw [← _root_.MeasureTheory.integral_smul]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [Lp.coeFn_smul r v] with t ht
    simp only [ht, Pi.smul_apply, map_smul, RingHom.id_apply]
  cont := continuous_integral_bilinear_lp_right B hB hC u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integralBilinearLpRight then
    throwError "Refusing to shadow existing declaration MeasureTheory.integralBilinearLpRight"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integralBilinearLpRight ``Submission.MeasureTheory.integralBilinearLpRight

open _root_.MeasureTheory in
theorem tendsto_integral_bilinear_of_weak
    (B : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (B₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ n x y, _root_.MeasureTheory.AEStronglyMeasurable (fun t => B n t x y) μ)
    (hB₀ : ∀ x y, _root_.MeasureTheory.AEStronglyMeasurable (fun t => B₀ t x y) μ)
    (C : ℕ → ℝ) (C₀ : ℝ)
    (hC : ∀ n, ∀ᵐ t ∂μ, ‖B n t‖ ≤ C n)
    (hC₀ : ∀ᵐ t ∂μ, ‖B₀ t‖ ≤ C₀)
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in _root_.Filter.atTop, ∀ᵐ t ∂μ, ‖B n t - B₀ t‖ ≤ δ)
    (u : ℕ → _root_.MeasureTheory.Lp X 2 μ) (u₀ v : _root_.MeasureTheory.Lp X 2 μ)
    (hu : ∀ F : _root_.MeasureTheory.Lp X 2 μ →L[ℝ] ℝ,
      _root_.Filter.Tendsto (fun n => F (u n)) _root_.Filter.atTop (𝓝 (F u₀))) :
    _root_.Filter.Tendsto (fun n => ∫ t, B n t (v t) (u n t) ∂μ) _root_.Filter.atTop
      (𝓝 (∫ t, B₀ t (v t) (u₀ t) ∂μ)) := by
  obtain ⟨D, hD, huD⟩ := norm_bounded_of_tendsto_dual u u₀ hu
  have hfixed := hu (integralBilinearLpRight B₀ hB₀ hC₀ v)
  have herr : _root_.Filter.Tendsto
      (fun n => (∫ t, B n t (v t) (u n t) ∂μ) -
        ∫ t, B₀ t (v t) (u n t) ∂μ) _root_.Filter.atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hden : 0 < ‖v‖ * D + 1 := by positivity
    let δ : ℝ := ε / (‖v‖ * D + 1)
    have hδ : 0 < δ := div_pos hε hden
    filter_upwards [hconv δ hδ] with n hn
    have heq : (∫ t, B n t (v t) (u n t) ∂μ) -
        (∫ t, B₀ t (v t) (u n t) ∂μ) =
        ∫ t, (B n t - B₀ t) (v t) (u n t) ∂μ := by
      rw [← _root_.MeasureTheory.integral_sub
        (integrable_bilinear_of_apply_aestronglyMeasurable (B n) (hB n) (hC n)
          (Lp.memLp v) (Lp.memLp (u n)))
        (integrable_bilinear_of_apply_aestronglyMeasurable B₀ hB₀ hC₀
          (Lp.memLp v) (Lp.memLp (u n)))]
      rfl
    rw [dist_zero_right, heq]
    have hnorm := norm_integral_bilinear_le_lp_norm (fun t => B n t - B₀ t)
      (fun x y => (hB n x y).sub (hB₀ x y)) hδ.le hn v (u n)
    apply hnorm.trans_lt
    calc
      δ * (‖v‖ * ‖u n‖) ≤ δ * (‖v‖ * D) := by gcongr; exact huD n
      _ < ε := by
        dsimp only [δ]
        rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
        nlinarith [mul_nonneg (norm_nonneg v) hD]
  simpa only [integralBilinearLpRight, ContinuousLinearMap.coe_mk',
    LinearMap.coe_mk, AddHom.coe_mk, sub_add_cancel, zero_add] using herr.add hfixed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_integral_bilinear_of_weak then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_integral_bilinear_of_weak"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_integral_bilinear_of_weak ``Submission.MeasureTheory.tendsto_integral_bilinear_of_weak



open _root_.MeasureTheory in
theorem isBoundedUnder_integral_quadratic_of_weak
    (B : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ n x y, _root_.MeasureTheory.AEStronglyMeasurable (fun t => B n t x y) μ)
    {C : ℝ} (hC : ∀ᶠ n in _root_.Filter.atTop, ∀ᵐ t ∂μ, ‖B n t‖ ≤ C)
    (u : ℕ → _root_.MeasureTheory.Lp X 2 μ) (u₀ : _root_.MeasureTheory.Lp X 2 μ)
    (hu : ∀ F : _root_.MeasureTheory.Lp X 2 μ →L[ℝ] ℝ,
      _root_.Filter.Tendsto (fun n => F (u n)) _root_.Filter.atTop (𝓝 (F u₀))) :
    _root_.Filter.IsBoundedUnder (· ≤ ·) _root_.Filter.atTop
      (fun n => ‖∫ t, B n t (u n t) (u n t) ∂μ‖) := by
  obtain ⟨D, hD, huD⟩ := norm_bounded_of_tendsto_dual u u₀ hu
  refine ⟨max 0 C * (D * D), ?_⟩
  change ∀ᶠ n in _root_.Filter.atTop, ‖∫ t, B n t (u n t) (u n t) ∂μ‖ ≤ _
  filter_upwards [hC] with n hn
  have hb : ∀ᵐ t ∂μ, ‖B n t‖ ≤ _root_.Max.max 0 C :=
    hn.mono fun t ht => ht.trans (le_max_right 0 C)
  have hnorm := norm_integral_bilinear_le_lp_norm (B n) (hB n)
    (le_max_left 0 C) hb (u n) (u n)
  apply hnorm.trans
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (huD n) (huD n) (norm_nonneg _) hD) (le_max_left 0 C)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.isBoundedUnder_integral_quadratic_of_weak then
    throwError "Refusing to shadow existing declaration MeasureTheory.isBoundedUnder_integral_quadratic_of_weak"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.isBoundedUnder_integral_quadratic_of_weak ``Submission.MeasureTheory.isBoundedUnder_integral_quadratic_of_weak

open _root_.MeasureTheory in
theorem integral_quadratic_le_liminf_of_weak
    (B : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (B₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ n x y, _root_.MeasureTheory.AEStronglyMeasurable (fun t => B n t x y) μ)
    (hB₀ : ∀ x y, _root_.MeasureTheory.AEStronglyMeasurable (fun t => B₀ t x y) μ)
    (C : ℕ → ℝ) (C₀ : ℝ)
    (hC : ∀ n, ∀ᵐ t ∂μ, ‖B n t‖ ≤ C n)
    (hC₀ : ∀ᵐ t ∂μ, ‖B₀ t‖ ≤ C₀)
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in _root_.Filter.atTop, ∀ᵐ t ∂μ, ‖B n t - B₀ t‖ ≤ δ)
    (hpos : ∀ n, ∀ᵐ t ∂μ, ∀ x, 0 ≤ B n t x x)
    (u : ℕ → _root_.MeasureTheory.Lp X 2 μ) (u₀ : _root_.MeasureTheory.Lp X 2 μ)
    (hu : ∀ F : _root_.MeasureTheory.Lp X 2 μ →L[ℝ] ℝ,
      _root_.Filter.Tendsto (fun n => F (u n)) _root_.Filter.atTop (𝓝 (F u₀))) :
    (∫ t, B₀ t (u₀ t) (u₀ t) ∂μ) ≤
      liminf (fun n => ∫ t, B n t (u n t) (u n t) ∂μ) atTop := by
  let q : ℕ → ℝ := fun n => ∫ t, B n t (u n t) (u n t) ∂μ
  let q₀ : ℝ := ∫ t, B₀ t (u₀ t) (u₀ t) ∂μ
  have hleft := tendsto_integral_bilinear_of_weak B B₀ hB hB₀ C C₀ hC hC₀ hconv u u₀ u₀ hu
  have hright := tendsto_integral_bilinear_of_weak
    (fun n t => (B n t).flip) (fun t => (B₀ t).flip)
    (fun n x y => hB n y x) (fun x y => hB₀ y x) C C₀
    (fun n => (hC n).mono fun t ht => by simpa only [ContinuousLinearMap.opNorm_flip] using ht)
    (hC₀.mono fun t ht => by simpa only [ContinuousLinearMap.opNorm_flip] using ht)
    (fun δ hδ => (hconv δ hδ).mono fun n hn => hn.mono fun t ht => by
      have heq : (B n t).flip - (B₀ t).flip = (B n t - B₀ t).flip := rfl
      simpa only [heq, ContinuousLinearMap.opNorm_flip] using ht)
    u u₀ u₀ hu
  have hfixed := tendsto_integral_bilinear_of_weak B B₀ hB hB₀ C C₀ hC hC₀ hconv
    (fun _ => u₀) u₀ u₀ (fun _ => tendsto_const_nhds)
  let r : ℕ → ℝ := fun n =>
    (∫ t, B n t (u₀ t) (u n t) ∂μ) + (∫ t, B n t (u n t) (u₀ t) ∂μ) -
      ∫ t, B n t (u₀ t) (u₀ t) ∂μ
  have hr : _root_.Filter.Tendsto r _root_.Filter.atTop (𝓝 q₀) := by
    simpa only [ContinuousLinearMap.flip_apply, add_sub_cancel_left] using
      (hleft.add hright).sub hfixed
  have hi (n) (v w : _root_.MeasureTheory.Lp X 2 μ) :=
    integrable_bilinear_of_apply_aestronglyMeasurable (B n) (hB n) (hC n)
      (Lp.memLp v) (Lp.memLp w)
  have hrq (n) : r n ≤ q n := by
    have hn : 0 ≤ ∫ t, B n t ((u n - u₀) t) ((u n - u₀) t) ∂μ :=
      _root_.MeasureTheory.integral_nonneg_of_ae ((hpos n).mono fun t ht => ht _)
    have heq : (∫ t, B n t ((u n - u₀) t) ((u n - u₀) t) ∂μ) = q n - r n := by
      calc
        _ = ∫ t, B n t (u n t) (u n t) - B n t (u₀ t) (u n t) -
            B n t (u n t) (u₀ t) + B n t (u₀ t) (u₀ t) ∂μ := by
          apply _root_.MeasureTheory.integral_congr_ae
          filter_upwards [Lp.coeFn_sub (u n) u₀] with t ht
          simp only [ht, Pi.sub_apply, map_sub, sub_apply]
          ring
        _ = q n - r n := by
          have hab := _root_.MeasureTheory.integral_sub (hi n (u n) (u n)) (hi n u₀ (u n))
          have habc := _root_.MeasureTheory.integral_sub ((hi n (u n) (u n)).sub (hi n u₀ (u n)))
            (hi n (u n) u₀)
          have habcd := _root_.MeasureTheory.integral_add
            (((hi n (u n) (u n)).sub (hi n u₀ (u n))).sub (hi n (u n) u₀))
            (hi n u₀ u₀)
          simp only [Pi.sub_apply] at habc habcd
          rw [habcd, habc, hab]
          dsimp only [q, r]
          ring
    rw [heq] at hn
    linarith
  have hbound : ∀ᶠ n in _root_.Filter.atTop, ∀ᵐ t ∂μ, ‖B n t‖ ≤ 1 + C₀ := by
    filter_upwards [hconv 1 zero_lt_one] with n hn
    filter_upwards [hn, hC₀] with t ht ht₀
    exact (norm_le_norm_sub_add (B n t) (B₀ t)).trans (add_le_add ht ht₀)
  obtain ⟨D, hD⟩ := isBoundedUnder_integral_quadratic_of_weak B hB hbound u u₀ hu
  change ∀ᶠ n in _root_.Filter.atTop, ‖q n‖ ≤ D at hD
  have hqbound : ∀ᶠ n in _root_.Filter.atTop, q n ≤ D :=
    hD.mono fun n hn => (le_abs_self (q n)).trans hn
  have hcob : _root_.Filter.IsCoboundedUnder (· ≥ ·) _root_.Filter.atTop q :=
    _root_.Filter.isCoboundedUnder_ge_of_eventually_le _root_.Filter.atTop hqbound
  apply le_of_forall_lt
  intro a ha
  let b : ℝ := (a + q₀) / 2
  have hab : a < b := by dsimp only [b]; linarith
  have hbq : b < q₀ := by dsimp only [b]; linarith
  have hbv : ∀ᶠ n in _root_.Filter.atTop, b ≤ q n :=
    ((tendsto_order.1 hr).1 b hbq).mono fun n hn => hn.le.trans (hrq n)
  exact hab.trans_le (_root_.Filter.le_liminf_of_le hcob hbv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integral_quadratic_le_liminf_of_weak then
    throwError "Refusing to shadow existing declaration MeasureTheory.integral_quadratic_le_liminf_of_weak"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integral_quadratic_le_liminf_of_weak ``Submission.MeasureTheory.integral_quadratic_le_liminf_of_weak

end MeasureTheory

end

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

variable {P X : Type*} [MeasurableSpace P] {μ : Measure P}
  [NormedAddCommGroup X] [NormedSpace ℝ X]


open _root_.MeasureTheory in
private theorem norm_integral_dual_apply_le
    (W : _root_.MeasureTheory.Lp (X →L[ℝ] ℝ) 2 μ) (u : _root_.MeasureTheory.Lp X 2 μ) :
    ‖∫ t, W t (u t) ∂μ‖ ≤ ‖W‖ * ‖u‖ := by
  let B : (X →L[ℝ] ℝ) →L[ℝ] X →L[ℝ] ℝ := (ContinuousLinearMap.apply ℝ ℝ).flip
  have hB : ‖B‖ ≤ 1 := by
    apply B.opNorm_le_bound zero_le_one
    intro L
    change ‖L‖ ≤ 1 * ‖L‖
    simp only [one_mul, le_refl]
  have h := norm_integral_bilinear_le_lp_norm (fun _ : P => B)
    (fun _ _ => _root_.MeasureTheory.aestronglyMeasurable_const) zero_le_one
    (Eventually.of_forall fun _ => hB) W u
  simpa only [one_mul, B, ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply] using h

run_cmd do
  let target := ``Submission.MeasureTheory.norm_integral_dual_apply_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.norm_integral_dual_apply_le target :: scope.openDecls } }


open _root_.MeasureTheory in
theorem tendsto_integral_bilinear_of_weak_of_ae_tendsto
    (B : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (B₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (B n) μ)
    (C : ℝ)
    (hC : ∀ n, ∀ᵐ t ∂μ, ‖B n t‖ ≤ C)
    (hconv : ∀ᵐ t ∂μ, _root_.Filter.Tendsto (fun n => B n t) _root_.Filter.atTop (𝓝 (B₀ t)))
    (u : ℕ → _root_.MeasureTheory.Lp X 2 μ) (u₀ : _root_.MeasureTheory.Lp X 2 μ) (v : _root_.MeasureTheory.Lp X 2 μ)
    (hu : ∀ F : _root_.MeasureTheory.Lp X 2 μ →L[ℝ] ℝ,
      _root_.Filter.Tendsto (fun n => F (u n)) _root_.Filter.atTop (𝓝 (F u₀))) :
    _root_.Filter.Tendsto (fun n => ∫ t, B n t (v t) (u n t) ∂μ) _root_.Filter.atTop
      (𝓝 (∫ t, B₀ t (v t) (u₀ t) ∂μ)) := by
  let : TopologicalSpace.PseudoMetrizableSpace (X →L[ℝ] X →L[ℝ] ℝ) :=
    @PseudoEMetricSpace.pseudoMetrizableSpace _
      (inferInstance : PseudoEMetricSpace (X →L[ℝ] X →L[ℝ] ℝ))
  have hB₀ : _root_.MeasureTheory.AEStronglyMeasurable B₀ μ :=
    aestronglyMeasurable_of_tendsto_ae _root_.Filter.atTop hB hconv
  have hC₀ : ∀ᵐ t ∂μ, ‖B₀ t‖ ≤ C := by
    filter_upwards [hconv, _root_.MeasureTheory.ae_all_iff.mpr hC] with t ht hb
    have hnorm : _root_.Filter.Tendsto (fun n => ‖B n t‖) _root_.Filter.atTop (𝓝 ‖B₀ t‖) :=
      (continuous_norm.tendsto (B₀ t)).comp ht
    exact le_of_tendsto hnorm (Eventually.of_forall hb)
  obtain ⟨D, _, huD⟩ := norm_bounded_of_tendsto_dual u u₀ hu
  have hBapply (n : ℕ) (x : X) (y : X) :=
    ((hB n).apply_continuousLinearMap x).apply_continuousLinearMap y
  have hB₀apply (x : X) (y : X) :=
    (hB₀.apply_continuousLinearMap x).apply_continuousLinearMap y
  let F : _root_.MeasureTheory.Lp X 2 μ →L[ℝ] ℝ := integralBilinearLpRight B₀ hB₀apply hC₀ v
  have hfixed := hu F
  let f (n : ℕ) (t : P) : X →L[ℝ] ℝ := (B n t - B₀ t) (v t)
  have hf : ∀ n, _root_.MeasureTheory.MemLp (f n) 2 μ := by
    intro n
    apply MemLp.clm_apply_of_ae_norm_le ((hB n).sub hB₀)
      (C := C + C) _ (Lp.memLp v)
    filter_upwards [hC n, hC₀] with t ht ht₀
    exact (norm_sub_le _ _).trans (add_le_add ht ht₀)
  let W (n : ℕ) : _root_.MeasureTheory.Lp (X →L[ℝ] ℝ) 2 μ := (hf n).toLp (f n)
  have hW : _root_.Filter.Tendsto (fun n => ‖W n‖) _root_.Filter.atTop (𝓝 0) := by
    have hnorm := tendsto_eLpNorm_clm_apply_sub_of_ae_tendsto
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) B B₀ hB hC hconv (Lp.memLp v)
    have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hnorm
    simpa only [Function.comp_def, W, Lp.norm_toLp, ENNReal.toReal_zero] using hreal
  have herr : _root_.Filter.Tendsto
      (fun n => (∫ t, B n t (v t) (u n t) ∂μ) -
        ∫ t, B₀ t (v t) (u n t) ∂μ) _root_.Filter.atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) (by simpa using hW.mul_const D)
    have heq : (∫ t, B n t (v t) (u n t) ∂μ) -
        (∫ t, B₀ t (v t) (u n t) ∂μ) = ∫ t, W n t (u n t) ∂μ := by
      rw [← _root_.MeasureTheory.integral_sub
        (integrable_bilinear_of_apply_aestronglyMeasurable (B n) (hBapply n) (hC n)
          (Lp.memLp v) (Lp.memLp (u n)))
        (integrable_bilinear_of_apply_aestronglyMeasurable B₀ hB₀apply hC₀
          (Lp.memLp v) (Lp.memLp (u n)))]
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [(hf n).coeFn_toLp] with t ht
      change _ = ((hf n).toLp (f n)) t (u n t)
      rw [ht]
      rfl
    rw [heq]
    exact (norm_integral_dual_apply_le (W n) (u n)).trans
      (mul_le_mul_of_nonneg_left (huD n) (norm_nonneg _))
  simpa only [F, integralBilinearLpRight, ContinuousLinearMap.coe_mk',
    LinearMap.coe_mk, AddHom.coe_mk,
    sub_add_cancel, zero_add] using herr.add hfixed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_integral_bilinear_of_weak_of_ae_tendsto then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_integral_bilinear_of_weak_of_ae_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_integral_bilinear_of_weak_of_ae_tendsto ``Submission.MeasureTheory.tendsto_integral_bilinear_of_weak_of_ae_tendsto


open _root_.MeasureTheory in
theorem integral_quadratic_le_liminf_of_weak_of_ae_tendsto
    (B : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (B₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (B n) μ)
    (C : ℝ)
    (hC : ∀ n, ∀ᵐ t ∂μ, ‖B n t‖ ≤ C)
    (hconv : ∀ᵐ t ∂μ, _root_.Filter.Tendsto (fun n => B n t) _root_.Filter.atTop (𝓝 (B₀ t)))
    (hpos : ∀ n, ∀ᵐ t ∂μ, ∀ x, 0 ≤ B n t x x)
    (u : ℕ → _root_.MeasureTheory.Lp X 2 μ) (u₀ : _root_.MeasureTheory.Lp X 2 μ)
    (hu : ∀ F : _root_.MeasureTheory.Lp X 2 μ →L[ℝ] ℝ,
      _root_.Filter.Tendsto (fun n => F (u n)) _root_.Filter.atTop (𝓝 (F u₀))) :
    (∫ t, B₀ t (u₀ t) (u₀ t) ∂μ) ≤
      liminf (fun n => ∫ t, B n t (u n t) (u n t) ∂μ) atTop := by
  let q : ℕ → ℝ := fun n => ∫ t, B n t (u n t) (u n t) ∂μ
  let q₀ : ℝ := ∫ t, B₀ t (u₀ t) (u₀ t) ∂μ
  have hBapply (n : ℕ) (x y : X) :
      AEStronglyMeasurable (fun t => B n t x y) μ :=
    ((hB n).apply_continuousLinearMap x).apply_continuousLinearMap y
  have hflip : Continuous (fun A : X →L[ℝ] X →L[ℝ] ℝ => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ X X ℝ).continuous
  have hleft := tendsto_integral_bilinear_of_weak_of_ae_tendsto
    B B₀ hB C hC hconv u u₀ u₀ hu
  have hright := tendsto_integral_bilinear_of_weak_of_ae_tendsto
    (fun n t => (B n t).flip) (fun t => (B₀ t).flip)
    (fun n => hflip.comp_aestronglyMeasurable (hB n))
    C
    (fun n => (hC n).mono fun t ht => by
      simpa only [ContinuousLinearMap.opNorm_flip] using ht)
    (hconv.mono fun t ht => (hflip.tendsto (B₀ t)).comp ht)
    u u₀ u₀ hu
  have hfixed := tendsto_integral_bilinear_of_weak_of_ae_tendsto
    B B₀ hB C hC hconv
    (fun _ => u₀) u₀ u₀ (fun _ => tendsto_const_nhds)
  let r : ℕ → ℝ := fun n =>
    (∫ t, B n t (u₀ t) (u n t) ∂μ) + (∫ t, B n t (u n t) (u₀ t) ∂μ) -
      ∫ t, B n t (u₀ t) (u₀ t) ∂μ
  have hr : _root_.Filter.Tendsto r _root_.Filter.atTop (𝓝 q₀) := by
    simpa only [ContinuousLinearMap.flip_apply, add_sub_cancel_left] using
      (hleft.add hright).sub hfixed
  have hi (n) (v w : _root_.MeasureTheory.Lp X 2 μ) :=
    integrable_bilinear_of_apply_aestronglyMeasurable (B n) (hBapply n) (hC n)
      (Lp.memLp v) (Lp.memLp w)
  have hrq (n) : r n ≤ q n := by
    have hn : 0 ≤ ∫ t, B n t ((u n - u₀) t) ((u n - u₀) t) ∂μ :=
      _root_.MeasureTheory.integral_nonneg_of_ae ((hpos n).mono fun t ht => ht _)
    have heq : (∫ t, B n t ((u n - u₀) t) ((u n - u₀) t) ∂μ) = q n - r n := by
      calc
        _ = ∫ t, B n t (u n t) (u n t) - B n t (u₀ t) (u n t) -
            B n t (u n t) (u₀ t) + B n t (u₀ t) (u₀ t) ∂μ := by
          apply _root_.MeasureTheory.integral_congr_ae
          filter_upwards [Lp.coeFn_sub (u n) u₀] with t ht
          simp only [ht, Pi.sub_apply, map_sub, sub_apply]
          ring
        _ = q n - r n := by
          have hab := _root_.MeasureTheory.integral_sub (hi n (u n) (u n)) (hi n u₀ (u n))
          have habc := _root_.MeasureTheory.integral_sub ((hi n (u n) (u n)).sub (hi n u₀ (u n)))
            (hi n (u n) u₀)
          have habcd := _root_.MeasureTheory.integral_add
            (((hi n (u n) (u n)).sub (hi n u₀ (u n))).sub (hi n (u n) u₀))
            (hi n u₀ u₀)
          simp only [Pi.sub_apply] at habc habcd
          rw [habcd, habc, hab]
          dsimp only [q, r]
          ring
    rw [heq] at hn
    linarith
  obtain ⟨D, hD⟩ := isBoundedUnder_integral_quadratic_of_weak B hBapply
    (Eventually.of_forall hC) u u₀ hu
  change ∀ᶠ n in _root_.Filter.atTop, ‖q n‖ ≤ D at hD
  have hqbound : ∀ᶠ n in _root_.Filter.atTop, q n ≤ D :=
    hD.mono fun n hn => (le_abs_self (q n)).trans hn
  have hcob : _root_.Filter.IsCoboundedUnder (· ≥ ·) _root_.Filter.atTop q :=
    _root_.Filter.isCoboundedUnder_ge_of_eventually_le _root_.Filter.atTop hqbound
  apply le_of_forall_lt
  intro a ha
  let b : ℝ := (a + q₀) / 2
  have hab : a < b := by dsimp only [b]; linarith
  have hbq : b < q₀ := by dsimp only [b]; linarith
  have hbv : ∀ᶠ n in _root_.Filter.atTop, b ≤ q n :=
    ((tendsto_order.1 hr).1 b hbq).mono fun n hn => hn.le.trans (hrq n)
  exact hab.trans_le (_root_.Filter.le_liminf_of_le hcob hbv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integral_quadratic_le_liminf_of_weak_of_ae_tendsto then
    throwError "Refusing to shadow existing declaration MeasureTheory.integral_quadratic_le_liminf_of_weak_of_ae_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integral_quadratic_le_liminf_of_weak_of_ae_tendsto ``Submission.MeasureTheory.integral_quadratic_le_liminf_of_weak_of_ae_tendsto

end MeasureTheory
