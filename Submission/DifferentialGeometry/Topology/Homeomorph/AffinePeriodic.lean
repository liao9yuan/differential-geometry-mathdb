import Submission.DifferentialGeometry.Analysis.Calculus.Periodic.Affine
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Function _root_.Set _root_.Filter
open scoped _root_.Topology _root_.NNReal

namespace DifferentialGeometry.Analysis



theorem exists_homeomorph_affinePeriodic_of_lowerSlope {f : ℝ → ℝ}
    (hc : Continuous f) (hp : ∀ t, f (t + 1) = f t + 1) {τ : ℝ} (hτ : 0 < τ)
    (hl : ∀ x y, x ≤ y → τ * (y - x) ≤ f y - f x) :
    ∃ (F : ℝ ≃ₜ ℝ) (L : ℝ≥0), (∀ x, F x = f x) ∧ LipschitzWith L F.symm := by
  have hs : StrictMono f := by
    intro x y hxy
    have h := hl x y hxy.le
    have hpos : 0 < τ * (y - x) := mul_pos hτ (sub_pos.mpr hxy)
    linarith
  obtain ⟨B, _, hB⟩ := exists_bound_of_continuous_unit_periodic
    (hc.sub continuous_id) (affinePeriodic_sub_id hp)
  have hbounds (x : ℝ) : x - B ≤ f x ∧ f x ≤ x + B := by
    have h := hB x
    change |f x - x| ≤ B at h
    obtain ⟨h₁, h₂⟩ := abs_le.mp h
    constructor <;> linarith
  have htop : _root_.Filter.Tendsto f _root_.Filter.atTop atTop := _root_.Filter.tendsto_atTop_mono (fun x => (hbounds x).1)
    (by simpa only [sub_eq_add_neg, id_eq] using _root_.Filter.tendsto_atTop_add_const_right _root_.Filter.atTop (-B) _root_.Filter.tendsto_id)
  have hbot : _root_.Filter.Tendsto f _root_.Filter.atBot atBot := _root_.Filter.tendsto_atBot_mono (fun x => (hbounds x).2)
    (_root_.Filter.tendsto_atBot_add_const_right _root_.Filter.atBot B _root_.Filter.tendsto_id)
  have hsurj : _root_.Function.Surjective f := hc.surjective htop hbot
  let e : ℝ ≃ ℝ := Equiv.ofBijective f ⟨hs.injective, hsurj⟩
  let L : ℝ≥0 := ⟨τ⁻¹, inv_nonneg.mpr hτ.le⟩
  have hL : LipschitzWith L e.symm := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    wlog hxy : x ≤ y generalizing x y
    · rw [dist_comm (e.symm x) (e.symm y), dist_comm x y]
      exact this y x (le_of_not_ge hxy)
    have hinv : e.symm x ≤ e.symm y := hs.le_iff_le.mp (by
      change e (e.symm x) ≤ e (e.symm y)
      simpa only [e.apply_symm_apply] using hxy)
    have hb := hl (e.symm x) (e.symm y) hinv
    change τ * (e.symm y - e.symm x) ≤ e (e.symm y) - e (e.symm x) at hb
    rw [e.apply_symm_apply, e.apply_symm_apply] at hb
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hinv), neg_sub,
      Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
    change e.symm y - e.symm x ≤ τ⁻¹ * (y - x)
    have h := (le_div_iff₀ hτ).mpr (by simpa only [mul_comm] using hb)
    simpa only [div_eq_mul_inv, mul_comm] using h
  refine ⟨{ toEquiv := e, continuous_toFun := hc, continuous_invFun := hL.continuous }, L,
    fun _ => rfl, hL⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_homeomorph_affinePeriodic_of_lowerSlope then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_homeomorph_affinePeriodic_of_lowerSlope"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_homeomorph_affinePeriodic_of_lowerSlope ``Submission.DifferentialGeometry.Analysis.exists_homeomorph_affinePeriodic_of_lowerSlope

end DifferentialGeometry.Analysis
