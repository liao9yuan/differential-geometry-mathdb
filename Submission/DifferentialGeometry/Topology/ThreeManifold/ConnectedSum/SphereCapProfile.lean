import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereUnitFilling
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Topology.SphereUnitFilling

def capWeight (ρ : ℝ) : ℝ := Real.smoothTransition (4 * (ρ - 3 / 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capWeight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capWeight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capWeight ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capWeight

def capDensity (ρ : ℝ) : ℝ :=
  (1 - capWeight ρ) * (2 - ρ)⁻¹ + capWeight ρ * ρ⁻¹

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capDensity ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capDensity

def capRadius (ρ : ℝ) : ℝ := Real.exp (-(∫ s in (1 : ℝ)..ρ, capDensity s))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capRadius ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capRadius

lemma capWeight_of_le {ρ : ℝ} (h : ρ ≤ 3 / 2) : capWeight ρ = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capWeight_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capWeight_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capWeight_of_le ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capWeight_of_le

lemma capWeight_of_le' {ρ : ℝ} (h : 7 / 4 ≤ ρ) : capWeight ρ = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capWeight_of_le' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capWeight_of_le'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capWeight_of_le' ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capWeight_of_le'

lemma capWeight_nonneg (ρ : ℝ) : 0 ≤ capWeight ρ := Real.smoothTransition.nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capWeight_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capWeight_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capWeight_nonneg ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capWeight_nonneg

lemma capWeight_le_one (ρ : ℝ) : capWeight ρ ≤ 1 := Real.smoothTransition.le_one _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capWeight_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capWeight_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capWeight_le_one ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capWeight_le_one

lemma capWeight_lt_one {ρ : ℝ} (h : ρ < 7 / 4) : capWeight ρ < 1 := by
  apply Real.smoothTransition.lt_one_of_lt_one
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capWeight_lt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capWeight_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capWeight_lt_one ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capWeight_lt_one

lemma capWeight_contDiff : ContDiff ℝ ∞ capWeight :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capWeight_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capWeight_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capWeight_contDiff ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capWeight_contDiff

lemma capDensity_of_le {ρ : ℝ} (h : ρ ≤ 3 / 2) : capDensity ρ = (2 - ρ)⁻¹ := by
  rw [capDensity, capWeight_of_le h]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capDensity_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capDensity_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capDensity_of_le ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capDensity_of_le

lemma capDensity_of_le' {ρ : ℝ} (h : 7 / 4 ≤ ρ) : capDensity ρ = ρ⁻¹ := by
  rw [capDensity, capWeight_of_le' h]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capDensity_of_le' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capDensity_of_le'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capDensity_of_le' ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capDensity_of_le'

lemma capDensity_pos' (ρ : ℝ) : 0 < capDensity ρ := by
  rcases lt_or_ge ρ (3 / 2) with h₁ | h₁
  · rw [capDensity_of_le (le_of_lt h₁)]
    exact inv_pos.mpr (by linarith)
  rcases lt_or_ge ρ (7 / 4) with h₂ | h₂
  · have hw : capWeight ρ < 1 := capWeight_lt_one h₂
    have hw0 : 0 ≤ capWeight ρ := capWeight_nonneg ρ
    have h2ρ : 0 < 2 - ρ := by linarith
    have h1' : (1 - capWeight ρ) * (2 - ρ)⁻¹ > 0 := mul_pos (by linarith) (inv_pos.mpr h2ρ)
    have h2' : 0 ≤ capWeight ρ * ρ⁻¹ := mul_nonneg hw0 (inv_nonneg.mpr (by linarith))
    rw [capDensity]
    linarith
  · rw [capDensity_of_le' h₂]
    exact inv_pos.mpr (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capDensity_pos' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capDensity_pos'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capDensity_pos' ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capDensity_pos'

lemma capRadius_one : capRadius 1 = 1 := by
  rw [capRadius, intervalIntegral.integral_same, neg_zero, Real.exp_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capRadius_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capRadius_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capRadius_one ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capRadius_one

lemma capRadius_pos (ρ : ℝ) : 0 < capRadius ρ := by
  rw [capRadius]; exact Real.exp_pos _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capRadius_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capRadius_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capRadius_pos ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capRadius_pos

lemma capRadius_of_le {ρ : ℝ} (h1 : 1 ≤ ρ) (h2 : ρ ≤ 3 / 2) : capRadius ρ = 2 - ρ := by
  have hcongr : (∫ s in (1 : ℝ)..ρ, capDensity s) = ∫ s in (1 : ℝ)..ρ, (2 - s)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ _root_.Set.Icc (1 : ℝ) ρ := by simpa [_root_.Set.uIcc_of_le h1] using hs
    exact capDensity_of_le (by linarith [hs'.2])
  have hderiv : ∀ s ∈ _root_.Set.uIcc (1 : ℝ) ρ,
      HasDerivAt ((-Real.log) ∘ (fun x : ℝ => (2:ℝ) - x)) ((2 - s)⁻¹) s := by
    intro s hs
    have hs' : s ∈ _root_.Set.Icc (1 : ℝ) ρ := by simpa [_root_.Set.uIcc_of_le h1] using hs
    have h0 : (2 - s) ≠ 0 := by linarith [hs'.2]
    have h1' : HasDerivAt (fun x : ℝ => (2:ℝ) - x) (-1) s := (hasDerivAt_id s).const_sub 2
    exact ((Real.hasDerivAt_log h0).comp s h1').neg.congr_deriv (by ring)
  have hint : IntervalIntegrable (fun s : ℝ => (2 - s)⁻¹) _root_.MeasureTheory.MeasureSpace.volume 1 ρ := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · fun_prop
    · intro s hs
      have hs' : s ∈ _root_.Set.Icc (1 : ℝ) ρ := by simpa [_root_.Set.uIcc_of_le h1] using hs
      linarith [hs'.2]
  have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [capRadius, hcongr, hval]
  simp only [Function.comp_apply, Pi.neg_apply]
  have hlog : Real.log (2 - 1) = 0 := by norm_num
  rw [hlog]
  have harg : -(-Real.log (2 - ρ) - -0) = Real.log (2 - ρ) := by ring
  rw [harg, Real.exp_log]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capRadius_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capRadius_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capRadius_of_le ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capRadius_of_le


lemma contDiffOn_capDensity : ContDiffOn ℝ ∞ capDensity (_root_.Set.Ioi 0) := by
  refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
  rcases lt_or_ge x 2 with hx2 | hx2
  · have hxmem : x ∈ _root_.Set.Iio ((x + 2) / 2) := by change x < (x + 2) / 2; linarith
    refine ⟨Iio ((x + 2) / 2), isOpen_Iio, hxmem, ?_⟩
    change ContDiffOn ℝ ∞ (fun y : ℝ => (1 - capWeight y) * (2 - y)⁻¹ + capWeight y * y⁻¹)
      (_root_.Set.Ioi 0 ∩ _root_.Set.Iio ((x + 2) / 2))
    refine ContDiffOn.add ?_ ?_
    · refine ContDiffOn.mul ?_ ?_
      · exact contDiffOn_const.sub capWeight_contDiff.contDiffOn
      · refine ContDiffOn.inv ?_ ?_
        · fun_prop
        · intro y hy
          have hy2 : y < (x + 2) / 2 := hy.2
          linarith
    · refine ContDiffOn.mul capWeight_contDiff.contDiffOn ?_
      refine ContDiffOn.inv ?_ ?_
      · fun_prop
      · intro y hy
        have hy1 : (0 : ℝ) < y := hy.1
        linarith
  · have hxmem : x ∈ _root_.Set.Ioi (7 / 4 : ℝ) := by change (7 : ℝ) / 4 < x; linarith
    refine ⟨Ioi (7 / 4 : ℝ), isOpen_Ioi, hxmem, ?_⟩
    have hcongr : ∀ y ∈ _root_.Set.Ioi (0 : ℝ) ∩ _root_.Set.Ioi (7 / 4 : ℝ), capDensity y = y⁻¹ := fun y hy =>
      capDensity_of_le' (le_of_lt hy.2)
    refine ContDiffOn.congr ?_ hcongr
    exact contDiffOn_id.inv (fun y hy => by
      have hy2 : (7 : ℝ) / 4 < y := hy.2
      have hpos : (0 : ℝ) < y := by linarith
      exact ne_of_gt hpos)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.contDiffOn_capDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.contDiffOn_capDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.contDiffOn_capDensity ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.contDiffOn_capDensity

lemma capRadius_strictAntiOn : StrictAntiOn capRadius (_root_.Set.Ici 1) := by
  intro a ha b hb hab
  have ha' : (1 : ℝ) ≤ a := ha
  have h1 : (0 : ℝ) < ∫ s in a..b, capDensity s := by
    refine intervalIntegral.intervalIntegral_pos_of_pos ?_ capDensity_pos' hab
    refine ContinuousOn.intervalIntegrable ?_
    refine contDiffOn_capDensity.continuousOn.mono ?_
    intro y hy
    have hy' : y ∈ _root_.Set.Icc (_root_.Min.min a b) (_root_.Max.max a b) := hy
    have : (1 : ℝ) ≤ a := ha
    rcases le_total a b with h | h
    · have h2 : a ≤ y := by have := hy'.1; rwa [min_eq_left h] at this
      change (0 : ℝ) < y
      linarith
    · have h2 : y ≤ a := by have := hy'.2; rwa [max_eq_left h] at this
      change (0 : ℝ) < y
      linarith
  have hsplit : (∫ s in (1 : ℝ)..b, capDensity s)
      = (∫ s in (1 : ℝ)..a, capDensity s) + ∫ s in a..b, capDensity s := by
    refine (intervalIntegral.integral_add_adjacent_intervals ?_ ?_).symm
    · exact ContinuousOn.intervalIntegrable (contDiffOn_capDensity.continuousOn.mono (by
        intro y hy
        have hy' : y ∈ _root_.Set.Icc (_root_.Min.min 1 a) (_root_.Max.max 1 a) := hy
        rcases le_total 1 a with h | h
        · have h2 : (1:ℝ) ≤ y := by have := hy'.1; rwa [min_eq_left h] at this
          change (0 : ℝ) < y
          linarith
        · have h2 : a ≤ y := by have := hy'.1; rwa [min_eq_right h] at this
          change (0 : ℝ) < y
          linarith [ha', h2]))
    · exact ContinuousOn.intervalIntegrable (contDiffOn_capDensity.continuousOn.mono (by
        intro y hy
        have hy' : y ∈ _root_.Set.Icc (_root_.Min.min a b) (_root_.Max.max a b) := hy
        have : (1 : ℝ) ≤ a := ha
        rcases le_total a b with h | h
        · have h2 : a ≤ y := by have := hy'.1; rwa [min_eq_left h] at this
          change (0 : ℝ) < y
          linarith
        · have h2 : y ≤ a := by have := hy'.2; rwa [max_eq_left h] at this
          change (0 : ℝ) < y
          linarith))
  have hb_val : capRadius b
      = Real.exp (-((∫ s in (1 : ℝ)..a, capDensity s) + ∫ s in a..b, capDensity s)) := by
    rw [capRadius, hsplit]
  have ha_val : capRadius a = Real.exp (-(∫ s in (1 : ℝ)..a, capDensity s)) := rfl
  rw [hb_val, ha_val]
  refine Real.exp_lt_exp.mpr ?_
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capRadius_strictAntiOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capRadius_strictAntiOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capRadius_strictAntiOn ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capRadius_strictAntiOn

lemma capRadius_le_one {ρ : ℝ} (h : 1 ≤ ρ) : capRadius ρ ≤ 1 := by
  rcases eq_or_lt_of_le h with hρ | hρ
  · rw [← hρ, capRadius_one]
  · simpa only [capRadius_one] using
      (capRadius_strictAntiOn (le_refl (1 : ℝ)) h hρ).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capRadius_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capRadius_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capRadius_le_one ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capRadius_le_one

lemma capRadius_lt_one {ρ : ℝ} (h : 1 < ρ) : capRadius ρ < 1 := by
  have h1 : capRadius ρ < capRadius 1 := capRadius_strictAntiOn (le_refl (1 : ℝ)) (le_of_lt h) h
  rwa [capRadius_one] at h1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capRadius_lt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capRadius_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capRadius_lt_one ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capRadius_lt_one

lemma capRadius_injOn : _root_.Set.InjOn capRadius (_root_.Set.Ici 1) := capRadius_strictAntiOn.injOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereUnitFilling.capRadius_injOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereUnitFilling.capRadius_injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereUnitFilling.capRadius_injOn ``Submission.DifferentialGeometry.Topology.SphereUnitFilling.capRadius_injOn

end DifferentialGeometry.Topology.SphereUnitFilling
