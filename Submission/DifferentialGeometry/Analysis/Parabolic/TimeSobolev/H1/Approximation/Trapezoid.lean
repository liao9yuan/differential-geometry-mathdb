import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Approximation.Tent
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Interval _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1

noncomputable def trapezoid (L r : ℝ) : timeH1 ℝ L :=
  ((L - r) / L) • (tent L r (1 : ℝ) + tent L (L - r) (1 : ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid

theorem trapezoid_toFun_left {L r t : ℝ} (hr : 0 < r) (hL : 2 * r ≤ L)
    (ht : t ∈ _root_.Set.Icc (0 : ℝ) r) :
    (trapezoid L r).toFun t = t / r := by
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith : 0 < 2 * r) hL
  have hrL : r < L := by linarith
  have hrLr : r ≤ L - r := by linarith
  have hLrL : L - r < L := by linarith
  have htL : t ∈ _root_.Set.Icc (0 : ℝ) L := ⟨ht.1, ht.2.trans hrL.le⟩
  have htLr : t ∈ _root_.Set.Icc (0 : ℝ) (L - r) := ⟨ht.1, ht.2.trans hrLr⟩
  rw [trapezoid, toFun_smul _ _ htL, toFun_add _ _ htL,
    tent_toFun_left (1 : ℝ) hrL ht,
    tent_toFun_left (1 : ℝ) hLrL htLr]
  simp only [smul_eq_mul, mul_one]
  field_simp [hLpos.ne', hr.ne', sub_ne_zero.mpr hrL.ne']
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid_toFun_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid_toFun_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid_toFun_left ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid_toFun_left

theorem trapezoid_toFun_mid {L r t : ℝ} (hr : 0 < r)
    (ht : t ∈ _root_.Set.Icc r (L - r)) :
    (trapezoid L r).toFun t = 1 := by
  have hL : 2 * r ≤ L := by linarith [ht.1, ht.2]
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith : 0 < 2 * r) hL
  have hrL : r < L := by linarith
  have hLrpos : 0 < L - r := sub_pos.mpr hrL
  have hLrL : L - r < L := by linarith
  have htL : t ∈ _root_.Set.Icc (0 : ℝ) L :=
    ⟨hr.le.trans ht.1, ht.2.trans hLrL.le⟩
  have htrL : t ∈ _root_.Set.Icc r L := ⟨ht.1, ht.2.trans hLrL.le⟩
  have htLr : t ∈ _root_.Set.Icc (0 : ℝ) (L - r) := ⟨hr.le.trans ht.1, ht.2⟩
  rw [trapezoid, toFun_smul _ _ htL, toFun_add _ _ htL,
    tent_toFun_right (1 : ℝ) hr hrL htrL,
    tent_toFun_left (1 : ℝ) hLrL htLr]
  simp only [smul_eq_mul, mul_one]
  field_simp [hLpos.ne', hLrpos.ne']
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid_toFun_mid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid_toFun_mid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid_toFun_mid ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid_toFun_mid

theorem trapezoid_toFun_right {L r t : ℝ} (hr : 0 < r) (hL : 2 * r ≤ L)
    (ht : t ∈ _root_.Set.Icc (L - r) L) :
    (trapezoid L r).toFun t = (L - t) / r := by
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith : 0 < 2 * r) hL
  have hrL : r < L := by linarith
  have hLrpos : 0 < L - r := sub_pos.mpr hrL
  have hrLr : r ≤ L - r := by linarith
  have htL : t ∈ _root_.Set.Icc (0 : ℝ) L :=
    ⟨hr.le.trans (hrLr.trans ht.1), ht.2⟩
  have htrL : t ∈ _root_.Set.Icc r L := ⟨hrLr.trans ht.1, ht.2⟩
  rw [trapezoid, toFun_smul _ _ htL, toFun_add _ _ htL,
    tent_toFun_right (1 : ℝ) hr hrL htrL,
    tent_toFun_right (1 : ℝ) hLrpos (by linarith) ht]
  simp only [smul_eq_mul, mul_one]
  field_simp [hLpos.ne', hr.ne', hLrpos.ne']
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid_toFun_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid_toFun_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid_toFun_right ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid_toFun_right

private theorem trapezoid_deriv_left {L r : ℝ} (hr : 0 < r) (hL : 2 * r ≤ L) :
    (trapezoid L r).deriv =ᵐ[volume.restrict (_root_.Set.Icc (0 : ℝ) r)]
      fun _ => 1 / r := by
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith : 0 < 2 * r) hL
  have hrL : r < L := by linarith
  have hrLr : r ≤ L - r := by linarith
  have hLrL : L - r < L := by linarith
  have hle : volume.restrict (_root_.Set.Icc (0 : ℝ) r) ≤ timeMeasure L := by
    unfold timeMeasure
    exact Measure.restrict_mono (_root_.Set.Icc_subset_Icc le_rfl hrL.le) le_rfl
  have hleLr : volume.restrict (_root_.Set.Icc (0 : ℝ) r) ≤
      volume.restrict (_root_.Set.Icc (0 : ℝ) (L - r)) :=
    Measure.restrict_mono (_root_.Set.Icc_subset_Icc le_rfl hrLr) le_rfl
  have h₁ := tent_deriv_left (T := L) (c := r) (1 : ℝ) hrL
  have h₂ := tent_deriv_left (T := L) (c := L - r) (1 : ℝ) hLrL
  rw [_root_.MeasureTheory.restrict_Ioo_eq_restrict_Icc] at h₁ h₂
  filter_upwards [
    (Lp.coeFn_smul ((L - r) / L)
      ((tent L r (1 : ℝ)).deriv +
        (tent L (L - r) (1 : ℝ)).deriv)).filter_mono
        (_root_.MeasureTheory.ae_mono hle),
    (Lp.coeFn_add (tent L r (1 : ℝ)).deriv
      (tent L (L - r) (1 : ℝ)).deriv).filter_mono (_root_.MeasureTheory.ae_mono hle),
    h₁, h₂.filter_mono (_root_.MeasureTheory.ae_mono hleLr)] with t hsmul hadd h₁t h₂t
  simp only [trapezoid, deriv_smul, deriv_add]
  rw [hsmul, Pi.smul_apply, hadd, Pi.add_apply, h₁t, h₂t]
  simp only [smul_eq_mul, mul_one]
  field_simp [hLpos.ne', hr.ne', sub_ne_zero.mpr hrL.ne']
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid_deriv_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid_deriv_left target :: scope.openDecls } }

private theorem trapezoid_deriv_mid {L r : ℝ} (hr : 0 < r) (hL : 2 * r ≤ L) :
    (trapezoid L r).deriv =ᵐ[volume.restrict (_root_.Set.Icc r (L - r))]
      fun _ => 0 := by
  have hrL : r < L := by linarith
  have hrLr : r ≤ L - r := by linarith
  have hLrL : L - r < L := by linarith
  have hle : volume.restrict (_root_.Set.Icc r (L - r)) ≤ timeMeasure L := by
    unfold timeMeasure
    exact Measure.restrict_mono
      (_root_.Set.Icc_subset_Icc (by linarith : 0 ≤ r) hLrL.le) le_rfl
  have hleRight : volume.restrict (_root_.Set.Icc r (L - r)) ≤
      volume.restrict (_root_.Set.Icc r L) :=
    Measure.restrict_mono (_root_.Set.Icc_subset_Icc le_rfl hLrL.le) le_rfl
  have hleLeft : volume.restrict (_root_.Set.Icc r (L - r)) ≤
      volume.restrict (_root_.Set.Icc (0 : ℝ) (L - r)) :=
    Measure.restrict_mono (_root_.Set.Icc_subset_Icc hr.le le_rfl) le_rfl
  have h₁ := tent_deriv_right (T := L) (c := r) (1 : ℝ) hr
  have h₂ := tent_deriv_left (T := L) (c := L - r) (1 : ℝ) hLrL
  rw [_root_.MeasureTheory.restrict_Ioo_eq_restrict_Icc] at h₁ h₂
  filter_upwards [
    (Lp.coeFn_smul ((L - r) / L)
      ((tent L r (1 : ℝ)).deriv +
        (tent L (L - r) (1 : ℝ)).deriv)).filter_mono
        (_root_.MeasureTheory.ae_mono hle),
    (Lp.coeFn_add (tent L r (1 : ℝ)).deriv
      (tent L (L - r) (1 : ℝ)).deriv).filter_mono (_root_.MeasureTheory.ae_mono hle),
    h₁.filter_mono (_root_.MeasureTheory.ae_mono hleRight), h₂.filter_mono (_root_.MeasureTheory.ae_mono hleLeft)]
      with t hsmul hadd h₁t h₂t
  simp only [trapezoid, deriv_smul, deriv_add]
  rw [hsmul, Pi.smul_apply, hadd, Pi.add_apply, h₁t, h₂t]
  simp only [smul_eq_mul, mul_one]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid_deriv_mid
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid_deriv_mid target :: scope.openDecls } }

private theorem trapezoid_deriv_right {L r : ℝ} (hr : 0 < r) (hL : 2 * r ≤ L) :
    (trapezoid L r).deriv =ᵐ[volume.restrict (_root_.Set.Icc (L - r) L)]
      fun _ => -(1 / r) := by
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith : 0 < 2 * r) hL
  have hrL : r < L := by linarith
  have hLrpos : 0 < L - r := sub_pos.mpr hrL
  have hrLr : r ≤ L - r := by linarith
  have hle : volume.restrict (_root_.Set.Icc (L - r) L) ≤ timeMeasure L := by
    unfold timeMeasure
    exact Measure.restrict_mono
      (_root_.Set.Icc_subset_Icc (sub_nonneg.mpr hrL.le) le_rfl) le_rfl
  have hleR : volume.restrict (_root_.Set.Icc (L - r) L) ≤
      volume.restrict (_root_.Set.Icc r L) :=
    Measure.restrict_mono (_root_.Set.Icc_subset_Icc hrLr le_rfl) le_rfl
  have h₁ := tent_deriv_right (T := L) (c := r) (1 : ℝ) hr
  have h₂ := tent_deriv_right (T := L) (c := L - r) (1 : ℝ) hLrpos
  rw [_root_.MeasureTheory.restrict_Ioo_eq_restrict_Icc] at h₁ h₂
  filter_upwards [
    (Lp.coeFn_smul ((L - r) / L)
      ((tent L r (1 : ℝ)).deriv +
        (tent L (L - r) (1 : ℝ)).deriv)).filter_mono
        (_root_.MeasureTheory.ae_mono hle),
    (Lp.coeFn_add (tent L r (1 : ℝ)).deriv
      (tent L (L - r) (1 : ℝ)).deriv).filter_mono (_root_.MeasureTheory.ae_mono hle),
    h₁.filter_mono (_root_.MeasureTheory.ae_mono hleR), h₂] with t hsmul hadd h₁t h₂t
  simp only [trapezoid, deriv_smul, deriv_add]
  rw [hsmul, Pi.smul_apply, hadd, Pi.add_apply, h₁t, h₂t]
  simp only [smul_eq_mul, mul_one, sub_sub_cancel]
  field_simp [hLpos.ne', hr.ne', hLrpos.ne']
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid_deriv_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.trapezoid_deriv_right target :: scope.openDecls } }

theorem norm_deriv_trapezoid_sq {L r : ℝ} (hr : 0 < r) (hL : 2 * r ≤ L) :
    ‖(trapezoid L r).deriv‖ ^ 2 = 2 / r := by
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith : 0 < 2 * r) hL
  have hrL : r < L := by linarith
  have hrLr : r ≤ L - r := by linarith
  have hLrL : L - r < L := by linarith
  let F : ℝ → ℝ := fun t => ‖(trapezoid L r).deriv t‖ ^ 2
  have hfull : IntervalIntegrable F _root_.MeasureTheory.MeasureSpace.volume (0 : ℝ) L := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hLpos.le]
    exact (Lp.memLp (trapezoid L r).deriv).integrable_norm_pow (by norm_num)
  have hleftInt : IntervalIntegrable F _root_.MeasureTheory.MeasureSpace.volume (0 : ℝ) r :=
    hfull.mono_set (by
      rw [_root_.Set.uIcc_of_le hr.le, _root_.Set.uIcc_of_le hLpos.le]
      exact _root_.Set.Icc_subset_Icc le_rfl hrL.le)
  have hmidInt : IntervalIntegrable F _root_.MeasureTheory.MeasureSpace.volume r (L - r) :=
    hfull.mono_set (by
      rw [_root_.Set.uIcc_of_le hrLr, _root_.Set.uIcc_of_le hLpos.le]
      exact _root_.Set.Icc_subset_Icc hr.le hLrL.le)
  have hrightInt : IntervalIntegrable F _root_.MeasureTheory.MeasureSpace.volume (L - r) L :=
    hfull.mono_set (by
      rw [_root_.Set.uIcc_of_le hLrL.le, _root_.Set.uIcc_of_le hLpos.le]
      exact _root_.Set.Icc_subset_Icc (sub_nonneg.mpr hrL.le) le_rfl)
  have hzeroMidInt : IntervalIntegrable F _root_.MeasureTheory.MeasureSpace.volume (0 : ℝ) (L - r) :=
    hfull.mono_set (by
      rw [_root_.Set.uIcc_of_le (sub_nonneg.mpr hrL.le), _root_.Set.uIcc_of_le hLpos.le]
      exact _root_.Set.Icc_subset_Icc le_rfl hLrL.le)
  have hleft : (∫ t in (0 : ℝ)..r, F t) = 1 / r := by
    rw [show (∫ t in (0 : ℝ)..r, F t) = ∫ _t in (0 : ℝ)..r, (1 / r) ^ 2 by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [_root_.Set.uIoc_of_le hr.le, _root_.MeasureTheory.restrict_Ioc_eq_restrict_Icc]
      filter_upwards [trapezoid_deriv_left hr hL] with t ht
      dsimp only [F]
      rw [ht, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hr)]
    ]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    field_simp [hr.ne']
  have hmid : (∫ t in r..(L - r), F t) = 0 := by
    rw [show (∫ t in r..(L - r), F t) = ∫ _t in r..(L - r), (0 : ℝ) by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [_root_.Set.uIoc_of_le hrLr, _root_.MeasureTheory.restrict_Ioc_eq_restrict_Icc]
      filter_upwards [trapezoid_deriv_mid hr hL] with t ht
      dsimp only [F]
      rw [ht, norm_zero]
      norm_num]
    simp only [intervalIntegral.integral_const, smul_zero]
  have hright : (∫ t in (L - r)..L, F t) = 1 / r := by
    rw [show (∫ t in (L - r)..L, F t) =
        ∫ _t in (L - r)..L, (1 / r) ^ 2 by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [_root_.Set.uIoc_of_le hLrL.le, _root_.MeasureTheory.restrict_Ioc_eq_restrict_Icc]
      filter_upwards [trapezoid_deriv_right hr hL] with t ht
      dsimp only [F]
      rw [ht, Real.norm_eq_abs, abs_neg, abs_of_pos (one_div_pos.mpr hr)]
    ]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    field_simp [hr.ne']
    ring
  rw [TimeSobolev.norm_sq_eq_integral, _root_.MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hLpos.le]
  dsimp only [F] at hleftInt hmidInt hrightInt hzeroMidInt hleft hmid hright ⊢
  rw [← intervalIntegral.integral_add_adjacent_intervals hzeroMidInt hrightInt,
    ← intervalIntegral.integral_add_adjacent_intervals hleftInt hmidInt,
    hleft, hmid, hright]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_deriv_trapezoid_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_deriv_trapezoid_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_deriv_trapezoid_sq ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_deriv_trapezoid_sq

theorem integral_one_sub_trapezoid_sq {L r : ℝ} (hr : 0 < r) (hL : 2 * r ≤ L) :
    (∫ t in (0 : ℝ)..L, 1 - (trapezoid L r).toFun t ^ 2) = 4 * r / 3 := by
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith : 0 < 2 * r) hL
  have hrL : r < L := by linarith
  have hrLr : r ≤ L - r := by linarith
  have hLrL : L - r < L := by linarith
  let F : ℝ → ℝ := fun t => 1 - (trapezoid L r).toFun t ^ 2
  have hFcont : ContinuousOn F (_root_.Set.Icc (0 : ℝ) L) :=
    continuousOn_const.sub ((trapezoid L r).continuousOn_toFun.pow 2)
  have hleftInt : IntervalIntegrable F _root_.MeasureTheory.MeasureSpace.volume (0 : ℝ) r := by
    apply ContinuousOn.intervalIntegrable
    rw [_root_.Set.uIcc_of_le hr.le]
    exact hFcont.mono (_root_.Set.Icc_subset_Icc le_rfl hrL.le)
  have hmidInt : IntervalIntegrable F _root_.MeasureTheory.MeasureSpace.volume r (L - r) := by
    apply ContinuousOn.intervalIntegrable
    rw [_root_.Set.uIcc_of_le hrLr]
    exact hFcont.mono (_root_.Set.Icc_subset_Icc hr.le hLrL.le)
  have hrightInt : IntervalIntegrable F _root_.MeasureTheory.MeasureSpace.volume (L - r) L := by
    apply ContinuousOn.intervalIntegrable
    rw [_root_.Set.uIcc_of_le hLrL.le]
    exact hFcont.mono (_root_.Set.Icc_subset_Icc (sub_nonneg.mpr hrL.le) le_rfl)
  have hzeroMidInt : IntervalIntegrable F _root_.MeasureTheory.MeasureSpace.volume (0 : ℝ) (L - r) := by
    apply ContinuousOn.intervalIntegrable
    rw [_root_.Set.uIcc_of_le (sub_nonneg.mpr hrL.le)]
    exact hFcont.mono (_root_.Set.Icc_subset_Icc le_rfl hLrL.le)
  have hbase : (∫ t in (0 : ℝ)..r, 1 - (t / r) ^ 2) = 2 * r / 3 := by
    have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) _root_.MeasureTheory.MeasureSpace.volume 0 r :=
      continuous_const.intervalIntegrable 0 r
    have hsq : IntervalIntegrable (fun t : ℝ => r⁻¹ ^ 2 * t ^ 2) _root_.MeasureTheory.MeasureSpace.volume 0 r :=
      ((continuous_const.pow 2).mul (continuous_id.pow 2)).intervalIntegrable 0 r
    rw [show (fun t : ℝ => 1 - (t / r) ^ 2) =
        fun t => 1 - r⁻¹ ^ 2 * t ^ 2 by
      funext t
      simp only [div_eq_mul_inv]
      ring]
    rw [intervalIntegral.integral_sub hone hsq,
      intervalIntegral.integral_const_mul, integral_pow]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    norm_num
    field_simp [hr.ne']
    ring
  have hleft : (∫ t in (0 : ℝ)..r, F t) = 2 * r / 3 := by
    rw [show (∫ t in (0 : ℝ)..r, F t) =
        ∫ t in (0 : ℝ)..r, 1 - (t / r) ^ 2 by
      apply intervalIntegral.integral_congr
      intro t ht
      exact congrArg (fun x : ℝ => 1 - x ^ 2)
        (trapezoid_toFun_left hr hL (by simpa only [_root_.Set.uIcc_of_le hr.le] using ht))]
    exact hbase
  have hmid : (∫ t in r..(L - r), F t) = 0 := by
    rw [show (∫ t in r..(L - r), F t) = ∫ _t in r..(L - r), (0 : ℝ) by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only [F]
      rw [trapezoid_toFun_mid hr (by simpa only [_root_.Set.uIcc_of_le hrLr] using ht)]
      norm_num]
    simp only [intervalIntegral.integral_const, smul_zero]
  have hright : (∫ t in (L - r)..L, F t) = 2 * r / 3 := by
    rw [show (∫ t in (L - r)..L, F t) =
        ∫ t in (L - r)..L, 1 - ((L - t) / r) ^ 2 by
      apply intervalIntegral.integral_congr
      intro t ht
      exact congrArg (fun x : ℝ => 1 - x ^ 2)
        (trapezoid_toFun_right hr hL (by simpa only [_root_.Set.uIcc_of_le hLrL.le] using ht))]
    have hreflect := intervalIntegral.integral_comp_sub_left
      (f := fun t : ℝ => 1 - (t / r) ^ 2)
      (a := L - r) (b := L) L
    simp only [sub_self, sub_sub_cancel] at hreflect
    exact hreflect.trans hbase
  dsimp only [F] at hleftInt hmidInt hrightInt hzeroMidInt ⊢
  rw [← intervalIntegral.integral_add_adjacent_intervals hzeroMidInt hrightInt,
    ← intervalIntegral.integral_add_adjacent_intervals hleftInt hmidInt,
    hleft, hmid, hright]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.integral_one_sub_trapezoid_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.integral_one_sub_trapezoid_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.integral_one_sub_trapezoid_sq ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.integral_one_sub_trapezoid_sq


end DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1
