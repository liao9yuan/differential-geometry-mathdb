import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.MetricSpace.Lipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.ComplexConjugate

namespace Complex
open _root_.Complex

open _root_.Complex in
def diskMoebius (a z : ℂ) : ℂ := (z - a) / (1 - conj a * z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.diskMoebius then
    throwError "Refusing to shadow existing declaration Complex.diskMoebius"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.diskMoebius ``Submission.Complex.diskMoebius

open _root_.Complex in
theorem diskMoebius_denominator_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - conj a * z ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have ht : ‖conj a * z‖ < 1 := by
    rw [norm_mul, _root_.Complex.norm_conj]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hz) ha
  rw [← h, _root_.NormOneClass.norm_one] at ht
  exact (lt_irrefl 1) ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.diskMoebius_denominator_ne_zero then
    throwError "Refusing to shadow existing declaration Complex.diskMoebius_denominator_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.diskMoebius_denominator_ne_zero ``Submission.Complex.diskMoebius_denominator_ne_zero

open _root_.Complex in
theorem normSq_diskMoebius_identity (a z : ℂ) :
    _root_.Complex.normSq (1 - conj a * z) - _root_.Complex.normSq (z - a) =
      (1 - _root_.Complex.normSq a) * (1 - _root_.Complex.normSq z) := by
  simp only [_root_.Complex.normSq_apply, _root_.Complex.sub_re, _root_.Complex.sub_im, _root_.Complex.one_re, _root_.Complex.one_im, _root_.Complex.mul_re, _root_.Complex.mul_im, _root_.Complex.conj_re, _root_.Complex.conj_im]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.normSq_diskMoebius_identity then
    throwError "Refusing to shadow existing declaration Complex.normSq_diskMoebius_identity"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.normSq_diskMoebius_identity ``Submission.Complex.normSq_diskMoebius_identity

open _root_.Complex in
theorem norm_diskMoebius_le_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖diskMoebius a z‖ ≤ 1 := by
  have hden := diskMoebius_denominator_ne_zero ha hz
  have ha' : _root_.Complex.normSq a < 1 := by rw [_root_.Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hz' : _root_.Complex.normSq z ≤ 1 := by rw [_root_.Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hi := normSq_diskMoebius_identity a z
  have hn : _root_.Complex.normSq (z - a) ≤ _root_.Complex.normSq (1 - conj a * z) := by nlinarith
  have hsq : _root_.Complex.normSq (diskMoebius a z) ≤ 1 := by
    rw [diskMoebius, _root_.Complex.normSq_div, div_le_one (_root_.Complex.normSq_pos.mpr hden)]
    exact hn
  rw [_root_.Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (diskMoebius a z)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.norm_diskMoebius_le_one then
    throwError "Refusing to shadow existing declaration Complex.norm_diskMoebius_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.norm_diskMoebius_le_one ``Submission.Complex.norm_diskMoebius_le_one

open _root_.Complex in
theorem norm_diskMoebius_lt_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖diskMoebius a z‖ < 1 := by
  have hden := diskMoebius_denominator_ne_zero ha hz.le
  have ha' : _root_.Complex.normSq a < 1 := by rw [_root_.Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hz' : _root_.Complex.normSq z < 1 := by rw [_root_.Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hi := normSq_diskMoebius_identity a z
  have hn : _root_.Complex.normSq (z - a) < _root_.Complex.normSq (1 - conj a * z) := by nlinarith
  have hsq : _root_.Complex.normSq (diskMoebius a z) < 1 := by
    rw [diskMoebius, _root_.Complex.normSq_div, div_lt_one (_root_.Complex.normSq_pos.mpr hden)]
    exact hn
  rw [_root_.Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (diskMoebius a z)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.norm_diskMoebius_lt_one then
    throwError "Refusing to shadow existing declaration Complex.norm_diskMoebius_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.norm_diskMoebius_lt_one ``Submission.Complex.norm_diskMoebius_lt_one

open _root_.Complex in
theorem diskMoebius_denominator_re_pos {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    0 < (1 - conj a * z).re := by
  have hnorm : ‖conj a * z‖ < 1 := by
    rw [norm_mul, _root_.Complex.norm_conj]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hz) ha
  have h := _root_.Complex.re_le_norm (conj a * z)
  simp only [_root_.Complex.sub_re, _root_.Complex.one_re]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.diskMoebius_denominator_re_pos then
    throwError "Refusing to shadow existing declaration Complex.diskMoebius_denominator_re_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.diskMoebius_denominator_re_pos ``Submission.Complex.diskMoebius_denominator_re_pos

open _root_.Complex in
theorem norm_diskMoebius_eq_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    ‖diskMoebius a z‖ = 1 := by
  have hden := diskMoebius_denominator_ne_zero ha hz.le
  have hz' : _root_.Complex.normSq z = 1 := by rw [_root_.Complex.normSq_eq_norm_sq, hz]; norm_num
  have hi := normSq_diskMoebius_identity a z
  rw [hz'] at hi
  have hn : _root_.Complex.normSq (z - a) = _root_.Complex.normSq (1 - conj a * z) := by linarith
  have hsq : _root_.Complex.normSq (diskMoebius a z) = 1 := by
    rw [diskMoebius, _root_.Complex.normSq_div, hn, div_self (ne_of_gt (_root_.Complex.normSq_pos.mpr hden))]
  rw [_root_.Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (diskMoebius a z)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.norm_diskMoebius_eq_one then
    throwError "Refusing to shadow existing declaration Complex.norm_diskMoebius_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.norm_diskMoebius_eq_one ``Submission.Complex.norm_diskMoebius_eq_one

open _root_.Complex in
theorem diskMoebius_eq_mul_conj_div {a z : ℂ} (hz : ‖z‖ = 1) :
    diskMoebius a z = z * conj (1 - conj a * z) / (1 - conj a * z) := by
  unfold diskMoebius
  congr 1
  have hc : z * conj z = 1 := by rw [_root_.Complex.mul_conj, _root_.Complex.normSq_eq_norm_sq, hz]; norm_num
  simp only [map_sub, map_one, map_mul, _root_.Complex.conj_conj]
  calc
    z - a = z - a * (z * conj z) := by rw [hc, mul_one]
    _ = z * (1 - a * conj z) := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.diskMoebius_eq_mul_conj_div then
    throwError "Refusing to shadow existing declaration Complex.diskMoebius_eq_mul_conj_div"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.diskMoebius_eq_mul_conj_div ``Submission.Complex.diskMoebius_eq_mul_conj_div

open _root_.Complex in
theorem diskMoebius_neg_apply {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    diskMoebius (-a) (diskMoebius a z) = z := by
  have hden := diskMoebius_denominator_ne_zero ha hz
  have ha' : ‖-a‖ < 1 := by simpa using ha
  have hinv := diskMoebius_denominator_ne_zero ha' (norm_diskMoebius_le_one ha hz)
  unfold diskMoebius at hinv ⊢
  simp only [map_neg, sub_neg_eq_add, neg_mul] at hinv ⊢
  apply (div_eq_iff hinv).mpr
  have hden' : 1 - z * conj a ≠ 0 := by simpa only [mul_comm] using hden
  field_simp [hden, hden']
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.diskMoebius_neg_apply then
    throwError "Refusing to shadow existing declaration Complex.diskMoebius_neg_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.diskMoebius_neg_apply ``Submission.Complex.diskMoebius_neg_apply

open _root_.Complex in
theorem hasDerivAt_diskMoebius {a z : ℂ} (hz : 1 - conj a * z ≠ 0) :
    HasDerivAt (diskMoebius a) ((1 - _root_.Complex.normSq a) / (1 - conj a * z) ^ 2) z := by
  have hn : HasDerivAt (fun w : ℂ => w - a) 1 z := (hasDerivAt_id z).sub_const a
  have hd : HasDerivAt (fun w : ℂ => 1 - conj a * w) (-conj a) z := by
    convert! (hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_id z).const_mul (conj a)) using 1
    simp
  have h := hn.div hd hz
  convert! h using 1
  rw [← _root_.Complex.mul_conj a]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.hasDerivAt_diskMoebius then
    throwError "Refusing to shadow existing declaration Complex.hasDerivAt_diskMoebius"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.hasDerivAt_diskMoebius ``Submission.Complex.hasDerivAt_diskMoebius

open _root_.Complex in
theorem hasDerivAt_const_mul_diskMoebius (η : ℂ) {a z : ℂ} (hz : 1 - conj a * z ≠ 0) :
    HasDerivAt (fun w => η * diskMoebius a w)
      (η * ((1 - _root_.Complex.normSq a) / (1 - conj a * z) ^ 2)) z :=
  (hasDerivAt_diskMoebius hz).const_mul η

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.hasDerivAt_const_mul_diskMoebius then
    throwError "Refusing to shadow existing declaration Complex.hasDerivAt_const_mul_diskMoebius"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.hasDerivAt_const_mul_diskMoebius ``Submission.Complex.hasDerivAt_const_mul_diskMoebius

open _root_.Complex in
theorem diskMoebius_sub {a z w : ℂ} (hz : 1 - conj a * z ≠ 0) (hw : 1 - conj a * w ≠ 0) :
    diskMoebius a z - diskMoebius a w =
      (1 - _root_.Complex.normSq a) * (z - w) / ((1 - conj a * z) * (1 - conj a * w)) := by
  unfold diskMoebius
  rw [← _root_.Complex.mul_conj a]
  have hz' : 1 - z * conj a ≠ 0 := by simpa only [mul_comm] using hz
  have hw' : 1 - w * conj a ≠ 0 := by simpa only [mul_comm] using hw
  field_simp [hz, hw, hz', hw']
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.diskMoebius_sub then
    throwError "Refusing to shadow existing declaration Complex.diskMoebius_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.diskMoebius_sub ``Submission.Complex.diskMoebius_sub

open _root_.Complex in
theorem one_sub_norm_le_norm_diskMoebius_denominator {a z : ℂ} (hz : ‖z‖ ≤ 1) :
    1 - ‖a‖ ≤ ‖1 - conj a * z‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (conj a * z)
  rw [_root_.NormOneClass.norm_one, norm_mul, _root_.Complex.norm_conj] at h
  have hm := mul_le_of_le_one_right (norm_nonneg a) hz
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.one_sub_norm_le_norm_diskMoebius_denominator then
    throwError "Refusing to shadow existing declaration Complex.one_sub_norm_le_norm_diskMoebius_denominator"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.one_sub_norm_le_norm_diskMoebius_denominator ``Submission.Complex.one_sub_norm_le_norm_diskMoebius_denominator

open _root_.Complex in
theorem dist_diskMoebius_le {a z w : ℂ} (ha : ‖a‖ < 1)
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    dist (diskMoebius a z) (diskMoebius a w) ≤ (1 + ‖a‖) / (1 - ‖a‖) * _root_.Dist.dist z w := by
  have hzden := diskMoebius_denominator_ne_zero ha hz
  have hwden := diskMoebius_denominator_ne_zero ha hw
  have hza := one_sub_norm_le_norm_diskMoebius_denominator (a := a) hz
  have hwa := one_sub_norm_le_norm_diskMoebius_denominator (a := a) hw
  have ha0 := norm_nonneg a
  have hp : 0 < 1 - ‖a‖ := sub_pos.mpr ha
  have hs : 0 ≤ 1 - _root_.Complex.normSq a := by rw [_root_.Complex.normSq_eq_norm_sq]; nlinarith
  rw [dist_eq_norm, diskMoebius_sub hzden hwden, norm_div, norm_mul, norm_mul,
    ← _root_.Complex.ofReal_one, ← _root_.Complex.ofReal_sub, _root_.Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs,
    _root_.Complex.normSq_eq_norm_sq, dist_eq_norm]
  have hd : (1 - ‖a‖)^2 ≤ ‖1 - conj a * z‖ * ‖1 - conj a * w‖ := by
    nlinarith [mul_le_mul hza hwa hp.le (norm_nonneg (1 - conj a * z))]
  calc
    (1 - ‖a‖ ^ 2) * ‖z - w‖ / (‖1 - conj a * z‖ * ‖1 - conj a * w‖) ≤
        (1 - ‖a‖ ^ 2) * ‖z - w‖ / (1 - ‖a‖)^2 :=
      div_le_div_of_nonneg_left (mul_nonneg (by nlinarith) (norm_nonneg _)) (sq_pos_of_pos hp) hd
    _ = (1 + ‖a‖) / (1 - ‖a‖) * ‖z - w‖ := by field_simp; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.dist_diskMoebius_le then
    throwError "Refusing to shadow existing declaration Complex.dist_diskMoebius_le"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.dist_diskMoebius_le ``Submission.Complex.dist_diskMoebius_le

open _root_.Complex in
def diskAutomorphism (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1) :
    Metric.closedBall (0 : ℂ) 1 ≃ₜ Metric.closedBall (0 : ℂ) 1 where
  toFun z := ⟨η * diskMoebius a z, by
    rw [mem_closedBall_zero_iff, norm_mul, hη, one_mul]
    exact norm_diskMoebius_le_one ha (mem_closedBall_zero_iff.mp z.property)⟩
  invFun z := ⟨diskMoebius (-a) (conj η * z), by
    rw [mem_closedBall_zero_iff]
    apply norm_diskMoebius_le_one (by simpa using ha)
    rw [norm_mul, _root_.Complex.norm_conj, hη, one_mul]
    exact mem_closedBall_zero_iff.mp z.property⟩
  left_inv z := by
    apply Subtype.ext
    dsimp
    have hc : conj η * η = 1 := by rw [mul_comm, _root_.Complex.mul_conj, _root_.Complex.normSq_eq_norm_sq, hη]; norm_num
    rw [← mul_assoc, hc, one_mul]
    exact diskMoebius_neg_apply ha (mem_closedBall_zero_iff.mp z.property)
  right_inv z := by
    apply Subtype.ext
    dsimp
    have hnorm : ‖conj η * (z : ℂ)‖ ≤ 1 := by
      rw [norm_mul, _root_.Complex.norm_conj, hη, one_mul]
      exact mem_closedBall_zero_iff.mp z.property
    have hinv := diskMoebius_neg_apply (a := -a) (by simpa using ha) hnorm
    simp only [neg_neg] at hinv
    rw [hinv, ← mul_assoc, _root_.Complex.mul_conj, _root_.Complex.normSq_eq_norm_sq, hη]
    norm_num
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_const.mul
    apply Continuous.div
    · exact continuous_subtype_val.sub continuous_const
    · exact continuous_const.sub (continuous_const.mul continuous_subtype_val)
    · intro z
      exact diskMoebius_denominator_ne_zero ha (mem_closedBall_zero_iff.mp z.property)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.div
    · exact (continuous_const.mul continuous_subtype_val).sub continuous_const
    · exact continuous_const.sub
        (continuous_const.mul (continuous_const.mul continuous_subtype_val))
    · intro z
      apply diskMoebius_denominator_ne_zero (by simpa using ha)
      rw [norm_mul, _root_.Complex.norm_conj, hη, one_mul]
      exact mem_closedBall_zero_iff.mp z.property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.diskAutomorphism then
    throwError "Refusing to shadow existing declaration Complex.diskAutomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.diskAutomorphism ``Submission.Complex.diskAutomorphism

open _root_.Complex in
theorem coe_diskAutomorphism_apply (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1)
    (z : Metric.closedBall (0 : ℂ) 1) :
    (diskAutomorphism a η ha hη z : ℂ) = η * diskMoebius a z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.coe_diskAutomorphism_apply then
    throwError "Refusing to shadow existing declaration Complex.coe_diskAutomorphism_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.coe_diskAutomorphism_apply ``Submission.Complex.coe_diskAutomorphism_apply

open _root_.Complex in
theorem lipschitz_diskAutomorphism (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1) :
    LipschitzWith ⟨(1 + ‖a‖) / (1 - ‖a‖), by positivity⟩ (diskAutomorphism a η ha hη) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  change _root_.Dist.dist (η * diskMoebius a z) (η * diskMoebius a w) ≤ _
  rw [dist_eq_norm, ← mul_sub, norm_mul, hη, one_mul, ← dist_eq_norm]
  exact dist_diskMoebius_le ha (mem_closedBall_zero_iff.mp z.property)
    (mem_closedBall_zero_iff.mp w.property)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.lipschitz_diskAutomorphism then
    throwError "Refusing to shadow existing declaration Complex.lipschitz_diskAutomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.lipschitz_diskAutomorphism ``Submission.Complex.lipschitz_diskAutomorphism

open _root_.Complex in
theorem lipschitz_diskAutomorphism_symm (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1) :
    LipschitzWith ⟨(1 + ‖a‖) / (1 - ‖a‖), by positivity⟩ (diskAutomorphism a η ha hη).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hnorm (v : Metric.closedBall (0 : ℂ) 1) : ‖conj η * (v : ℂ)‖ ≤ 1 := by
    rw [norm_mul, _root_.Complex.norm_conj, hη, one_mul]
    exact mem_closedBall_zero_iff.mp v.property
  have h := dist_diskMoebius_le (a := -a) (by simpa using ha) (hnorm z) (hnorm w)
  change _root_.Dist.dist (diskMoebius (-a) (conj η * (z : ℂ)))
    (diskMoebius (-a) (conj η * (w : ℂ))) ≤ (1 + ‖a‖) / (1 - ‖a‖) * _root_.Dist.dist (z : ℂ) (w : ℂ)
  convert! h using 1
  simp only [norm_neg, dist_eq_norm, ← mul_sub, norm_mul, _root_.Complex.norm_conj, hη, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.lipschitz_diskAutomorphism_symm then
    throwError "Refusing to shadow existing declaration Complex.lipschitz_diskAutomorphism_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.lipschitz_diskAutomorphism_symm ``Submission.Complex.lipschitz_diskAutomorphism_symm

open _root_.Complex in
def diskAutomorphismCircle (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1) : Circle ≃ₜ Circle where
  toFun z := ⟨η * diskMoebius a z, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_mul, hη, one_mul]
    exact norm_diskMoebius_eq_one ha (Circle.norm_coe z)⟩
  invFun z := ⟨diskMoebius (-a) (conj η * z), by
    apply mem_sphere_zero_iff_norm.mpr
    apply norm_diskMoebius_eq_one (by simpa using ha)
    rw [norm_mul, _root_.Complex.norm_conj, hη, Circle.norm_coe, one_mul]⟩
  left_inv z := by
    apply Subtype.ext
    dsimp
    have hc : conj η * η = 1 := by rw [mul_comm, _root_.Complex.mul_conj, _root_.Complex.normSq_eq_norm_sq, hη]; norm_num
    rw [← mul_assoc, hc, one_mul]
    exact diskMoebius_neg_apply ha (Circle.norm_coe z).le
  right_inv z := by
    apply Subtype.ext
    dsimp
    have hn : ‖conj η * (z : ℂ)‖ ≤ 1 := by rw [norm_mul, _root_.Complex.norm_conj, hη, Circle.norm_coe, one_mul]
    have hi := diskMoebius_neg_apply (a := -a) (by simpa using ha) hn
    simp only [neg_neg] at hi
    rw [hi, ← mul_assoc, _root_.Complex.mul_conj, _root_.Complex.normSq_eq_norm_sq, hη]
    norm_num
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_const.mul
    apply Continuous.div
    · exact continuous_subtype_val.sub continuous_const
    · exact continuous_const.sub (continuous_const.mul continuous_subtype_val)
    · intro z
      exact diskMoebius_denominator_ne_zero ha (Circle.norm_coe z).le
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.div
    · exact (continuous_const.mul continuous_subtype_val).sub continuous_const
    · exact continuous_const.sub
        (continuous_const.mul (continuous_const.mul continuous_subtype_val))
    · intro z
      apply diskMoebius_denominator_ne_zero (by simpa using ha)
      rw [norm_mul, _root_.Complex.norm_conj, hη, Circle.norm_coe, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.diskAutomorphismCircle then
    throwError "Refusing to shadow existing declaration Complex.diskAutomorphismCircle"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.diskAutomorphismCircle ``Submission.Complex.diskAutomorphismCircle

open _root_.Complex in
theorem coe_diskAutomorphismCircle_apply (a η : ℂ) (ha : ‖a‖ < 1) (hη : ‖η‖ = 1)
    (z : Circle) : (diskAutomorphismCircle a η ha hη z : ℂ) = η * diskMoebius a z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.coe_diskAutomorphismCircle_apply then
    throwError "Refusing to shadow existing declaration Complex.coe_diskAutomorphismCircle_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.coe_diskAutomorphismCircle_apply ``Submission.Complex.coe_diskAutomorphismCircle_apply

end Complex

end
