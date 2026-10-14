import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set

namespace Metric

variable {Y : Type*} [PseudoMetricSpace Y]

def coneDistance (x y : ℝ × Y) : ℝ :=
  Real.sqrt (x.1 ^ 2 + y.1 ^ 2 - 2 * x.1 * y.1 * Real.cos (_root_.Min.min Real.pi (_root_.Dist.dist x.2 y.2)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Metric.coneDistance then
    throwError "Refusing to shadow existing declaration Metric.coneDistance"
  Lean.modifyEnv fun env => Lean.addAlias env `Metric.coneDistance ``Submission.Metric.coneDistance

theorem coneDistance_nonneg (x y : ℝ × Y) : 0 ≤ coneDistance x y := Real.sqrt_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Metric.coneDistance_nonneg then
    throwError "Refusing to shadow existing declaration Metric.coneDistance_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `Metric.coneDistance_nonneg ``Submission.Metric.coneDistance_nonneg

theorem coneDistance_comm (x y : ℝ × Y) : coneDistance x y = coneDistance y x := by
  unfold coneDistance
  rw [dist_comm y.2 x.2]
  congr 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Metric.coneDistance_comm then
    throwError "Refusing to shadow existing declaration Metric.coneDistance_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `Metric.coneDistance_comm ``Submission.Metric.coneDistance_comm

theorem coneDistance_same_direction (r s : ℝ) (u : Y) :
    coneDistance (r, u) (s, u) = |r - s| := by
  unfold coneDistance
  simp only [dist_self, min_eq_right Real.pi_pos.le, Real.cos_zero, mul_one]
  rw [show r ^ 2 + s ^ 2 - 2 * r * s = (r - s) ^ 2 by ring, Real.sqrt_sq_eq_abs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Metric.coneDistance_same_direction then
    throwError "Refusing to shadow existing declaration Metric.coneDistance_same_direction"
  Lean.modifyEnv fun env => Lean.addAlias env `Metric.coneDistance_same_direction ``Submission.Metric.coneDistance_same_direction

theorem coneDistance_le_abs_sub_add_mul_dist {x y : ℝ × Y} {B : ℝ}
    (hx : x.1 ∈ _root_.Set.Icc 0 B) (hy : y.1 ∈ _root_.Set.Icc 0 B) :
    coneDistance x y ≤ |x.1 - y.1| + B * _root_.Dist.dist x.2 y.2 := by
  have hB : 0 ≤ B := hx.1.trans hx.2
  have htheta : 0 ≤ _root_.Min.min Real.pi (_root_.Dist.dist x.2 y.2) := le_min Real.pi_pos.le dist_nonneg
  have hthetaSq := pow_le_pow_left₀ htheta (min_le_right Real.pi (_root_.Dist.dist x.2 y.2)) 2
  have hcos := Real.one_sub_sq_div_two_le_cos (x := _root_.Min.min Real.pi (_root_.Dist.dist x.2 y.2))
  have hcosBound : 1 - _root_.Dist.dist x.2 y.2 ^ 2 / 2 ≤ Real.cos (_root_.Min.min Real.pi (_root_.Dist.dist x.2 y.2)) := by
    linarith only [hthetaSq, hcos]
  have hab := mul_nonneg hx.1 hy.1
  have habB : x.1 * y.1 ≤ B ^ 2 := by
    simpa only [pow_two] using mul_le_mul hx.2 hy.2 hy.1 hB
  have hmul := mul_le_mul_of_nonneg_left hcosBound (show 0 ≤ 2 * x.1 * y.1 by nlinarith only [hab])
  have hbd := mul_le_mul_of_nonneg_right habB (sq_nonneg (_root_.Dist.dist x.2 y.2))
  unfold coneDistance
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have hc := mul_nonneg (abs_nonneg (x.1 - y.1)) (mul_nonneg hB (dist_nonneg (x := x.2) (y := y.2)))
  nlinarith only [hmul, hbd, hc, sq_abs (x.1 - y.1)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Metric.coneDistance_le_abs_sub_add_mul_dist then
    throwError "Refusing to shadow existing declaration Metric.coneDistance_le_abs_sub_add_mul_dist"
  Lean.modifyEnv fun env => Lean.addAlias env `Metric.coneDistance_le_abs_sub_add_mul_dist ``Submission.Metric.coneDistance_le_abs_sub_add_mul_dist

theorem coneDistance_sq {x y : ℝ × Y} (hx : 0 ≤ x.1) (hy : 0 ≤ y.1) :
    coneDistance x y ^ 2 =
      x.1 ^ 2 + y.1 ^ 2 - 2 * x.1 * y.1 * Real.cos (_root_.Min.min Real.pi (_root_.Dist.dist x.2 y.2)) := by
  apply Real.sq_sqrt
  have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one (_root_.Min.min Real.pi (_root_.Dist.dist x.2 y.2)))
    (show 0 ≤ 2 * x.1 * y.1 by positivity)
  nlinarith only [hh, sq_nonneg (x.1 - y.1)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Metric.coneDistance_sq then
    throwError "Refusing to shadow existing declaration Metric.coneDistance_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `Metric.coneDistance_sq ``Submission.Metric.coneDistance_sq

theorem coneDistance_recover_radius_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ≠ b) (u : Y) {x : ℝ × Y} (hx : 0 ≤ x.1) :
    x.1 ^ 2 = a * b +
      (b * coneDistance (a, u) x ^ 2 - a * coneDistance (b, u) x ^ 2) / (b - a) := by
  rw [coneDistance_sq ha hx, coneDistance_sq hb hx]
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  field_simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Metric.coneDistance_recover_radius_sq then
    throwError "Refusing to shadow existing declaration Metric.coneDistance_recover_radius_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `Metric.coneDistance_recover_radius_sq ``Submission.Metric.coneDistance_recover_radius_sq

theorem continuous_coneDistance {Y : Type*} [PseudoMetricSpace Y] :
    Continuous (fun p : (ℝ × Y) × (ℝ × Y) => coneDistance p.1 p.2) := by
  unfold coneDistance
  fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Metric.continuous_coneDistance then
    throwError "Refusing to shadow existing declaration Metric.continuous_coneDistance"
  Lean.modifyEnv fun env => Lean.addAlias env `Metric.continuous_coneDistance ``Submission.Metric.continuous_coneDistance


theorem coneDistance_self {Y : Type*} [PseudoMetricSpace Y] (x : ℝ × Y) :
    coneDistance x x = 0 := by
  unfold coneDistance
  simp only [dist_self, min_eq_right Real.pi_pos.le, Real.cos_zero, mul_one]
  rw [show x.1 ^ 2 + x.1 ^ 2 - 2 * x.1 * x.1 = 0 by ring, Real.sqrt_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Metric.coneDistance_self then
    throwError "Refusing to shadow existing declaration Metric.coneDistance_self"
  Lean.modifyEnv fun env => Lean.addAlias env `Metric.coneDistance_self ``Submission.Metric.coneDistance_self

theorem coneDistance_eq_zero_iff {Y : Type*} [MetricSpace Y] {x y : ℝ × Y}
    (hx : 0 < x.1) (hy : 0 < y.1) : coneDistance x y = 0 ↔ x = y := by
  refine ⟨fun hzero => ?_, fun h => h ▸ coneDistance_self x⟩
  have hsq := coneDistance_sq hx.le hy.le
  rw [hzero, zero_pow (by decide)] at hsq
  have hcos := Real.cos_le_one (_root_.Min.min Real.pi (_root_.Dist.dist x.2 y.2))
  have hnonneg := mul_nonneg (show 0 ≤ 2 * x.1 * y.1 by positivity) (sub_nonneg.mpr hcos)
  have heq : x.1 = y.1 := by nlinarith only [hsq, hnonneg, sq_nonneg (x.1 - y.1)]
  have hangle : Real.cos (_root_.Min.min Real.pi (_root_.Dist.dist x.2 y.2)) = 1 := by
    have hprod : 0 < 2 * x.1 * y.1 := by positivity
    have hz : (2 * x.1 * y.1) *
        (1 - Real.cos (_root_.Min.min Real.pi (_root_.Dist.dist x.2 y.2))) = 0 := by nlinarith only [hsq, heq]
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hprod.ne')).symm
  have ht : _root_.Min.min Real.pi (_root_.Dist.dist x.2 y.2) = 0 :=
    (Real.cos_eq_one_iff_of_lt_of_lt
      (by linarith [le_min Real.pi_pos.le (dist_nonneg (x := x.2) (y := y.2)), Real.pi_pos])
      (by linarith [min_le_left Real.pi (_root_.Dist.dist x.2 y.2), Real.pi_pos])).mp hangle
  have hd : _root_.Dist.dist x.2 y.2 = 0 := by
    rcases min_cases Real.pi (_root_.Dist.dist x.2 y.2) with h | h
    · rw [h.1] at ht
      exact False.elim (Real.pi_pos.ne' ht)
    · rwa [h.1] at ht
  exact Prod.ext heq (dist_eq_zero.mp hd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Metric.coneDistance_eq_zero_iff then
    throwError "Refusing to shadow existing declaration Metric.coneDistance_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Metric.coneDistance_eq_zero_iff ``Submission.Metric.coneDistance_eq_zero_iff

theorem abs_radius_sub_le_coneDistance {Y : Type*} [PseudoMetricSpace Y]
    {x y : ℝ × Y} (hx : 0 ≤ x.1) (hy : 0 ≤ y.1) :
    |x.1 - y.1| ≤ Metric.coneDistance x y := by
  have hs := Metric.coneDistance_sq hx hy
  have hc := mul_le_mul_of_nonneg_left (Real.cos_le_one (_root_.Min.min Real.pi (_root_.Dist.dist x.2 y.2)))
    (show 0 ≤ 2 * x.1 * y.1 by positivity)
  have hn := Metric.coneDistance_nonneg x y
  nlinarith only [hs, hc, hn, sq_abs (x.1 - y.1), abs_nonneg (x.1 - y.1)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Metric.abs_radius_sub_le_coneDistance then
    throwError "Refusing to shadow existing declaration Metric.abs_radius_sub_le_coneDistance"
  Lean.modifyEnv fun env => Lean.addAlias env `Metric.abs_radius_sub_le_coneDistance ``Submission.Metric.abs_radius_sub_le_coneDistance

theorem coneDistance_radial_mul {Y : Type*} [PseudoMetricSpace Y]
    (c : ℝ) (x y : ℝ × Y) :
    coneDistance (c * x.1, x.2) (c * y.1, y.2) = |c| * coneDistance x y := by
  unfold coneDistance
  rw [show (c * x.1) ^ 2 + (c * y.1) ^ 2 -
      2 * (c * x.1) * (c * y.1) * Real.cos (_root_.Min.min Real.pi (_root_.Dist.dist x.2 y.2)) =
      c ^ 2 * (x.1 ^ 2 + y.1 ^ 2 - 2 * x.1 * y.1 * Real.cos (_root_.Min.min Real.pi (_root_.Dist.dist x.2 y.2))) by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Metric.coneDistance_radial_mul then
    throwError "Refusing to shadow existing declaration Metric.coneDistance_radial_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `Metric.coneDistance_radial_mul ``Submission.Metric.coneDistance_radial_mul

end Metric
