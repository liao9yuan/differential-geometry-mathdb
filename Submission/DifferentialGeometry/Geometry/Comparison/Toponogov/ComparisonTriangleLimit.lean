import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngle
import Mathlib.Topology.Order.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open _root_.Filter _root_.Set
open scoped _root_.Topology

theorem tendsto_triangle_side_ratio_one {ι : Type*} {l : Filter ι}
    {a b c : ι → ℝ} (hb : ∀ i, 0 < b i)
    (hlower : ∀ i, |a i - b i| ≤ c i) (hupper : ∀ i, c i ≤ a i + b i)
    (hratio : _root_.Filter.Tendsto (fun i => a i / b i) l (𝓝 0)) :
    Tendsto (fun i => c i / b i) l (𝓝 1) := by
  have hlow : _root_.Filter.Tendsto (fun i => 1 - a i / b i) l (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hratio
  have hupp : _root_.Filter.Tendsto (fun i => 1 + a i / b i) l (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hratio
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp
  · intro i
    have hsub : b i - a i ≤ c i := by
      have habs := neg_le_abs (a i - b i)
      linarith [hlower i]
    calc
      1 - a i / b i = (b i - a i) / b i := by
        rw [sub_div, div_self (hb i).ne']
      _ ≤ c i / b i := (div_le_div_iff_of_pos_right (hb i)).2 hsub
  · intro i
    calc
      c i / b i ≤ (a i + b i) / b i :=
        (div_le_div_iff_of_pos_right (hb i)).2 (hupper i)
      _ = 1 + a i / b i := by
        rw [add_div, div_self (hb i).ne', add_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_triangle_side_ratio_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_triangle_side_ratio_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_triangle_side_ratio_one ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_triangle_side_ratio_one

theorem comparison_cosine_quotient_eq {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hlower : |a - b| ≤ c) (hupper : c ≤ a + b) :
    (a ^ 2 + c ^ 2 - b ^ 2) / (2 * a * c) =
      (a / b - Real.cos (comparisonAngle a b c)) / (c / b) := by
  rw [cos_comparisonAngle ha hb hlower hupper]
  field_simp [ha.ne', hb.ne', hc.ne']
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.comparison_cosine_quotient_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.comparison_cosine_quotient_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.comparison_cosine_quotient_eq ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.comparison_cosine_quotient_eq

theorem tendsto_comparisonAngle_pi_of_tendsto_zero {ι : Type*} {l : Filter ι}
    {a b c : ι → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hlower : ∀ i, |a i - b i| ≤ c i)
    (hupper : ∀ i, c i ≤ a i + b i)
    (hratio : _root_.Filter.Tendsto (fun i => a i / b i) l (𝓝 0))
    (hangle : _root_.Filter.Tendsto (fun i => comparisonAngle (a i) (b i) (c i)) l (𝓝 0)) :
    Tendsto (fun i => comparisonAngle (a i) (c i) (b i)) l (𝓝 Real.pi) := by
  have hw := tendsto_triangle_side_ratio_one hb hlower hupper hratio
  have hcos : _root_.Filter.Tendsto (fun i => Real.cos (comparisonAngle (a i) (b i) (c i)))
      l (𝓝 1) := by
    simpa only [Real.cos_zero, Function.comp_def] using
      Real.continuous_cos.continuousAt.tendsto.comp hangle
  have hquot : _root_.Filter.Tendsto
      (fun i => (a i / b i - Real.cos (comparisonAngle (a i) (b i) (c i))) /
        (c i / b i)) l (𝓝 (-1)) := by
    have h := (hratio.sub hcos).div hw (by norm_num)
    change _root_.Filter.Tendsto (fun i => (a i / b i - Real.cos (comparisonAngle (a i) (b i) (c i))) /
      (c i / b i)) l (𝓝 ((0 - 1) / 1)) at h
    simpa only [zero_sub, div_one] using h
  have harccos := Real.continuous_arccos.continuousAt.tendsto.comp hquot
  have hid (i : ι) : comparisonAngle (a i) (c i) (b i) =
      Real.arccos ((a i / b i - Real.cos (comparisonAngle (a i) (b i) (c i))) /
        (c i / b i)) := by
    rw [comparisonAngle,
      comparison_cosine_quotient_eq (ha i) (hb i) (hc i) (hlower i) (hupper i)]
  simpa only [Real.arccos_neg_one, hid, Function.comp_def] using harccos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_comparisonAngle_pi_of_tendsto_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_comparisonAngle_pi_of_tendsto_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_comparisonAngle_pi_of_tendsto_zero ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_comparisonAngle_pi_of_tendsto_zero

theorem comparisonAngle_quadratic_side_loss {A B C : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hlower : |A - B| ≤ C) (hupper : C ≤ A + B)
    (hangle : comparisonAngle A B C ≤ Real.pi / 3) :
    C ^ 2 ≤ A ^ 2 + B ^ 2 - A * B := by
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (comparisonAngle_mem_Icc A B C).1 (by linarith [Real.pi_pos]) hangle
  rw [Real.cos_pi_div_three, cos_comparisonAngle hA hB hlower hupper] at hcos
  have hden : 0 < 2 * A * B := by positivity
  have hquot := (le_div_iff₀ hden).mp hcos
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_quadratic_side_loss then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_quadratic_side_loss"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_quadratic_side_loss ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_quadratic_side_loss

theorem comparisonAngle_linear_side_loss {A B C : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hlower : |A - B| ≤ C) (hupper : C ≤ A + B)
    (hangle : comparisonAngle A B C ≤ Real.pi / 3) (hlarge : 2 * B ≤ A) :
    C ≤ A - B / 4 := by
  have hquad := comparisonAngle_quadratic_side_loss hA hB hlower hupper hangle
  have hC : 0 ≤ C := (abs_nonneg _).trans hlower
  have hright : 0 ≤ A - B / 4 := by linarith
  have hmul := mul_nonneg (sub_nonneg.mpr hlarge) hB.le
  have hsq : C ^ 2 ≤ (A - B / 4) ^ 2 := by nlinarith
  exact (sq_le_sq₀ hC hright).mp hsq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_linear_side_loss then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_linear_side_loss"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_linear_side_loss ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_linear_side_loss

end DifferentialGeometry.Geometry.Comparison.Toponogov
