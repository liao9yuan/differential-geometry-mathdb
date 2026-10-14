import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open _root_.Filter _root_.Set
open scoped _root_.Topology

noncomputable def comparisonAngle (a b c : ℝ) : ℝ :=
  Real.arccos ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle


noncomputable def metricComparisonAngle {X : Type*} [MetricSpace X] (x o y : X) : ℝ :=
  comparisonAngle (_root_.Dist.dist o x) (_root_.Dist.dist o y) (_root_.Dist.dist x y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.metricComparisonAngle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.metricComparisonAngle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.metricComparisonAngle ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.metricComparisonAngle


theorem comparisonAngle_mem_Icc (a b c : ℝ) : comparisonAngle a b c ∈ _root_.Set.Icc 0 Real.pi :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_mem_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_mem_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_mem_Icc ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_mem_Icc


theorem comparison_cosine_mem_Icc {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlower : |a - b| ≤ c) (hupper : c ≤ a + b) :
    (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) ∈ _root_.Set.Icc (-1) 1 := by
  have hc : 0 ≤ c := (abs_nonneg _).trans hlower
  have hcu := mul_self_le_mul_self hc hupper
  have hcl := mul_self_le_mul_self (abs_nonneg (a - b)) hlower
  have hden : 0 < 2 * a * b := by positivity
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith
  · rw [div_le_iff₀ hden]
    nlinarith [sq_abs (a - b)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.comparison_cosine_mem_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.comparison_cosine_mem_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.comparison_cosine_mem_Icc ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.comparison_cosine_mem_Icc


theorem cos_comparisonAngle {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlower : |a - b| ≤ c) (hupper : c ≤ a + b) :
    Real.cos (comparisonAngle a b c) = (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) :=
  Real.cos_arccos (comparison_cosine_mem_Icc ha hb hlower hupper).1
    (comparison_cosine_mem_Icc ha hb hlower hupper).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.cos_comparisonAngle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.cos_comparisonAngle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.cos_comparisonAngle ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.cos_comparisonAngle

theorem comparisonAngle_scale (a b c : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    comparisonAngle (lam * a) (lam * b) (lam * c) = comparisonAngle a b c := by
  unfold comparisonAngle
  congr 1
  have hnum : (lam * a) ^ 2 + (lam * b) ^ 2 - (lam * c) ^ 2 =
      lam ^ 2 * (a ^ 2 + b ^ 2 - c ^ 2) := by ring
  have hden : 2 * (lam * a) * (lam * b) = lam ^ 2 * (2 * a * b) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero 2 hlam.ne')]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_scale ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_scale


theorem comparisonAngle_comm (a b c : ℝ) : comparisonAngle a b c = comparisonAngle b a c := by
  unfold comparisonAngle
  congr 1
  congr 1 <;> ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_comm ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_comm

theorem tendsto_comparisonAngle {A : Type*} {l : Filter A} {a b c : A → ℝ}
    {a0 b0 c0 : ℝ} (ha : _root_.Filter.Tendsto a l (𝓝 a0)) (hb : _root_.Filter.Tendsto b l (𝓝 b0))
    (hc : _root_.Filter.Tendsto c l (𝓝 c0)) (ha0 : 0 < a0) (hb0 : 0 < b0) :
    Tendsto (fun i => comparisonAngle (a i) (b i) (c i)) l (𝓝 (comparisonAngle a0 b0 c0)) :=
  Real.continuous_arccos.continuousAt.tendsto.comp
    (((ha.pow 2).add (hb.pow 2)).sub (hc.pow 2) |>.div
      ((tendsto_const_nhds.mul ha).mul hb) (by positivity))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_comparisonAngle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_comparisonAngle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_comparisonAngle ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_comparisonAngle

theorem comparison_triangle_limits {A : Type*} {l : Filter A} [l.NeBot]
    {a b c : A → ℝ} {a0 b0 c0 : ℝ}
    (ha : _root_.Filter.Tendsto a l (𝓝 a0)) (hb : _root_.Filter.Tendsto b l (𝓝 b0)) (hc : _root_.Filter.Tendsto c l (𝓝 c0))
    (htri : ∀ᶠ i in l, |a i - b i| ≤ c i ∧ c i ≤ a i + b i) :
    |a0 - b0| ≤ c0 ∧ c0 ≤ a0 + b0 :=
  ⟨le_of_tendsto_of_tendsto (ha.sub hb).abs hc (htri.mono fun _ h => h.1),
    le_of_tendsto_of_tendsto hc (ha.add hb) (htri.mono fun _ h => h.2)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.comparison_triangle_limits then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.comparison_triangle_limits"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.comparison_triangle_limits ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.comparison_triangle_limits


theorem comparisonAngle_abs_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    comparisonAngle a b |a - b| = 0 := by
  have hden : 2 * a * b ≠ 0 := by positivity
  have hval : (a ^ 2 + b ^ 2 - |a - b| ^ 2) / (2 * a * b) = 1 := by
    apply (div_eq_iff hden).2
    nlinarith [sq_abs (a - b)]
  rw [comparisonAngle, hval, Real.arccos_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_abs_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_abs_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_abs_sub ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_abs_sub


theorem comparisonAngle_add {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    comparisonAngle a b (a + b) = Real.pi := by
  have hden : 2 * a * b ≠ 0 := by positivity
  have hval : (a ^ 2 + b ^ 2 - (a + b) ^ 2) / (2 * a * b) = -1 := by
    apply (div_eq_iff hden).2
    ring
  rw [comparisonAngle, hval, Real.arccos_neg_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_add ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_add

theorem cos_metricComparisonAngle {X : Type*} [MetricSpace X] {x o y : X}
    (hx : x ≠ o) (hy : y ≠ o) :
    Real.cos (metricComparisonAngle x o y) =
      (_root_.Dist.dist o x ^ 2 + _root_.Dist.dist o y ^ 2 - _root_.Dist.dist x y ^ 2) / (2 * _root_.Dist.dist o x * _root_.Dist.dist o y) := by
  apply cos_comparisonAngle (dist_pos.mpr hx.symm) (dist_pos.mpr hy.symm)
  · simpa only [dist_comm o x, dist_comm o y] using abs_dist_sub_le x y o
  · simpa only [dist_comm x o] using dist_triangle x o y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.cos_metricComparisonAngle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.cos_metricComparisonAngle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.cos_metricComparisonAngle ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.cos_metricComparisonAngle

end DifferentialGeometry.Geometry.Comparison.Toponogov
