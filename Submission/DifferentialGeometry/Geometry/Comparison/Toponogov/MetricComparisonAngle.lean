import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter _root_.Set _root_.Topology

noncomputable section

namespace DifferentialGeometry.Toponogov


def comparisonCosine (a b c : ℝ) : ℝ :=
  (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.comparisonCosine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.comparisonCosine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.comparisonCosine ``Submission.DifferentialGeometry.Toponogov.comparisonCosine

def comparisonAngle (a b c : ℝ) : ℝ :=
  Real.arccos (comparisonCosine a b c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.comparisonAngle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.comparisonAngle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.comparisonAngle ``Submission.DifferentialGeometry.Toponogov.comparisonAngle

def metricComparisonAngle {X : Type*} [PseudoMetricSpace X] (x o y : X) : ℝ :=
  comparisonAngle (_root_.Dist.dist o x) (_root_.Dist.dist o y) (_root_.Dist.dist x y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.metricComparisonAngle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.metricComparisonAngle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.metricComparisonAngle ``Submission.DifferentialGeometry.Toponogov.metricComparisonAngle


theorem comparisonAngle_mem_Icc (a b c : ℝ) : comparisonAngle a b c ∈ _root_.Set.Icc 0 Real.pi := by
  exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.comparisonAngle_mem_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.comparisonAngle_mem_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.comparisonAngle_mem_Icc ``Submission.DifferentialGeometry.Toponogov.comparisonAngle_mem_Icc

theorem comparisonCosine_mem_Icc {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hca : |a - b| ≤ c) (hac : c ≤ a + b) : comparisonCosine a b c ∈ _root_.Set.Icc (-1) 1 := by
  have hc : 0 ≤ c := (abs_nonneg (a - b)).trans hca
  have hab : 0 ≤ a + b := (add_pos ha hb).le
  have hsqLower : (a - b) ^ 2 ≤ c ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (a - b)) hc).2 hca
  have hsqUpper : c ^ 2 ≤ (a + b) ^ 2 :=
    (sq_le_sq₀ hc hab).2 hac
  have hden : 0 < 2 * a * b := by positivity
  constructor
  · rw [comparisonCosine, le_div_iff₀ hden]
    nlinarith
  · rw [comparisonCosine, div_le_iff₀ hden]
    nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.comparisonCosine_mem_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.comparisonCosine_mem_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.comparisonCosine_mem_Icc ``Submission.DifferentialGeometry.Toponogov.comparisonCosine_mem_Icc


theorem cos_comparisonAngle {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hca : |a - b| ≤ c) (hac : c ≤ a + b) :
    Real.cos (comparisonAngle a b c) = comparisonCosine a b c := by
  exact Real.cos_arccos (comparisonCosine_mem_Icc ha hb hca hac).1
    (comparisonCosine_mem_Icc ha hb hca hac).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.cos_comparisonAngle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.cos_comparisonAngle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.cos_comparisonAngle ``Submission.DifferentialGeometry.Toponogov.cos_comparisonAngle


theorem comparisonCosine_scale {a b c scale : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hscale : scale ≠ 0) :
    comparisonCosine (scale * a) (scale * b) (scale * c) = comparisonCosine a b c := by
  unfold comparisonCosine
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.comparisonCosine_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.comparisonCosine_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.comparisonCosine_scale ``Submission.DifferentialGeometry.Toponogov.comparisonCosine_scale

theorem comparisonAngle_scale {a b c scale : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hscale : 0 < scale) :
    comparisonAngle (scale * a) (scale * b) (scale * c) = comparisonAngle a b c := by
  exact congrArg Real.arccos (comparisonCosine_scale ha.ne' hb.ne' hscale.ne')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.comparisonAngle_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.comparisonAngle_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.comparisonAngle_scale ``Submission.DifferentialGeometry.Toponogov.comparisonAngle_scale


theorem comparisonCosine_comm (a b c : ℝ) :
    comparisonCosine a b c = comparisonCosine b a c := by
  unfold comparisonCosine
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.comparisonCosine_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.comparisonCosine_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.comparisonCosine_comm ``Submission.DifferentialGeometry.Toponogov.comparisonCosine_comm

theorem comparisonAngle_comm (a b c : ℝ) :
    comparisonAngle a b c = comparisonAngle b a c := by
  simp only [comparisonAngle, comparisonCosine_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.comparisonAngle_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.comparisonAngle_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.comparisonAngle_comm ``Submission.DifferentialGeometry.Toponogov.comparisonAngle_comm


theorem comparisonSideInequalities_limit {a b c : ℕ → ℝ} {a₀ b₀ c₀ : ℝ}
    (ha : _root_.Filter.Tendsto a _root_.Filter.atTop (nhds a₀)) (hb : _root_.Filter.Tendsto b _root_.Filter.atTop (nhds b₀))
    (hc : _root_.Filter.Tendsto c _root_.Filter.atTop (nhds c₀)) (hca : ∀ j, |a j - b j| ≤ c j)
    (hac : ∀ j, c j ≤ a j + b j) : |a₀ - b₀| ≤ c₀ ∧ c₀ ≤ a₀ + b₀ := by
  constructor
  · exact le_of_tendsto_of_tendsto' ((ha.sub hb).abs) hc hca
  · exact le_of_tendsto_of_tendsto' hc (ha.add hb) hac

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.comparisonSideInequalities_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.comparisonSideInequalities_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.comparisonSideInequalities_limit ``Submission.DifferentialGeometry.Toponogov.comparisonSideInequalities_limit


theorem comparisonAngle_tendsto {a b c : ℕ → ℝ} {a₀ b₀ c₀ : ℝ}
    (ha : _root_.Filter.Tendsto a _root_.Filter.atTop (nhds a₀)) (hb : _root_.Filter.Tendsto b _root_.Filter.atTop (nhds b₀))
    (hc : _root_.Filter.Tendsto c _root_.Filter.atTop (nhds c₀)) (ha₀ : 0 < a₀) (hb₀ : 0 < b₀) :
    _root_.Filter.Tendsto (fun j ↦ comparisonAngle (a j) (b j) (c j)) _root_.Filter.atTop
      (nhds (comparisonAngle a₀ b₀ c₀)) := by
  have hden : 2 * a₀ * b₀ ≠ 0 := by positivity
  have hquotient :
      _root_.Filter.Tendsto (fun j ↦ comparisonCosine (a j) (b j) (c j)) _root_.Filter.atTop
        (nhds (comparisonCosine a₀ b₀ c₀)) := by
    change _root_.Filter.Tendsto
      ((fun j ↦ a j ^ 2 + b j ^ 2 - c j ^ 2) / (fun j ↦ 2 * a j * b j)) _root_.Filter.atTop
      (nhds ((a₀ ^ 2 + b₀ ^ 2 - c₀ ^ 2) / (2 * a₀ * b₀)))
    exact (((ha.pow 2).add (hb.pow 2)).sub (hc.pow 2)).div
      ((tendsto_const_nhds.mul ha).mul hb) hden
  exact (Real.continuous_arccos.tendsto _).comp hquotient

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.comparisonAngle_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.comparisonAngle_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.comparisonAngle_tendsto ``Submission.DifferentialGeometry.Toponogov.comparisonAngle_tendsto

theorem comparisonAngle_tendsto_of_sideInequalities {a b c : ℕ → ℝ} {a₀ b₀ c₀ : ℝ}
    (ha : _root_.Filter.Tendsto a _root_.Filter.atTop (nhds a₀)) (hb : _root_.Filter.Tendsto b _root_.Filter.atTop (nhds b₀))
    (hc : _root_.Filter.Tendsto c _root_.Filter.atTop (nhds c₀)) (_ha_pos : ∀ j, 0 < a j) (_hb_pos : ∀ j, 0 < b j)
    (hca : ∀ j, |a j - b j| ≤ c j) (hac : ∀ j, c j ≤ a j + b j)
    (ha₀ : 0 < a₀) (hb₀ : 0 < b₀) :
    (|a₀ - b₀| ≤ c₀ ∧ c₀ ≤ a₀ + b₀) ∧
      _root_.Filter.Tendsto (fun j ↦ comparisonAngle (a j) (b j) (c j)) _root_.Filter.atTop
        (nhds (comparisonAngle a₀ b₀ c₀)) := by
  exact ⟨comparisonSideInequalities_limit ha hb hc hca hac,
    comparisonAngle_tendsto ha hb hc ha₀ hb₀⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.comparisonAngle_tendsto_of_sideInequalities then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.comparisonAngle_tendsto_of_sideInequalities"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.comparisonAngle_tendsto_of_sideInequalities ``Submission.DifferentialGeometry.Toponogov.comparisonAngle_tendsto_of_sideInequalities


theorem comparisonAngle_abs_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    comparisonAngle a b |a - b| = 0 := by
  have hquotient : comparisonCosine a b |a - b| = 1 := by
    unfold comparisonCosine
    rw [sq_abs]
    field_simp [ha.ne, hb.ne]
    ring
  simp only [comparisonAngle, hquotient, Real.arccos_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.comparisonAngle_abs_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.comparisonAngle_abs_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.comparisonAngle_abs_sub ``Submission.DifferentialGeometry.Toponogov.comparisonAngle_abs_sub


theorem comparisonAngle_add {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    comparisonAngle a b (a + b) = Real.pi := by
  have hquotient : comparisonCosine a b (a + b) = -1 := by
    unfold comparisonCosine
    field_simp [ha.ne, hb.ne]
    ring
  simp only [comparisonAngle, hquotient, Real.arccos_neg_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.comparisonAngle_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.comparisonAngle_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.comparisonAngle_add ``Submission.DifferentialGeometry.Toponogov.comparisonAngle_add


theorem metricComparisonAngle_sideInequalities {X : Type*} [PseudoMetricSpace X] (x o y : X) :
    |dist o x - _root_.Dist.dist o y| ≤ _root_.Dist.dist x y ∧ _root_.Dist.dist x y ≤ _root_.Dist.dist o x + _root_.Dist.dist o y := by
  constructor
  · simpa [dist_comm] using abs_dist_sub_le x y o
  · simpa [dist_comm] using dist_triangle x o y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.metricComparisonAngle_sideInequalities then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.metricComparisonAngle_sideInequalities"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.metricComparisonAngle_sideInequalities ``Submission.DifferentialGeometry.Toponogov.metricComparisonAngle_sideInequalities


theorem metricComparisonCosine_mem_Icc {X : Type*} [MetricSpace X] {x o y : X}
    (hxo : x ≠ o) (hyo : y ≠ o) :
    comparisonCosine (_root_.Dist.dist o x) (_root_.Dist.dist o y) (_root_.Dist.dist x y) ∈ _root_.Set.Icc (-1) 1 := by
  exact comparisonCosine_mem_Icc (dist_pos.mpr hxo.symm) (dist_pos.mpr hyo.symm)
    (metricComparisonAngle_sideInequalities x o y).1
    (metricComparisonAngle_sideInequalities x o y).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.metricComparisonCosine_mem_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.metricComparisonCosine_mem_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.metricComparisonCosine_mem_Icc ``Submission.DifferentialGeometry.Toponogov.metricComparisonCosine_mem_Icc


theorem cos_metricComparisonAngle {X : Type*} [MetricSpace X] {x o y : X}
    (hxo : x ≠ o) (hyo : y ≠ o) :
    Real.cos (metricComparisonAngle x o y) =
      comparisonCosine (_root_.Dist.dist o x) (_root_.Dist.dist o y) (_root_.Dist.dist x y) := by
  exact Real.cos_arccos (metricComparisonCosine_mem_Icc hxo hyo).1
    (metricComparisonCosine_mem_Icc hxo hyo).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.cos_metricComparisonAngle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.cos_metricComparisonAngle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.cos_metricComparisonAngle ``Submission.DifferentialGeometry.Toponogov.cos_metricComparisonAngle


@[simp] theorem metricComparisonAngle_self {X : Type*} [MetricSpace X] {x o : X}
    (hxo : x ≠ o) : metricComparisonAngle x o x = 0 := by
  have hpos : 0 < _root_.Dist.dist o x := dist_pos.mpr hxo.symm
  simpa only [metricComparisonAngle, dist_self, sub_self, abs_zero] using
    (comparisonAngle_abs_sub hpos hpos)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.metricComparisonAngle_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.metricComparisonAngle_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.metricComparisonAngle_self ``Submission.DifferentialGeometry.Toponogov.metricComparisonAngle_self

end DifferentialGeometry.Toponogov
