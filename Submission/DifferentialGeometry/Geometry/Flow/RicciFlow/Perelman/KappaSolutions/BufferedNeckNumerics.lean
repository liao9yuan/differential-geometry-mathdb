import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry.Comparison.Toponogov

theorem bufferedNeck_band_connector_bound {a : ℝ} (ha : 0 < a) :
    (13 / 12 : ℝ) * Real.sqrt ((10 * Real.pi) ^ 2 + Real.pi ^ 2) * a <
      11 * Real.pi * a := by
  let s : ℝ := Real.sqrt ((10 * Real.pi) ^ 2 + Real.pi ^ 2)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = 101 * Real.pi ^ 2 := by
    dsimp only [s]
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hbound : s < (132 / 13 : ℝ) * Real.pi := by
    by_contra h
    have hlarge : (132 / 13 : ℝ) * Real.pi ≤ s := le_of_not_gt h
    have hprod := mul_nonneg (sub_nonneg.mpr hlarge)
      (add_nonneg hs (by positivity : 0 ≤ (132 / 13 : ℝ) * Real.pi))
    nlinarith
  have hlength : (13 / 12 : ℝ) * s < 11 * Real.pi := by nlinarith
  exact mul_lt_mul_of_pos_right hlength ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedNeck_band_connector_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedNeck_band_connector_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedNeck_band_connector_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedNeck_band_connector_bound

theorem bufferedNeck_cosine_lower {a r₁ r₂ w : ℝ} (ha : 0 < a)
    (h₁ : (11 / 12 : ℝ) * (5 * Real.pi) * a ≤ r₁)
    (h₂ : (11 / 12 : ℝ) * (5 * Real.pi) * a ≤ r₂)
    (hw0 : 0 ≤ w) (hw : w ≤ (13 / 12 : ℝ) * Real.pi * a) :
    1 - (169 / 6050 : ℝ) ≤ (r₁ ^ 2 + r₂ ^ 2 - w ^ 2) / (2 * r₁ * r₂) := by
  let l : ℝ := (11 / 12 : ℝ) * (5 * Real.pi) * a
  let u : ℝ := (13 / 12 : ℝ) * Real.pi * a
  have hl : 0 < l := by dsimp only [l]; positivity
  have hr₁ : 0 < r₁ := hl.trans_le h₁
  have hr₂ : 0 < r₂ := hl.trans_le h₂
  have hprod : l * l ≤ r₁ * r₂ := mul_le_mul h₁ h₂ hl.le hr₁.le
  have hwSq : w ^ 2 ≤ u ^ 2 := by
    change w ^ 2 ≤ ((13 / 12 : ℝ) * Real.pi * a) ^ 2
    nlinarith [mul_self_le_mul_self hw0 hw]
  have hratio : u ^ 2 = (169 / 6050 : ℝ) * (2 * l ^ 2) := by
    dsimp only [l, u]
    ring
  have hwden : w ^ 2 ≤ (169 / 6050 : ℝ) * (2 * r₁ * r₂) := by
    nlinarith
  have hden : 0 < 2 * r₁ * r₂ := by positivity
  rw [le_div_iff₀ hden]
  nlinarith [sq_nonneg (r₁ - r₂)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedNeck_cosine_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedNeck_cosine_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedNeck_cosine_lower ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedNeck_cosine_lower

private theorem bufferedNeck_cosine_gap :
    Real.cos (Real.pi / 6) < 1 - (169 / 6050 : ℝ) := by
  have hs : Real.sqrt 3 < (9 / 5 : ℝ) := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith [Real.sqrt_nonneg 3]
  rw [Real.cos_pi_div_six]
  nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedNeck_cosine_gap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedNeck_cosine_gap target :: scope.openDecls } }

theorem bufferedNeck_comparisonAngle_lt_pi_div_six {a r₁ r₂ w : ℝ} (ha : 0 < a)
    (h₁ : (11 / 12 : ℝ) * (5 * Real.pi) * a ≤ r₁)
    (h₂ : (11 / 12 : ℝ) * (5 * Real.pi) * a ≤ r₂)
    (hw0 : 0 ≤ w) (hw : w ≤ (13 / 12 : ℝ) * Real.pi * a) :
    comparisonAngle r₁ r₂ w < Real.pi / 6 := by
  have hq := bufferedNeck_cosine_lower ha h₁ h₂ hw0 hw
  have hangle := Real.arccos_lt_arccos (Real.neg_one_le_cos (Real.pi / 6))
    bufferedNeck_cosine_gap (by norm_num : 1 - (169 / 6050 : ℝ) ≤ 1)
  have hpi0 : 0 ≤ Real.pi / 6 := by positivity
  have hpile : Real.pi / 6 ≤ Real.pi := by nlinarith [Real.pi_pos]
  rw [Real.arccos_cos hpi0 hpile] at hangle
  exact (Real.arccos_le_arccos hq).trans_lt hangle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedNeck_comparisonAngle_lt_pi_div_six then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedNeck_comparisonAngle_lt_pi_div_six"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedNeck_comparisonAngle_lt_pi_div_six ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedNeck_comparisonAngle_lt_pi_div_six

theorem bufferedNeck_metricComparisonAngle_lt_pi_div_six
    {X : Type*} [MetricSpace X] {a : ℝ} (ha : 0 < a) (y z₁ z₂ : X)
    (h₁ : (11 / 12 : ℝ) * (5 * Real.pi) * a ≤ _root_.Dist.dist y z₁)
    (h₂ : (11 / 12 : ℝ) * (5 * Real.pi) * a ≤ _root_.Dist.dist y z₂)
    (hw : _root_.Dist.dist z₁ z₂ ≤ (13 / 12 : ℝ) * Real.pi * a) :
    metricComparisonAngle z₁ y z₂ < Real.pi / 6 :=
  bufferedNeck_comparisonAngle_lt_pi_div_six ha h₁ h₂ dist_nonneg hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedNeck_metricComparisonAngle_lt_pi_div_six then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedNeck_metricComparisonAngle_lt_pi_div_six"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedNeck_metricComparisonAngle_lt_pi_div_six ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.bufferedNeck_metricComparisonAngle_lt_pi_div_six

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
