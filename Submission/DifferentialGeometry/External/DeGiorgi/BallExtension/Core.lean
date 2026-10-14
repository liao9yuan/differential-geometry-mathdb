-- Modified 2026-04-28: updated internal import paths for project namespace
import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace
import Submission.DifferentialGeometry.External.DeGiorgi.UnitBallApproximation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Ball Extension Core

Core definitions and basic algebra for the explicit unit-ball extension operator.
-/

noncomputable section

open _root_.MeasureTheory
open scoped _root_.NNReal

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Retraction used for the explicit unit-ball extension operator. -/
def unitBallRetraction (x : E) : E :=
  if ‖x‖ ≤ 1 then
    x
  else if ‖x‖ < 2 then
    (‖x‖ ^ (2 : ℕ))⁻¹ • x
  else
    0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.unitBallRetraction then
    throwError "Refusing to shadow existing declaration DeGiorgi.unitBallRetraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.unitBallRetraction ``Submission.DeGiorgi.unitBallRetraction

/-- Radial cutoff used for the explicit unit-ball extension operator. -/
def unitBallCutoff (x : E) : ℝ :=
  _root_.Min.min 1 (_root_.Max.max (2 - ‖x‖) 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.unitBallCutoff then
    throwError "Refusing to shadow existing declaration DeGiorgi.unitBallCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.unitBallCutoff ``Submission.DeGiorgi.unitBallCutoff

/-- Explicit unit-ball extension operator. -/
def unitBallExtension (u : E → ℝ) (x : E) : ℝ :=
  unitBallCutoff x * u (unitBallRetraction x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.unitBallExtension then
    throwError "Refusing to shadow existing declaration DeGiorgi.unitBallExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.unitBallExtension ``Submission.DeGiorgi.unitBallExtension

omit [NeZero d] in
lemma unitBallExtension_zero :
    unitBallExtension (d := d) (fun _ : E => (0 : ℝ)) = fun _ : E => (0 : ℝ) := by
  funext x
  simp [unitBallExtension]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.unitBallExtension_zero then
    throwError "Refusing to shadow existing declaration DeGiorgi.unitBallExtension_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.unitBallExtension_zero ``Submission.DeGiorgi.unitBallExtension_zero

omit [NeZero d] in
lemma unitBallExtension_add (u v : E → ℝ) :
    unitBallExtension (d := d) (fun x => u x + v x) =
      fun x => unitBallExtension (d := d) u x + unitBallExtension (d := d) v x := by
  funext x
  simp [unitBallExtension, mul_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.unitBallExtension_add then
    throwError "Refusing to shadow existing declaration DeGiorgi.unitBallExtension_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.unitBallExtension_add ``Submission.DeGiorgi.unitBallExtension_add

omit [NeZero d] in
lemma unitBallExtension_sub (u v : E → ℝ) :
    unitBallExtension (d := d) (fun x => u x - v x) =
      fun x => unitBallExtension (d := d) u x - unitBallExtension (d := d) v x := by
  funext x
  simp [unitBallExtension, sub_eq_add_neg, mul_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.unitBallExtension_sub then
    throwError "Refusing to shadow existing declaration DeGiorgi.unitBallExtension_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.unitBallExtension_sub ``Submission.DeGiorgi.unitBallExtension_sub

omit [NeZero d] in
lemma unitBallRetraction_eq_self_of_norm_le_one {x : E} (hx : ‖x‖ ≤ 1) :
    unitBallRetraction (d := d) x = x := by
  simp [unitBallRetraction, hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.unitBallRetraction_eq_self_of_norm_le_one then
    throwError "Refusing to shadow existing declaration DeGiorgi.unitBallRetraction_eq_self_of_norm_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.unitBallRetraction_eq_self_of_norm_le_one ``Submission.DeGiorgi.unitBallRetraction_eq_self_of_norm_le_one

omit [NeZero d] in
lemma unitBallRetraction_eq_self_of_mem_ball {x : E} (hx : x ∈ Metric.ball (0 : E) 1) :
    unitBallRetraction (d := d) x = x := by
  apply unitBallRetraction_eq_self_of_norm_le_one (d := d)
  rw [Metric.mem_ball, dist_zero_right] at hx
  exact le_of_lt hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.unitBallRetraction_eq_self_of_mem_ball then
    throwError "Refusing to shadow existing declaration DeGiorgi.unitBallRetraction_eq_self_of_mem_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.unitBallRetraction_eq_self_of_mem_ball ``Submission.DeGiorgi.unitBallRetraction_eq_self_of_mem_ball

omit [NeZero d] in
lemma unitBallExtension_eq_of_mem_ball {u : E → ℝ} {x : E}
    (hx : x ∈ Metric.ball (0 : E) 1) :
    unitBallExtension (d := d) u x = u x := by
  unfold unitBallExtension unitBallCutoff
  rw [unitBallRetraction_eq_self_of_mem_ball (d := d) hx]
  rw [Metric.mem_ball, dist_zero_right] at hx
  have hgt : 1 < 2 - ‖x‖ := by linarith
  rw [max_eq_left (by positivity), min_eq_left (le_of_lt hgt), one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.unitBallExtension_eq_of_mem_ball then
    throwError "Refusing to shadow existing declaration DeGiorgi.unitBallExtension_eq_of_mem_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.unitBallExtension_eq_of_mem_ball ``Submission.DeGiorgi.unitBallExtension_eq_of_mem_ball

omit [NeZero d] in
lemma unitBallRetraction_eq_smul_of_annulus {x : E}
    (h1 : 1 < ‖x‖) (h2 : ‖x‖ < 2) :
    unitBallRetraction (d := d) x = (‖x‖ ^ (2 : ℕ))⁻¹ • x := by
  have hx1 : ¬ ‖x‖ ≤ 1 := by linarith
  simp [unitBallRetraction, hx1, h2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.unitBallRetraction_eq_smul_of_annulus then
    throwError "Refusing to shadow existing declaration DeGiorgi.unitBallRetraction_eq_smul_of_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.unitBallRetraction_eq_smul_of_annulus ``Submission.DeGiorgi.unitBallRetraction_eq_smul_of_annulus

end DeGiorgi
