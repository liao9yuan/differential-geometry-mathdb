import Mathlib.Analysis.Calculus.BumpFunction.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace ContDiffBump
open _root_.ContDiffBump

open _root_.Set
open scoped _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [HasContDiffBump E]


open _root_.ContDiffBump in
noncomputable def radial (b : ContDiffBump (0 : E)) (x : E) : E :=
  b x • x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffBump.radial then
    throwError "Refusing to shadow existing declaration ContDiffBump.radial"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffBump.radial ``Submission.ContDiffBump.radial


open _root_.ContDiffBump in
theorem radial_contDiff (b : ContDiffBump (0 : E)) :
    ContDiff Real (∞ : WithTop ℕ∞) b.radial := by
  exact b.contDiff.smul contDiff_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffBump.radial_contDiff then
    throwError "Refusing to shadow existing declaration ContDiffBump.radial_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffBump.radial_contDiff ``Submission.ContDiffBump.radial_contDiff


open _root_.ContDiffBump in
theorem radial_mapsTo (b : ContDiffBump (0 : E)) :
    MapsTo b.radial Set.univ (Metric.ball 0 b.rOut) := by
  intro x _hx
  by_cases hbx : b x = 0
  · rw [radial, hbx, zero_smul, Metric.mem_ball, dist_self]
    exact b.rOut_pos
  · have hxout : x ∈ Metric.ball (0 : E) b.rOut := by
      rw [← b.support_eq]
      exact hbx
    rw [Metric.mem_ball, dist_zero_right] at hxout ⊢
    rw [radial, norm_smul, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
    calc
      b x * ‖x‖ ≤ 1 * ‖x‖ :=
        mul_le_mul_of_nonneg_right b.le_one (norm_nonneg x)
      _ = ‖x‖ := one_mul _
      _ < b.rOut := hxout

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffBump.radial_mapsTo then
    throwError "Refusing to shadow existing declaration ContDiffBump.radial_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffBump.radial_mapsTo ``Submission.ContDiffBump.radial_mapsTo


open _root_.ContDiffBump in
theorem radial_eq_self (b : ContDiffBump (0 : E)) {x : E}
    (hx : x ∈ Metric.closedBall 0 b.rIn) : b.radial x = x := by
  rw [radial, b.one_of_mem_closedBall hx, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffBump.radial_eq_self then
    throwError "Refusing to shadow existing declaration ContDiffBump.radial_eq_self"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffBump.radial_eq_self ``Submission.ContDiffBump.radial_eq_self

end ContDiffBump
