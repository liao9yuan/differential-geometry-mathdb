import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Function _root_.Metric
open scoped _root_.Topology
namespace DifferentialGeometry.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ballPrismScale (z : unitInterval × _root_.Metric.closedBall (0 : E) 1) : ℝ :=
  _root_.Max.max ‖(z.2 : E)‖ (1 - z.1.val / 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ballPrismScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ballPrismScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ballPrismScale ``Submission.DifferentialGeometry.Topology.ballPrismScale

omit [NormedSpace ℝ E] in
theorem half_le_ballPrismScale (z : unitInterval × _root_.Metric.closedBall (0 : E) 1) :
    (1 / 2 : ℝ) ≤ ballPrismScale z := by
  apply le_trans _ (le_max_right _ _)
  linarith [z.1.property.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.half_le_ballPrismScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.half_le_ballPrismScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.half_le_ballPrismScale ``Submission.DifferentialGeometry.Topology.half_le_ballPrismScale

omit [NormedSpace ℝ E] in
theorem ballPrismScale_pos (z : unitInterval × _root_.Metric.closedBall (0 : E) 1) : 0 < ballPrismScale z :=
  lt_of_lt_of_le (by norm_num) (half_le_ballPrismScale z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ballPrismScale_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ballPrismScale_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ballPrismScale_pos ``Submission.DifferentialGeometry.Topology.ballPrismScale_pos

omit [NormedSpace ℝ E] in
theorem continuous_ballPrismScale : Continuous (ballPrismScale (E := E)) :=
  continuous_norm.comp (continuous_subtype_val.comp continuous_snd) |>.max
    (continuous_const.sub ((continuous_subtype_val.comp continuous_fst).div_const 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_ballPrismScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_ballPrismScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_ballPrismScale ``Submission.DifferentialGeometry.Topology.continuous_ballPrismScale

omit [NormedSpace ℝ E] in
theorem ballPrismScale_le_one (z : unitInterval × _root_.Metric.closedBall (0 : E) 1) :
    ballPrismScale z ≤ 1 := by
  apply max_le
  · simpa only [Metric.mem_closedBall, dist_zero_right] using z.2.property
  · linarith [z.1.property.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ballPrismScale_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ballPrismScale_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ballPrismScale_le_one ``Submission.DifferentialGeometry.Topology.ballPrismScale_le_one

def ballPrismTime (z : unitInterval × _root_.Metric.closedBall (0 : E) 1) : unitInterval :=
  ⟨2 - (2 - z.1.val) / ballPrismScale z, by
    have hr := ballPrismScale_pos z
    have hlow : 1 - z.1.val / 2 ≤ ballPrismScale z := le_max_right _ _
    have hhigh := ballPrismScale_le_one z
    have hdiv0 : (2 - z.1.val) / ballPrismScale z ≤ 2 :=
      (div_le_iff₀ hr).mpr (by linarith)
    have hdiv1 : 1 ≤ (2 - z.1.val) / ballPrismScale z :=
      (le_div_iff₀ hr).mpr (by linarith [z.1.property.2])
    exact ⟨by linarith, by linarith⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ballPrismTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ballPrismTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ballPrismTime ``Submission.DifferentialGeometry.Topology.ballPrismTime

def ballPrismPosition (z : unitInterval × _root_.Metric.closedBall (0 : E) 1) : _root_.Metric.closedBall (0 : E) 1 :=
  ⟨(ballPrismScale z)⁻¹ • (z.2 : E), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv,
      Real.norm_of_nonneg (ballPrismScale_pos z).le]
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_le_iff₀ (ballPrismScale_pos z)).mpr (by
      simpa only [one_mul, ballPrismScale] using (le_max_left ‖(z.2 : E)‖ (1 - z.1.val / 2)))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ballPrismPosition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ballPrismPosition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ballPrismPosition ``Submission.DifferentialGeometry.Topology.ballPrismPosition

def ballPrismRetract (z : unitInterval × _root_.Metric.closedBall (0 : E) 1) :
    unitInterval × _root_.Metric.closedBall (0 : E) 1 := (ballPrismTime z, ballPrismPosition z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ballPrismRetract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ballPrismRetract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ballPrismRetract ``Submission.DifferentialGeometry.Topology.ballPrismRetract

theorem continuous_ballPrismRetract :
    Continuous (ballPrismRetract (E := E)) := by
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact continuous_const.sub
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).div
        (continuous_ballPrismScale (E := E)) (fun z => (ballPrismScale_pos z).ne'))
  · apply Continuous.subtype_mk
    exact ((continuous_ballPrismScale (E := E)).inv₀
      (fun z => (ballPrismScale_pos z).ne')).smul
        (continuous_subtype_val.comp continuous_snd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_ballPrismRetract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_ballPrismRetract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_ballPrismRetract ``Submission.DifferentialGeometry.Topology.continuous_ballPrismRetract

theorem ballPrismRetract_bottom (v : _root_.Metric.closedBall (0 : E) 1) :
    ballPrismRetract (0, v) = (0, v) := by
  have hs : ballPrismScale (0, v) = 1 := by
    change _root_.Max.max ‖(v : E)‖ (1 - (0 : ℝ) / 2) = 1
    simpa only [zero_div, sub_zero] using
      max_eq_right (show ‖(v : E)‖ ≤ 1 by
        simpa only [Metric.mem_closedBall, dist_zero_right] using v.property)
  apply Prod.ext
  · apply Subtype.ext
    change 2 - (2 - (0 : ℝ)) / ballPrismScale (0, v) = 0
    rw [hs]
    norm_num
  · apply Subtype.ext
    change (ballPrismScale (0, v))⁻¹ • (v : E) = (v : E)
    rw [hs, inv_one, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ballPrismRetract_bottom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ballPrismRetract_bottom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ballPrismRetract_bottom ``Submission.DifferentialGeometry.Topology.ballPrismRetract_bottom

theorem ballPrismRetract_side (t : unitInterval) (v : _root_.Metric.closedBall (0 : E) 1)
    (hv : (v : E) ∈ _root_.Metric.sphere (0 : E) 1) : ballPrismRetract (t, v) = (t, v) := by
  have hn : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp hv
  have hs : ballPrismScale (t, v) = 1 := by
    change _root_.Max.max ‖(v : E)‖ (1 - t.val / 2) = 1
    rw [hn]
    exact max_eq_left (by linarith [t.property.1])
  apply Prod.ext
  · apply Subtype.ext
    change 2 - (2 - t.val) / ballPrismScale (t, v) = t.val
    rw [hs]
    ring
  · apply Subtype.ext
    change (ballPrismScale (t, v))⁻¹ • (v : E) = (v : E)
    rw [hs, inv_one, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ballPrismRetract_side then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ballPrismRetract_side"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ballPrismRetract_side ``Submission.DifferentialGeometry.Topology.ballPrismRetract_side

theorem ballPrismRetract_time_zero (z : unitInterval × _root_.Metric.closedBall (0 : E) 1)
    (h : ‖(z.2 : E)‖ ≤ 1 - z.1.val / 2) : (ballPrismRetract z).1 = 0 := by
  have hr := ballPrismScale_pos z
  have hs : ballPrismScale z = 1 - z.1.val / 2 := max_eq_right h
  have hd : (2 - z.1.val) / ballPrismScale z = 2 :=
    (div_eq_iff hr.ne').mpr (by rw [hs]; ring)
  apply Subtype.ext
  change 2 - (2 - z.1.val) / ballPrismScale z = 0
  rw [hd, sub_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ballPrismRetract_time_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ballPrismRetract_time_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ballPrismRetract_time_zero ``Submission.DifferentialGeometry.Topology.ballPrismRetract_time_zero

theorem ballPrismRetract_position_sphere (z : unitInterval × _root_.Metric.closedBall (0 : E) 1)
    (h : 1 - z.1.val / 2 ≤ ‖(z.2 : E)‖) :
    ((ballPrismRetract z).2 : E) ∈ _root_.Metric.sphere (0 : E) 1 := by
  have hr := ballPrismScale_pos z
  have hs : ballPrismScale z = ‖(z.2 : E)‖ := max_eq_left h
  apply mem_sphere_zero_iff_norm.mpr
  change ‖(ballPrismScale z)⁻¹ • (z.2 : E)‖ = 1
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.le, ← hs, inv_mul_cancel₀ hr.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ballPrismRetract_position_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ballPrismRetract_position_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ballPrismRetract_position_sphere ``Submission.DifferentialGeometry.Topology.ballPrismRetract_position_sphere

theorem ballPrismRetract_image (z : unitInterval × _root_.Metric.closedBall (0 : E) 1) :
    (ballPrismRetract z).1 = 0 ∨ ((ballPrismRetract z).2 : E) ∈ _root_.Metric.sphere (0 : E) 1 := by
  rcases le_total ‖(z.2 : E)‖ (1 - z.1.val / 2) with h | h
  · exact Or.inl (ballPrismRetract_time_zero z h)
  · exact Or.inr (ballPrismRetract_position_sphere z h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ballPrismRetract_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ballPrismRetract_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ballPrismRetract_image ``Submission.DifferentialGeometry.Topology.ballPrismRetract_image

theorem ballPrismRetract_idempotent (z : unitInterval × _root_.Metric.closedBall (0 : E) 1) :
    ballPrismRetract (ballPrismRetract z) = ballPrismRetract z := by
  rcases ballPrismRetract_image z with h | h
  · have heq : ballPrismRetract z = (0, (ballPrismRetract z).2) := Prod.ext h rfl
    rw [heq]
    exact ballPrismRetract_bottom _
  · exact ballPrismRetract_side _ _ h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ballPrismRetract_idempotent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ballPrismRetract_idempotent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ballPrismRetract_idempotent ``Submission.DifferentialGeometry.Topology.ballPrismRetract_idempotent

end DifferentialGeometry.Topology
