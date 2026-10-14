import Submission.DifferentialGeometry.Topology.LoopSpace.CircleMetric
import Submission.DifferentialGeometry.Analysis.Calculus.Retraction.Normalization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.NormedSpace _root_.Set
open scoped _root_.NNReal

namespace DifferentialGeometry.Topology


def radialDirection (z : ℂ) : Circle :=
  if h : z = 0 then 1 else
    ⟨NormedSpace.normalize z, by
      exact mem_sphere_zero_iff_norm.mpr (_root_.NormedSpace.norm_normalize h)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialDirection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialDirection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialDirection ``Submission.DifferentialGeometry.Topology.radialDirection

theorem radialDirection_coe {z : ℂ} (hz : z ≠ 0) :
    (radialDirection z : ℂ) = NormedSpace.normalize z := by
  unfold radialDirection
  erw [dif_neg hz]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialDirection_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialDirection_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialDirection_coe ``Submission.DifferentialGeometry.Topology.radialDirection_coe

theorem radialDirection_reconstruct (z : ℂ) : ‖z‖ • (radialDirection z : ℂ) = z := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [radialDirection_coe hz]
    exact _root_.NormedSpace.norm_smul_normalize z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialDirection_reconstruct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialDirection_reconstruct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialDirection_reconstruct ``Submission.DifferentialGeometry.Topology.radialDirection_reconstruct

theorem radialDirection_unit (z : Circle) : radialDirection (z : ℂ) = z := by
  apply Subtype.ext
  rw [radialDirection_coe z.coe_ne_zero, _root_.NormedSpace.normalize_eq_self_of_norm_eq_one z.norm_coe]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialDirection_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialDirection_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialDirection_unit ``Submission.DifferentialGeometry.Topology.radialDirection_unit

theorem radialDirection_pos_smul {r : ℝ} (hr : 0 < r) (z : Circle) :
    radialDirection (r • (z : ℂ)) = z := by
  have hz : r • (z : ℂ) ≠ 0 := smul_ne_zero hr.ne' z.coe_ne_zero
  apply Subtype.ext
  rw [radialDirection_coe hz, _root_.NormedSpace.normalize_smul_of_pos hr,
    _root_.NormedSpace.normalize_eq_self_of_norm_eq_one z.norm_coe]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialDirection_pos_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialDirection_pos_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialDirection_pos_smul ``Submission.DifferentialGeometry.Topology.radialDirection_pos_smul


def polarAnnulusCoordinates (z : ℂ) : ℝ × loopCircle :=
  (2 * ‖z‖ - 1, (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (radialDirection z))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.polarAnnulusCoordinates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.polarAnnulusCoordinates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.polarAnnulusCoordinates ``Submission.DifferentialGeometry.Topology.polarAnnulusCoordinates

theorem polarAnnulusCoordinates_outer (θ : loopCircle) :
    polarAnnulusCoordinates (AddCircle.toCircle θ : ℂ) = (1, θ) := by
  unfold polarAnnulusCoordinates
  rw [Circle.norm_coe, radialDirection_unit, ← AddCircle.homeomorphCircle_apply one_ne_zero]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.polarAnnulusCoordinates_outer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.polarAnnulusCoordinates_outer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.polarAnnulusCoordinates_outer ``Submission.DifferentialGeometry.Topology.polarAnnulusCoordinates_outer

theorem polarAnnulusCoordinates_inner (θ : loopCircle) :
    polarAnnulusCoordinates ((1 / 2 : ℝ) • (AddCircle.toCircle θ : ℂ)) = (0, θ) := by
  unfold polarAnnulusCoordinates
  rw [norm_smul, Real.norm_eq_abs, Circle.norm_coe,
    radialDirection_pos_smul (by norm_num : (0 : ℝ) < 1 / 2),
    ← AddCircle.homeomorphCircle_apply one_ne_zero]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.polarAnnulusCoordinates_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.polarAnnulusCoordinates_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.polarAnnulusCoordinates_inner ``Submission.DifferentialGeometry.Topology.polarAnnulusCoordinates_inner



theorem polarAnnulusCoordinates_lipschitz :
    LipschitzOnWith 4 polarAnnulusCoordinates {z : ℂ | 1 / 2 ≤ ‖z‖} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hz)
  have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hw)
  have hd : _root_.Dist.dist (radialDirection z) (radialDirection w) ≤ 4 * _root_.Dist.dist z w := by
    change _root_.Dist.dist (radialDirection z : ℂ) (radialDirection w : ℂ) ≤ _
    rw [radialDirection_coe hz0, radialDirection_coe hw0]
    convert DifferentialGeometry.Analysis.normalize_dist_le (by norm_num : (0 : ℝ) < 1 / 2) hz hw using 1
    norm_num
  have ha := circle_parameter_lipschitz.dist_le_mul (radialDirection z) (radialDirection w)
  have ht : _root_.Dist.dist (2 * ‖z‖ - 1) (2 * ‖w‖ - 1) ≤ 4 * _root_.Dist.dist z w := by
    rw [Real.dist_eq, sub_sub_sub_cancel_right, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h := abs_norm_sub_norm_le z w
    rw [← dist_eq_norm] at h
    nlinarith [dist_nonneg (x := z) (y := w)]
  change _root_.Max.max (_root_.Dist.dist (2 * ‖z‖ - 1) (2 * ‖w‖ - 1)) _ ≤ (4 : ℝ) * _root_.Dist.dist z w
  apply max_le ht
  simpa only [NNReal.coe_one, one_mul, polarAnnulusCoordinates] using! ha.trans (by simpa using hd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.polarAnnulusCoordinates_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.polarAnnulusCoordinates_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.polarAnnulusCoordinates_lipschitz ``Submission.DifferentialGeometry.Topology.polarAnnulusCoordinates_lipschitz

end DifferentialGeometry.Topology
