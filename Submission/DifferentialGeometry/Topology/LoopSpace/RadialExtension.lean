import Submission.DifferentialGeometry.Topology.LoopSpace.PolarAnnulus
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.SpanningDisk
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.NormedSpace _root_.Metric
open scoped _root_.NNReal

namespace DifferentialGeometry.Topology


def radialExtension (F : Circle → Circle) (z : ℂ) : ℂ := ‖z‖ • (F (radialDirection z) : ℂ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialExtension ``Submission.DifferentialGeometry.Topology.radialExtension

@[simp] theorem radialExtension_zero (F : Circle → Circle) : radialExtension F 0 = 0 := by
  simp [radialExtension]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialExtension_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialExtension_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialExtension_zero ``Submission.DifferentialGeometry.Topology.radialExtension_zero

@[simp] theorem radialExtension_norm (F : Circle → Circle) (z : ℂ) :
    ‖radialExtension F z‖ = ‖z‖ := by
  rw [radialExtension, norm_smul, Circle.norm_coe, mul_one]
  exact norm_norm z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialExtension_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialExtension_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialExtension_norm ``Submission.DifferentialGeometry.Topology.radialExtension_norm

theorem radialExtension_circle (F : Circle → Circle) (z : Circle) :
    radialExtension F (z : ℂ) = (F z : ℂ) := by
  rw [radialExtension, Circle.norm_coe, one_smul, radialDirection_unit]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialExtension_circle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialExtension_circle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialExtension_circle ``Submission.DifferentialGeometry.Topology.radialExtension_circle

theorem radialDirection_radialExtension (F : Circle → Circle) {z : ℂ} (hz : z ≠ 0) :
    radialDirection (radialExtension F z) = F (radialDirection z) :=
  radialDirection_pos_smul (norm_pos_iff.mpr hz) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialDirection_radialExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialDirection_radialExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialDirection_radialExtension ``Submission.DifferentialGeometry.Topology.radialDirection_radialExtension

theorem radialExtension_id (z : ℂ) : radialExtension id z = z := radialDirection_reconstruct z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialExtension_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialExtension_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialExtension_id ``Submission.DifferentialGeometry.Topology.radialExtension_id

theorem radialExtension_comp (F G : Circle → Circle) (z : ℂ) :
    radialExtension (F ∘ G) z = radialExtension F (radialExtension G z) := by
  by_cases hz : z = 0
  · simp [hz]
  · change ‖z‖ • (F (G (radialDirection z)) : ℂ) =
      ‖radialExtension G z‖ • (F (radialDirection (radialExtension G z)) : ℂ)
    rw [radialExtension_norm, radialDirection_radialExtension G hz]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialExtension_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialExtension_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialExtension_comp ``Submission.DifferentialGeometry.Topology.radialExtension_comp



theorem radialExtension_lipschitz {F : Circle → Circle} {L : ℝ≥0}
    (hF : LipschitzWith L F) : LipschitzWith (2 * L + 1) (radialExtension F) := by
  have hordered (x y : ℂ) (hxy : ‖x‖ ≤ ‖y‖) :
      dist (radialExtension F x) (radialExtension F y) ≤ (2 * (L : ℝ) + 1) * _root_.Dist.dist x y := by
    by_cases hx : x = 0
    · subst x
      rw [radialExtension_zero, dist_zero_left, radialExtension_norm, dist_zero_left]
      nlinarith [L.coe_nonneg, norm_nonneg y]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hy : y ≠ 0 := norm_pos_iff.mp (hxpos.trans_le hxy)
    have hdir : _root_.Dist.dist (radialDirection x) (radialDirection y) ≤ (2 / ‖x‖) * _root_.Dist.dist x y := by
      change _root_.Dist.dist (radialDirection x : ℂ) (radialDirection y : ℂ) ≤ _
      rw [radialDirection_coe hx, radialDirection_coe hy]
      exact DifferentialGeometry.Analysis.normalize_dist_le hxpos le_rfl hxy
    have hangular := (hF.dist_le_mul (radialDirection x) (radialDirection y)).trans
      (mul_le_mul_of_nonneg_left hdir L.coe_nonneg)
    have hnormdiff := abs_norm_sub_norm_le x y
    have heq : radialExtension F x - radialExtension F y =
        ‖x‖ • ((F (radialDirection x) : ℂ) - (F (radialDirection y) : ℂ)) +
          (‖x‖ - ‖y‖) • (F (radialDirection y) : ℂ) := by
      simp only [radialExtension, smul_sub, sub_smul]
      abel
    rw [dist_eq_norm, heq]
    calc
      _ ≤ ‖‖x‖ • ((F (radialDirection x) : ℂ) - (F (radialDirection y) : ℂ))‖ +
          ‖(‖x‖ - ‖y‖) • (F (radialDirection y) : ℂ)‖ := norm_add_le _ _
      _ = ‖x‖ * _root_.Dist.dist (F (radialDirection x)) (F (radialDirection y)) + |‖x‖ - ‖y‖| := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hxpos, Circle.norm_coe, mul_one]
        rw [Real.norm_eq_abs]
        have hd : _root_.Dist.dist (F (radialDirection x)) (F (radialDirection y)) =
            ‖(F (radialDirection x) : ℂ) - (F (radialDirection y) : ℂ)‖ :=
          Complex.dist_eq _ _
        rw [hd]
      _ ≤ ‖x‖ * ((L : ℝ) * ((2 / ‖x‖) * _root_.Dist.dist x y)) + _root_.Dist.dist x y := by
        apply add_le_add (mul_le_mul_of_nonneg_left hangular hxpos.le)
        simpa only [← dist_eq_norm] using hnormdiff
      _ = _ := by field_simp
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h : _root_.Dist.dist (radialExtension F x) (radialExtension F y) ≤ (2 * (L : ℝ) + 1) * _root_.Dist.dist x y := by
    by_cases hxy : ‖x‖ ≤ ‖y‖
    · exact hordered x y hxy
    · simpa only [dist_comm] using hordered y x (le_of_not_ge hxy)
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialExtension_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialExtension_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialExtension_lipschitz ``Submission.DifferentialGeometry.Topology.radialExtension_lipschitz

open _root_.MeasureTheory in
theorem measurable_coe_radialDirection :
    Measurable (fun z : ℂ => (radialDirection z : ℂ)) := by
  classical
  have heq : (fun z : ℂ => (radialDirection z : ℂ)) =
      fun z => if z = 0 then 1 else ‖z‖⁻¹ • z := by
    funext z
    by_cases hz : z = 0 <;> simp [radialDirection, hz, NormedSpace.normalize]
  rw [heq]
  exact Measurable.ite (_root_.MeasurableSingletonClass.measurableSet_singleton (0 : ℂ)) measurable_const
    (measurable_norm.inv.smul measurable_id)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.measurable_coe_radialDirection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.measurable_coe_radialDirection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.measurable_coe_radialDirection ``Submission.DifferentialGeometry.Topology.measurable_coe_radialDirection

end DifferentialGeometry.Topology
