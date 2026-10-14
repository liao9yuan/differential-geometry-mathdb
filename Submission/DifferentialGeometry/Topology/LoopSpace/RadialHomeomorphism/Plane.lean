import Submission.DifferentialGeometry.Topology.LoopSpace.RadialExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.NNReal

namespace DifferentialGeometry.Topology

def radialHomeomorph (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) : ℂ ≃ₜ ℂ where
  toFun := radialExtension κ
  invFun := radialExtension κ.symm
  left_inv z := by
    rw [← radialExtension_comp]
    have heq : (κ.symm ∘ κ : Circle → Circle) = id := funext κ.symm_apply_apply
    rw [heq, radialExtension_id]
  right_inv z := by
    rw [← radialExtension_comp]
    have heq : (κ ∘ κ.symm : Circle → Circle) = id := funext κ.apply_symm_apply
    rw [heq, radialExtension_id]
  continuous_toFun := (radialExtension_lipschitz hκ).continuous
  continuous_invFun := (radialExtension_lipschitz hκi).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialHomeomorph ``Submission.DifferentialGeometry.Topology.radialHomeomorph

theorem radialHomeomorph_apply (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) (z : ℂ) :
    radialHomeomorph κ hκ hκi z = radialExtension κ z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialHomeomorph_apply ``Submission.DifferentialGeometry.Topology.radialHomeomorph_apply

theorem radialHomeomorph_symm_apply (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) (z : ℂ) :
    (radialHomeomorph κ hκ hκi).symm z = radialExtension κ.symm z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialHomeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialHomeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialHomeomorph_symm_apply ``Submission.DifferentialGeometry.Topology.radialHomeomorph_symm_apply

theorem radialHomeomorph_lipschitz (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) :
    LipschitzWith (2 * K + 1) (radialHomeomorph κ hκ hκi) :=
  radialExtension_lipschitz hκ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialHomeomorph_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialHomeomorph_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialHomeomorph_lipschitz ``Submission.DifferentialGeometry.Topology.radialHomeomorph_lipschitz

theorem radialHomeomorph_symm_lipschitz (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) :
    LipschitzWith (2 * L + 1) (radialHomeomorph κ hκ hκi).symm :=
  radialExtension_lipschitz hκi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialHomeomorph_symm_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialHomeomorph_symm_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialHomeomorph_symm_lipschitz ``Submission.DifferentialGeometry.Topology.radialHomeomorph_symm_lipschitz

theorem radialHomeomorph_norm (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) (z : ℂ) :
    ‖radialHomeomorph κ hκ hκi z‖ = ‖z‖ := radialExtension_norm κ z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialHomeomorph_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialHomeomorph_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialHomeomorph_norm ``Submission.DifferentialGeometry.Topology.radialHomeomorph_norm

theorem radialHomeomorph_circle (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) (z : Circle) :
    radialHomeomorph κ hκ hκi z = (κ z : ℂ) := radialExtension_circle κ z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialHomeomorph_circle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialHomeomorph_circle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialHomeomorph_circle ``Submission.DifferentialGeometry.Topology.radialHomeomorph_circle

theorem radialHomeomorph_image_closedBall (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) (r : ℝ) :
    radialHomeomorph κ hκ hκi '' _root_.Metric.closedBall (0 : ℂ) r = _root_.Metric.closedBall (0 : ℂ) r := by
  let e := radialHomeomorph κ hκ hκi
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [_root_.Metric.mem_closedBall, dist_zero_right, radialHomeomorph_norm] using hx
  · intro hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    simpa only [_root_.Metric.mem_closedBall, dist_zero_right, e, radialHomeomorph_symm_apply,
      radialExtension_norm] using hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialHomeomorph_image_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialHomeomorph_image_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialHomeomorph_image_closedBall ``Submission.DifferentialGeometry.Topology.radialHomeomorph_image_closedBall

theorem radialHomeomorph_image_ball (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) (r : ℝ) :
    radialHomeomorph κ hκ hκi '' _root_.Metric.ball (0 : ℂ) r = _root_.Metric.ball (0 : ℂ) r := by
  let e := radialHomeomorph κ hκ hκi
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [_root_.Metric.mem_ball, dist_zero_right, radialHomeomorph_norm] using hx
  · intro hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    simpa only [_root_.Metric.mem_ball, dist_zero_right, e, radialHomeomorph_symm_apply,
      radialExtension_norm] using hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialHomeomorph_image_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialHomeomorph_image_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialHomeomorph_image_ball ``Submission.DifferentialGeometry.Topology.radialHomeomorph_image_ball

theorem radialHomeomorph_image_sphere (κ : Circle ≃ₜ Circle) {K L : ℝ≥0}
    (hκ : LipschitzWith K κ) (hκi : LipschitzWith L κ.symm) (r : ℝ) :
    radialHomeomorph κ hκ hκi '' _root_.Metric.sphere (0 : ℂ) r = _root_.Metric.sphere (0 : ℂ) r := by
  let e := radialHomeomorph κ hκ hκi
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [_root_.Metric.mem_sphere, dist_zero_right, radialHomeomorph_norm] using hx
  · intro hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    simpa only [_root_.Metric.mem_sphere, dist_zero_right, e, radialHomeomorph_symm_apply,
      radialExtension_norm] using hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.radialHomeomorph_image_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.radialHomeomorph_image_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.radialHomeomorph_image_sphere ``Submission.DifferentialGeometry.Topology.radialHomeomorph_image_sphere

end DifferentialGeometry.Topology

end
