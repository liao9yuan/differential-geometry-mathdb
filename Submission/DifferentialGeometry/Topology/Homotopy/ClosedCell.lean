import Submission.DifferentialGeometry.Topology.Attachment.Defs
import Submission.DifferentialGeometry.Topology.Homotopy.DeformationRetract
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.UnitInterval

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.Homotopy

open _root_.ContinuousMap
open _root_.unitInterval

theorem one_minus_norm_mem_Ico {n : ℕ} {x : ClosedCell n}
    (hx : (x : EuclideanSpace ℝ (Fin n)) ≠ 0) :
    1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ∈ Set.Ico (0 : ℝ) 1 := by
  constructor
  · have hle : ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := x.2
    linarith
  · have hlt : 0 < ‖(x : EuclideanSpace ℝ (Fin n))‖ := norm_pos_iff.mpr hx
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.one_minus_norm_mem_Ico then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.one_minus_norm_mem_Ico"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.one_minus_norm_mem_Ico ``Submission.DifferentialGeometry.Topology.Homotopy.one_minus_norm_mem_Ico

def radialStep (n : ℕ) (t : I) (x : ClosedCell n) : ClosedCell n :=
  ⟨(1 - (t : ℝ)) • (x : EuclideanSpace ℝ (Fin n)), by
    have ht₀ : 0 ≤ 1 - (t : ℝ) := unitInterval.one_minus_nonneg t
    have hnorm : ‖(1 - (t : ℝ)) • (x : EuclideanSpace ℝ (Fin n))‖ =
        (1 - (t : ℝ)) * ‖(x : EuclideanSpace ℝ (Fin n))‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht₀]
    rw [hnorm]
    exact mul_le_one₀ (unitInterval.one_minus_le_one t) (norm_nonneg _) x.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.radialStep then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.radialStep"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.radialStep ``Submission.DifferentialGeometry.Topology.Homotopy.radialStep

@[simp]
theorem radialStep_zero (n : ℕ) (x : ClosedCell n) : radialStep n 0 x = x := by
  apply Subtype.ext
  simp [radialStep]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.radialStep_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.radialStep_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.radialStep_zero ``Submission.DifferentialGeometry.Topology.Homotopy.radialStep_zero

@[simp]
theorem radialStep_one (n : ℕ) (x : ClosedCell n) : radialStep n 1 x = closedCellCenter n := by
  apply Subtype.ext
  simp [radialStep, closedCellCenter]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.radialStep_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.radialStep_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.radialStep_one ``Submission.DifferentialGeometry.Topology.Homotopy.radialStep_one

@[simp]
theorem radialStep_center (n : ℕ) (t : I) :
    radialStep n t (closedCellCenter n) = closedCellCenter n := by
  apply Subtype.ext
  simp [radialStep, closedCellCenter]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.radialStep_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.radialStep_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.radialStep_center ``Submission.DifferentialGeometry.Topology.Homotopy.radialStep_center

theorem radialStep_norm (n : ℕ) (t : I) (x : ClosedCell n) :
    ‖(radialStep n t x : EuclideanSpace ℝ (Fin n))‖ =
      (1 - (t : ℝ)) * ‖(x : EuclideanSpace ℝ (Fin n))‖ := by
  simp [radialStep, norm_smul, Real.norm_eq_abs, unitInterval.one_minus_nonneg t]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.radialStep_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.radialStep_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.radialStep_norm ``Submission.DifferentialGeometry.Topology.Homotopy.radialStep_norm

noncomputable def boundaryNormalize {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    CellBoundary n :=
  ⟨‖x‖⁻¹ • x, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.boundaryNormalize then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.boundaryNormalize"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.boundaryNormalize ``Submission.DifferentialGeometry.Topology.Homotopy.boundaryNormalize

@[simp]
theorem norm_boundaryNormalize {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    ‖(boundaryNormalize x hx : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  rw [boundaryNormalize]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.norm_boundaryNormalize then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.norm_boundaryNormalize"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.norm_boundaryNormalize ``Submission.DifferentialGeometry.Topology.Homotopy.norm_boundaryNormalize

theorem smul_boundaryNormalize {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    ‖x‖ • (boundaryNormalize x hx : EuclideanSpace ℝ (Fin n)) = x := by
  rw [boundaryNormalize]
  rw [smul_smul]
  rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx)]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.smul_boundaryNormalize then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.smul_boundaryNormalize"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.smul_boundaryNormalize ``Submission.DifferentialGeometry.Topology.Homotopy.smul_boundaryNormalize

theorem continuous_radialStep (n : ℕ) :
    Continuous (fun p : I × ClosedCell n => radialStep n p.1 p.2) := by
  exact Continuous.subtype_mk
    (((continuous_const.sub continuous_subtype_val).comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd))
    (by
      intro p
      have ht₀ : 0 ≤ 1 - (p.1 : ℝ) := unitInterval.one_minus_nonneg p.1
      have hnorm : ‖(1 - (p.1 : ℝ)) • (p.2 : EuclideanSpace ℝ (Fin n))‖ =
          (1 - (p.1 : ℝ)) * ‖(p.2 : EuclideanSpace ℝ (Fin n))‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht₀]
      simpa using hnorm.trans_le
        (mul_le_one₀ (unitInterval.one_minus_le_one p.1) (norm_nonneg _) p.2.2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.continuous_radialStep then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.continuous_radialStep"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.continuous_radialStep ``Submission.DifferentialGeometry.Topology.Homotopy.continuous_radialStep

theorem continuous_radialStep_left (n : ℕ) (t : I) : Continuous (radialStep n t) :=
  (continuous_radialStep n).comp (continuous_const.prodMk continuous_id)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.continuous_radialStep_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.continuous_radialStep_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.continuous_radialStep_left ``Submission.DifferentialGeometry.Topology.Homotopy.continuous_radialStep_left

def closedCellRetract (n : ℕ) : StrongDeformationRetract ({closedCellCenter n} : Set (ClosedCell n)) where
  retraction := ⟨fun _ => ⟨closedCellCenter n, rfl⟩, continuous_const⟩
  homotopy := {
    toHomotopy := {
      toContinuousMap := ⟨fun p : I × ClosedCell n => radialStep n p.1 p.2, continuous_radialStep n⟩
      map_zero_left := by
        intro x
        simp
      map_one_left := by
        intro x
        simp
    }
    prop' := by
      intro t x hx
      simp at hx
      simp [hx]
  }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.closedCellRetract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.closedCellRetract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.closedCellRetract ``Submission.DifferentialGeometry.Topology.Homotopy.closedCellRetract

@[simp]
theorem closedCellRetract_retraction_apply (n : ℕ) (x : ClosedCell n) :
    ((closedCellRetract n).retraction x : ClosedCell n) = closedCellCenter n := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.closedCellRetract_retraction_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.closedCellRetract_retraction_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.closedCellRetract_retraction_apply ``Submission.DifferentialGeometry.Topology.Homotopy.closedCellRetract_retraction_apply

@[simp]
theorem closedCellRetract_homotopy_apply (n : ℕ) (t : I) (x : ClosedCell n) :
    (closedCellRetract n).homotopy (t, x) = radialStep n t x := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Homotopy.closedCellRetract_homotopy_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Homotopy.closedCellRetract_homotopy_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Homotopy.closedCellRetract_homotopy_apply ``Submission.DifferentialGeometry.Topology.Homotopy.closedCellRetract_homotopy_apply

end DifferentialGeometry.Topology.Homotopy
