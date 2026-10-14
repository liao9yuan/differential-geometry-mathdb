import Submission.DifferentialGeometry.Topology.Simplex.BoundaryRetraction
import Mathlib.Topology.Homeomorph.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

universe u v

namespace DifferentialGeometry.Simplex

variable (I : Type v) [Fintype I]

def uliftHomeomorph : ULift.{u} (stdSimplex ℝ I) ≃ₜ stdSimplex ℝ (ULift.{u} I) where
  toFun p := ⟨fun i ↦ p.down.val i.down, ⟨fun i ↦ p.down.property.1 i.down, by
    exact (Equiv.ulift.sum_comp p.down.val).trans p.down.property.2⟩⟩
  invFun q := ULift.up ⟨fun i ↦ q.val (ULift.up i), ⟨fun i ↦ q.property.1 (ULift.up i), by
    exact (Equiv.ulift.symm.sum_comp q.val).trans q.property.2⟩⟩
  left_inv p := rfl
  right_inv q := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_apply i.down).comp (continuous_subtype_val.comp continuous_uliftDown)
  continuous_invFun := by
    apply continuous_uliftUp.comp
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_apply (ULift.up i)).comp continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.uliftHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.uliftHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.uliftHomeomorph ``Submission.DifferentialGeometry.Simplex.uliftHomeomorph


@[simp]
theorem uliftHomeomorph_apply (p : ULift.{u} (stdSimplex ℝ I)) (i : ULift.{u} I) :
    (uliftHomeomorph I p).val i = p.down.val i.down := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.uliftHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.uliftHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.uliftHomeomorph_apply ``Submission.DifferentialGeometry.Simplex.uliftHomeomorph_apply


@[simp]
theorem uliftHomeomorph_symm_apply (q : stdSimplex ℝ (ULift.{u} I)) (i : I) :
    ((uliftHomeomorph I).symm q).down.val i = q.val (ULift.up i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.uliftHomeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.uliftHomeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.uliftHomeomorph_symm_apply ``Submission.DifferentialGeometry.Simplex.uliftHomeomorph_symm_apply


theorem uliftHomeomorph_mem_boundary (p : ULift.{u} (stdSimplex ℝ I)) :
    p.down ∈ boundary I ↔ uliftHomeomorph I p ∈ boundary (ULift.{u} I) := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨ULift.up i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.down, hi⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.uliftHomeomorph_mem_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.uliftHomeomorph_mem_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.uliftHomeomorph_mem_boundary ``Submission.DifferentialGeometry.Simplex.uliftHomeomorph_mem_boundary


def boundaryUliftHomeomorph :
    {p : ULift.{u} (stdSimplex ℝ I) // p.down ∈ boundary I} ≃ₜ boundary (ULift.{u} I) :=
  (uliftHomeomorph I).subtype (uliftHomeomorph_mem_boundary I)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.boundaryUliftHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.boundaryUliftHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.boundaryUliftHomeomorph ``Submission.DifferentialGeometry.Simplex.boundaryUliftHomeomorph


@[simp]
theorem boundaryUliftHomeomorph_val
    (p : {p : ULift.{u} (stdSimplex ℝ I) // p.down ∈ boundary I}) :
    (boundaryUliftHomeomorph I p).val = uliftHomeomorph I p.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.boundaryUliftHomeomorph_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.boundaryUliftHomeomorph_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.boundaryUliftHomeomorph_val ``Submission.DifferentialGeometry.Simplex.boundaryUliftHomeomorph_val

end DifferentialGeometry.Simplex
