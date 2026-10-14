/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.LocalDegree.SphereSuspension.RadialExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Metric _root_.Set

namespace DifferentialGeometry.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem sphereRadialExtension_inverse
    (f : _root_.Metric.sphere (0 : E) 1 ≃ₜ _root_.Metric.sphere (0 : F) 1) (x : E) :
    LocalDegree.sphereRadialExtension (toContinuousMap f.symm)
      (LocalDegree.sphereRadialExtension (toContinuousMap f) x) = x := by
  by_cases hx : x = 0
  · simp [hx]
  have hy : LocalDegree.sphereRadialExtension (toContinuousMap f) x ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [LocalDegree.sphereRadialExtension_norm]
    exact norm_ne_zero_iff.mpr hx
  have hdir : ((homeomorphUnitSphereProd F)
      ⟨LocalDegree.sphereRadialExtension (toContinuousMap f) x, hy⟩).1 =
      f ((homeomorphUnitSphereProd E) ⟨x, hx⟩).1 := by
    apply Subtype.ext
    rw [homeomorphUnitSphereProd_apply_fst_coe]
    change ‖LocalDegree.sphereRadialExtension (toContinuousMap f) x‖⁻¹ •
      LocalDegree.sphereRadialExtension (toContinuousMap f) x = _
    rw [LocalDegree.sphereRadialExtension_norm,
      LocalDegree.sphereRadialExtension_apply_of_ne_zero _ hx]
    simp only [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
    rfl
  rw [LocalDegree.sphereRadialExtension_apply_of_ne_zero _ hy, hdir]
  change ‖LocalDegree.sphereRadialExtension (toContinuousMap f) x‖ •
    (f.symm (f ((homeomorphUnitSphereProd E) ⟨x, hx⟩).1) : E) = x
  rw [f.symm_apply_apply, LocalDegree.sphereRadialExtension_norm,
    homeomorphUnitSphereProd_apply_fst_coe]
  simp only [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.sphereRadialExtension_inverse
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.sphereRadialExtension_inverse target :: scope.openDecls } }

noncomputable def sphereRadialHomeomorph
    (f : _root_.Metric.sphere (0 : E) 1 ≃ₜ _root_.Metric.sphere (0 : F) 1) : E ≃ₜ F where
  toFun := LocalDegree.sphereRadialExtension (toContinuousMap f)
  invFun := LocalDegree.sphereRadialExtension (toContinuousMap f.symm)
  left_inv := sphereRadialExtension_inverse f
  right_inv := sphereRadialExtension_inverse f.symm
  continuous_toFun := (LocalDegree.sphereRadialExtension (toContinuousMap f)).continuous
  continuous_invFun := (LocalDegree.sphereRadialExtension (toContinuousMap f.symm)).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereRadialHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereRadialHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereRadialHomeomorph ``Submission.DifferentialGeometry.Topology.sphereRadialHomeomorph

@[simp]
theorem sphereRadialHomeomorph_symm (f : _root_.Metric.sphere (0 : E) 1 ≃ₜ _root_.Metric.sphere (0 : F) 1) :
    (sphereRadialHomeomorph f).symm = sphereRadialHomeomorph f.symm := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereRadialHomeomorph_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereRadialHomeomorph_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereRadialHomeomorph_symm ``Submission.DifferentialGeometry.Topology.sphereRadialHomeomorph_symm

@[simp]
theorem sphereRadialHomeomorph_zero (f : _root_.Metric.sphere (0 : E) 1 ≃ₜ _root_.Metric.sphere (0 : F) 1) :
    sphereRadialHomeomorph f 0 = 0 := LocalDegree.sphereRadialExtension_zero _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereRadialHomeomorph_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereRadialHomeomorph_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereRadialHomeomorph_zero ``Submission.DifferentialGeometry.Topology.sphereRadialHomeomorph_zero

@[simp]
theorem norm_sphereRadialHomeomorph (f : _root_.Metric.sphere (0 : E) 1 ≃ₜ _root_.Metric.sphere (0 : F) 1) (x : E) :
    ‖sphereRadialHomeomorph f x‖ = ‖x‖ := LocalDegree.sphereRadialExtension_norm _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.norm_sphereRadialHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.norm_sphereRadialHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.norm_sphereRadialHomeomorph ``Submission.DifferentialGeometry.Topology.norm_sphereRadialHomeomorph

@[simp]
theorem sphereRadialHomeomorph_apply_sphere
    (f : _root_.Metric.sphere (0 : E) 1 ≃ₜ _root_.Metric.sphere (0 : F) 1) (x : _root_.Metric.sphere (0 : E) 1) :
    sphereRadialHomeomorph f x = f x := LocalDegree.sphereRadialExtension_sphere _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereRadialHomeomorph_apply_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereRadialHomeomorph_apply_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereRadialHomeomorph_apply_sphere ``Submission.DifferentialGeometry.Topology.sphereRadialHomeomorph_apply_sphere

noncomputable def closedBallHomeomorphExtension
    (f : _root_.Metric.sphere (0 : E) 1 ≃ₜ _root_.Metric.sphere (0 : F) 1) :
    closedBall (0 : E) 1 ≃ₜ _root_.Metric.closedBall (0 : F) 1 :=
  (sphereRadialHomeomorph f).subtype fun x => by
    simp only [_root_.Metric.mem_closedBall, dist_zero_right, norm_sphereRadialHomeomorph]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.closedBallHomeomorphExtension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.closedBallHomeomorphExtension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.closedBallHomeomorphExtension ``Submission.DifferentialGeometry.Topology.closedBallHomeomorphExtension

@[simp]
theorem closedBallHomeomorphExtension_apply_sphere
    (f : _root_.Metric.sphere (0 : E) 1 ≃ₜ _root_.Metric.sphere (0 : F) 1) (x : _root_.Metric.sphere (0 : E) 1) :
    closedBallHomeomorphExtension f ⟨x, _root_.Metric.sphere_subset_closedBall x.property⟩ =
      ⟨f x, _root_.Metric.sphere_subset_closedBall (f x).property⟩ := by
  apply Subtype.ext
  exact sphereRadialHomeomorph_apply_sphere f x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.closedBallHomeomorphExtension_apply_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.closedBallHomeomorphExtension_apply_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.closedBallHomeomorphExtension_apply_sphere ``Submission.DifferentialGeometry.Topology.closedBallHomeomorphExtension_apply_sphere

end DifferentialGeometry.Topology
