import Mathlib.Analysis.Convex.Cone.InnerDual

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.RealInnerProductSpace

namespace DifferentialGeometry.Analysis.InnerProductSpace

section

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [ContinuousAdd E] [Module ℝ E]
  [ContinuousConstSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [ContinuousAdd F] [Module ℝ F]
  [ContinuousConstSMul ℝ F]

omit [ContinuousAdd E] [ContinuousConstSMul ℝ E] in
theorem ProperCone.coe_map_continuousLinearEquiv
    (C : ProperCone ℝ E) (e : E ≃L[ℝ] F) :
    (C.map e.toContinuousLinearMap : Set F) = e '' C := by
  change closure (e '' (C : Set E)) = e '' C
  exact (e.toHomeomorph.isClosedMap (C : Set E) C.isClosed).closure_eq

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.InnerProductSpace.ProperCone
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.coe_map_continuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.coe_map_continuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.coe_map_continuousLinearEquiv ``Submission.DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.coe_map_continuousLinearEquiv

omit [ContinuousAdd E] [ContinuousConstSMul ℝ E] in
theorem ProperCone.mem_map_continuousLinearEquiv_iff
    (C : ProperCone ℝ E) (e : E ≃L[ℝ] F) (y : F) :
    y ∈ C.map e.toContinuousLinearMap ↔ e.symm y ∈ C := by
  change y ∈ (C.map e.toContinuousLinearMap : Set F) ↔ e.symm y ∈ C
  rw [show (C.map e.toContinuousLinearMap : Set F) = e '' C from
    ProperCone.coe_map_continuousLinearEquiv C e]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨e.symm y, hy, e.apply_symm_apply y⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.mem_map_continuousLinearEquiv_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.mem_map_continuousLinearEquiv_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.mem_map_continuousLinearEquiv_iff ``Submission.DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.mem_map_continuousLinearEquiv_iff

@[simp]
theorem ProperCone.map_continuousLinearEquiv_symm
    (C : ProperCone ℝ E) (e : E ≃L[ℝ] F) :
    (C.map e.toContinuousLinearMap).map e.symm.toContinuousLinearMap = C := by
  apply ProperCone.ext
  intro x
  rw [ProperCone.mem_map_continuousLinearEquiv_iff]
  rw [ProperCone.mem_map_continuousLinearEquiv_iff]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.map_continuousLinearEquiv_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.map_continuousLinearEquiv_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.map_continuousLinearEquiv_symm ``Submission.DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.map_continuousLinearEquiv_symm

end

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem LinearIsometryEquiv.mapsTo_innerDual
    (e : E ≃ₗᵢ[ℝ] F) {C : Set E} :
    MapsTo e (ProperCone.innerDual C) (ProperCone.innerDual (e '' C)) := by
  intro y hy
  change ∀ ⦃x : F⦄, x ∈ e '' C → 0 ≤ ⟪x, e y⟫
  rintro _ ⟨x, hx, rfl⟩
  rw [e.inner_map_map]
  with_unfolding_all exact hy hx

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.InnerProductSpace.LinearIsometryEquiv
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.InnerProductSpace.LinearIsometryEquiv.mapsTo_innerDual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.InnerProductSpace.LinearIsometryEquiv.mapsTo_innerDual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.InnerProductSpace.LinearIsometryEquiv.mapsTo_innerDual ``Submission.DifferentialGeometry.Analysis.InnerProductSpace.LinearIsometryEquiv.mapsTo_innerDual

theorem LinearIsometryEquiv.image_innerDual
    (e : E ≃ₗᵢ[ℝ] F) (C : Set E) :
    e '' ProperCone.innerDual C = ProperCone.innerDual (e '' C) := by
  apply Set.Subset.antisymm
  · exact (LinearIsometryEquiv.mapsTo_innerDual e).image_subset
  intro y hy
  have hmap := LinearIsometryEquiv.mapsTo_innerDual e.symm hy
  refine ⟨e.symm y, ?_, by simp⟩
  simpa using hmap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.InnerProductSpace.LinearIsometryEquiv.image_innerDual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.InnerProductSpace.LinearIsometryEquiv.image_innerDual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.InnerProductSpace.LinearIsometryEquiv.image_innerDual ``Submission.DifferentialGeometry.Analysis.InnerProductSpace.LinearIsometryEquiv.image_innerDual

theorem ProperCone.innerDual_map_linearIsometryEquiv
    (C : ProperCone ℝ E) (e : E ≃ₗᵢ[ℝ] F) :
    ProperCone.innerDual
        (C.map e.toContinuousLinearEquiv.toContinuousLinearMap : Set F) =
      (ProperCone.innerDual (C : Set E)).map
        e.toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ProperCone.ext
  intro y
  have hC :
      (C.map e.toContinuousLinearEquiv.toContinuousLinearMap : Set F) =
        e '' (C : Set E) :=
    ProperCone.coe_map_continuousLinearEquiv C e.toContinuousLinearEquiv
  have hdual :
      ((ProperCone.innerDual (C : Set E)).map
          e.toContinuousLinearEquiv.toContinuousLinearMap : Set F) =
        e '' ProperCone.innerDual (C : Set E) :=
    ProperCone.coe_map_continuousLinearEquiv
      (ProperCone.innerDual (C : Set E)) e.toContinuousLinearEquiv
  change y ∈ ProperCone.innerDual
      (C.map e.toContinuousLinearEquiv.toContinuousLinearMap : Set F) ↔
    y ∈ ((ProperCone.innerDual (C : Set E)).map
      e.toContinuousLinearEquiv.toContinuousLinearMap : Set F)
  rw [hC, hdual, LinearIsometryEquiv.image_innerDual]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDual_map_linearIsometryEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDual_map_linearIsometryEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDual_map_linearIsometryEquiv ``Submission.DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDual_map_linearIsometryEquiv

end DifferentialGeometry.Analysis.InnerProductSpace
