import Submission.DifferentialGeometry.Analysis.Convex.ProperConeFace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set
open scoped _root_.RealInnerProductSpace

namespace DifferentialGeometry.Analysis.InnerProductSpace

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

noncomputable def ProperCone.innerDualZeroFace
    (C : ProperCone ℝ E) (y : E) : ProperCone ℝ E :=
  DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace C (innerSL ℝ y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace ``Submission.DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace

theorem ProperCone.innerDualZeroFace_eq_dualZeroFace
    (C : ProperCone ℝ E) (y : E) :
    ProperCone.innerDualZeroFace C y =
      DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace C (innerSL ℝ y) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_eq_dualZeroFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_eq_dualZeroFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_eq_dualZeroFace ``Submission.DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_eq_dualZeroFace

@[simp]
theorem ProperCone.mem_innerDualZeroFace
    {C : ProperCone ℝ E} {x y : E} :
    x ∈ ProperCone.innerDualZeroFace C y ↔ x ∈ C ∧ ⟪x, y⟫ = 0 := by
  simp [ProperCone.innerDualZeroFace, real_inner_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.mem_innerDualZeroFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.mem_innerDualZeroFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.mem_innerDualZeroFace ``Submission.DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.mem_innerDualZeroFace

@[simp]
theorem ProperCone.innerDualZeroFace_zero (C : ProperCone ℝ E) :
    ProperCone.innerDualZeroFace C 0 = C := by
  ext x
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_zero ``Submission.DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_zero

theorem ProperCone.innerDualZeroFace_le
    (C : ProperCone ℝ E) (y : E) :
    ProperCone.innerDualZeroFace C y ≤ C := by
  intro x hx
  exact (ProperCone.mem_innerDualZeroFace.mp hx).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_le ``Submission.DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_le

theorem ProperCone.innerDualZeroFace_isExposed
    [CompleteSpace E]
    (C : ProperCone ℝ E) {y : E}
    (hy : y ∈ ProperCone.innerDual (C : Set E)) :
    IsExposed ℝ (C : Set E) (ProperCone.innerDualZeroFace C y : Set E) := by
  intro _
  refine ⟨-(innerSL ℝ y), Set.ext fun x ↦ ?_⟩
  constructor
  · intro hx
    obtain ⟨hxC, hxy⟩ := ProperCone.mem_innerDualZeroFace.mp hx
    refine ⟨hxC, fun z hz ↦ ?_⟩
    have hznonneg : 0 ≤ ⟪z, y⟫ := hy hz
    simp only [neg_apply, innerSL_apply_apply]
    rw [real_inner_comm z y, real_inner_comm x y, hxy]
    simpa using neg_nonpos.mpr hznonneg
  · rintro ⟨hxC, hxmax⟩
    have hxnonneg : 0 ≤ ⟪x, y⟫ := hy hxC
    have hxmax0 := hxmax 0 C.zero_mem
    have hxnonpos : ⟪x, y⟫ ≤ 0 := by
      simpa [real_inner_comm] using hxmax0
    exact ProperCone.mem_innerDualZeroFace.mpr
      ⟨hxC, le_antisymm hxnonpos hxnonneg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_isExposed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_isExposed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_isExposed ``Submission.DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_isExposed

theorem ProperCone.innerDualZeroFace_isExtreme
    [CompleteSpace E]
    (C : ProperCone ℝ E) {y : E}
    (hy : y ∈ ProperCone.innerDual (C : Set E)) :
    IsExtreme ℝ (C : Set E) (ProperCone.innerDualZeroFace C y : Set E) :=
  (ProperCone.innerDualZeroFace_isExposed C hy).isExtreme

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_isExtreme then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_isExtreme"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_isExtreme ``Submission.DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_isExtreme

@[simp]
theorem ProperCone.innerDualZeroFace_map_linearIsometryEquiv
    (C : ProperCone ℝ E) (e : E ≃ₗᵢ[ℝ] F) (y : E) :
    (ProperCone.innerDualZeroFace C y).map
        e.toContinuousLinearEquiv.toContinuousLinearMap =
      ProperCone.innerDualZeroFace
        (C.map e.toContinuousLinearEquiv.toContinuousLinearMap) (e y) := by
  apply ProperCone.ext
  intro z
  rw [ProperCone.mem_map_continuousLinearEquiv_iff]
  rw [ProperCone.mem_innerDualZeroFace]
  rw [ProperCone.mem_innerDualZeroFace]
  rw [ProperCone.mem_map_continuousLinearEquiv_iff]
  constructor
  · rintro ⟨hzC, hzy⟩
    refine ⟨hzC, ?_⟩
    have hinner : ⟪z, e y⟫ = ⟪e.symm z, y⟫ := by
      simpa using e.inner_map_map (e.symm z) y
    exact hinner.trans hzy
  · rintro ⟨hzC, hzy⟩
    refine ⟨hzC, ?_⟩
    have hinner : ⟪z, e y⟫ = ⟪e.symm z, y⟫ := by
      simpa using e.inner_map_map (e.symm z) y
    exact hinner.symm.trans hzy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_map_linearIsometryEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_map_linearIsometryEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_map_linearIsometryEquiv ``Submission.DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.innerDualZeroFace_map_linearIsometryEquiv

end

end DifferentialGeometry.Analysis.InnerProductSpace
