import Submission.DifferentialGeometry.Analysis.InnerProductSpace.ProperConeIsometry
import Mathlib.Analysis.Convex.Exposed

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set

namespace DifferentialGeometry.Analysis.Convex

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [ContinuousAdd E] [Module ℝ E]
  [ContinuousConstSMul ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [ContinuousAdd F] [Module ℝ F]
  [ContinuousConstSMul ℝ F]

def ProperCone.IsDualElement
    (C : ProperCone ℝ E) (phi : StrongDual ℝ E) : Prop :=
  ∀ x ∈ C, 0 ≤ phi x

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.Convex.ProperCone
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Convex.ProperCone.IsDualElement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Convex.ProperCone.IsDualElement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Convex.ProperCone.IsDualElement ``Submission.DifferentialGeometry.Analysis.Convex.ProperCone.IsDualElement

omit [ContinuousAdd E] [ContinuousConstSMul ℝ E] in
@[simp]
theorem ProperCone.isDualElement_iff
    {C : ProperCone ℝ E} {phi : StrongDual ℝ E} :
    ProperCone.IsDualElement C phi ↔ ∀ x ∈ C, 0 ≤ phi x :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Convex.ProperCone.isDualElement_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Convex.ProperCone.isDualElement_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Convex.ProperCone.isDualElement_iff ``Submission.DifferentialGeometry.Analysis.Convex.ProperCone.isDualElement_iff

noncomputable def ProperCone.dualZeroFace
    (C : ProperCone ℝ E) (phi : StrongDual ℝ E) : ProperCone ℝ E :=
  C ⊓ (⊥ : ProperCone ℝ ℝ).comap phi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace ``Submission.DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace

omit [ContinuousAdd E] [ContinuousConstSMul ℝ E] in
@[simp]
theorem ProperCone.mem_dualZeroFace
    {C : ProperCone ℝ E} {phi : StrongDual ℝ E} {x : E} :
    x ∈ ProperCone.dualZeroFace C phi ↔ x ∈ C ∧ phi x = 0 := by
  simp [ProperCone.dualZeroFace]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Convex.ProperCone.mem_dualZeroFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Convex.ProperCone.mem_dualZeroFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Convex.ProperCone.mem_dualZeroFace ``Submission.DifferentialGeometry.Analysis.Convex.ProperCone.mem_dualZeroFace

omit [ContinuousAdd E] [ContinuousConstSMul ℝ E] in
@[simp]
theorem ProperCone.dualZeroFace_zero (C : ProperCone ℝ E) :
    ProperCone.dualZeroFace C 0 = C := by
  ext x
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_zero ``Submission.DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_zero

omit [ContinuousAdd E] [ContinuousConstSMul ℝ E] in
theorem ProperCone.dualZeroFace_le
    (C : ProperCone ℝ E) (phi : StrongDual ℝ E) :
    ProperCone.dualZeroFace C phi ≤ C := by
  intro x hx
  exact (ProperCone.mem_dualZeroFace.mp hx).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_le ``Submission.DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_le

omit [ContinuousAdd E] [ContinuousConstSMul ℝ E] in
theorem ProperCone.dualZeroFace_isExposed
    (C : ProperCone ℝ E) {phi : StrongDual ℝ E}
    (hphi : ProperCone.IsDualElement C phi) :
    IsExposed ℝ (C : Set E) (ProperCone.dualZeroFace C phi : Set E) := by
  intro _
  refine ⟨-phi, Set.ext fun x ↦ ?_⟩
  constructor
  · intro hx
    obtain ⟨hxC, hphix⟩ := ProperCone.mem_dualZeroFace.mp hx
    refine ⟨hxC, fun z hz ↦ ?_⟩
    have hznonneg : 0 ≤ phi z := hphi z hz
    simp only [neg_apply]
    rw [hphix]
    simpa using neg_nonpos.mpr hznonneg
  · rintro ⟨hxC, hxmax⟩
    have hxnonneg : 0 ≤ phi x := hphi x hxC
    have hxmax0 := hxmax 0 C.zero_mem
    have hxnonpos : phi x ≤ 0 := by
      simpa using hxmax0
    exact ProperCone.mem_dualZeroFace.mpr
      ⟨hxC, le_antisymm hxnonpos hxnonneg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_isExposed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_isExposed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_isExposed ``Submission.DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_isExposed

omit [ContinuousAdd E] [ContinuousConstSMul ℝ E] in
theorem ProperCone.dualZeroFace_isExtreme
    (C : ProperCone ℝ E) {phi : StrongDual ℝ E}
    (hphi : ProperCone.IsDualElement C phi) :
    IsExtreme ℝ (C : Set E) (ProperCone.dualZeroFace C phi : Set E) :=
  (ProperCone.dualZeroFace_isExposed C hphi).isExtreme

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_isExtreme then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_isExtreme"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_isExtreme ``Submission.DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_isExtreme

omit [ContinuousAdd E] [ContinuousConstSMul ℝ E] in
theorem ProperCone.IsDualElement.comp_symm
    {C : ProperCone ℝ E} {phi : StrongDual ℝ E}
    (hphi : ProperCone.IsDualElement C phi) (e : E ≃L[ℝ] F) :
    ProperCone.IsDualElement (C.map e.toContinuousLinearMap)
      (phi.comp e.symm.toContinuousLinearMap) := by
  intro y hy
  exact hphi (e.symm y)
    ((DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.mem_map_continuousLinearEquiv_iff
      C e y).mp hy)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.Convex.ProperCone.IsDualElement
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Convex.ProperCone.IsDualElement.comp_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Convex.ProperCone.IsDualElement.comp_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Convex.ProperCone.IsDualElement.comp_symm ``Submission.DifferentialGeometry.Analysis.Convex.ProperCone.IsDualElement.comp_symm

omit [ContinuousAdd E] [ContinuousConstSMul ℝ E] in
@[simp]
theorem ProperCone.dualZeroFace_map_continuousLinearEquiv
    (C : ProperCone ℝ E) (e : E ≃L[ℝ] F) (phi : StrongDual ℝ E) :
    (ProperCone.dualZeroFace C phi).map e.toContinuousLinearMap =
      ProperCone.dualZeroFace (C.map e.toContinuousLinearMap)
        (phi.comp e.symm.toContinuousLinearMap) := by
  apply ProperCone.ext
  intro y
  simp only [
    DifferentialGeometry.Analysis.InnerProductSpace.ProperCone.mem_map_continuousLinearEquiv_iff,
    ProperCone.mem_dualZeroFace, ContinuousLinearMap.comp_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_map_continuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_map_continuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_map_continuousLinearEquiv ``Submission.DifferentialGeometry.Analysis.Convex.ProperCone.dualZeroFace_map_continuousLinearEquiv

end DifferentialGeometry.Analysis.Convex
