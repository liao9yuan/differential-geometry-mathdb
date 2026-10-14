import Submission.DifferentialGeometry.Topology.Homotopy.OpenCollapse
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Topology.Order.Monotone

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function
open scoped _root_.Topology

namespace DifferentialGeometry.Topology


def cubeInterior (N : Type*) : Set (N → unitInterval) :=
  {t | ∀ i, 0 < (t i).val ∧ (t i).val < 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeInterior ``Submission.DifferentialGeometry.Topology.cubeInterior


theorem cubeInterior_eq_compl_boundary (N : Type*) : cubeInterior N = (Cube.boundary N)ᶜ := by
  ext t
  constructor
  · intro ht ⟨i, hi⟩
    rcases hi with hi | hi
    · have h := (ht i).1
      rw [hi] at h
      exact (lt_irrefl (0 : ℝ)) h
    · have h := (ht i).2
      rw [hi] at h
      exact (lt_irrefl (1 : ℝ)) h
  · intro ht i
    have h0 : (t i).val ≠ 0 := fun h => ht ⟨i, Or.inl (Subtype.ext h)⟩
    have h1 : (t i).val ≠ 1 := fun h => ht ⟨i, Or.inr (Subtype.ext h)⟩
    exact ⟨lt_of_le_of_ne (t i).property.1 h0.symm, lt_of_le_of_ne (t i).property.2 h1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeInterior_eq_compl_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeInterior_eq_compl_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeInterior_eq_compl_boundary ``Submission.DifferentialGeometry.Topology.cubeInterior_eq_compl_boundary


theorem isOpen_cubeInterior (N : Type*) [Finite N] : IsOpen (cubeInterior N) := by
  have heq : cubeInterior N = ⋂ i : N,
      (fun t : N → unitInterval => (t i).val) ⁻¹' _root_.Set.Ioo (0 : ℝ) 1 := by
    ext t
    simp only [cubeInterior, _root_.Set.mem_ofPred_eq, _root_.Set.mem_iInter, _root_.Set.mem_preimage, _root_.Set.mem_Ioo]
  rw [heq]
  exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage
    (continuous_subtype_val.comp (continuous_apply i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isOpen_cubeInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isOpen_cubeInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isOpen_cubeInterior ``Submission.DifferentialGeometry.Topology.isOpen_cubeInterior


theorem cubeInterior_compl_nonempty (N : Type*) [Nonempty N] : (cubeInterior N)ᶜ.Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  rw [cubeInterior_eq_compl_boundary, compl_compl]
  exact ⟨Classical.arbitrary N, Or.inl rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeInterior_compl_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeInterior_compl_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeInterior_compl_nonempty ``Submission.DifferentialGeometry.Topology.cubeInterior_compl_nonempty


def realOpenUnitIntervalHomeomorph : ℝ ≃ₜ _root_.Set.Ioo (0 : ℝ) 1 :=
  (StrictMono.orderIsoOfSurjective
    (fun r : ℝ => (⟨Real.sigmoid r, Real.sigmoid_pos r, Real.sigmoid_lt_one r⟩ : _root_.Set.Ioo (0 : ℝ) 1))
    (fun a b hab => Real.sigmoid_strictMono hab)
    (by
      intro t
      have ht : t.val ∈ _root_.Set.range Real.sigmoid := by
        rw [Real.range_sigmoid]
        exact t.property
      obtain ⟨r, hr⟩ := ht
      exact ⟨r, Subtype.ext hr⟩)).toHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.realOpenUnitIntervalHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.realOpenUnitIntervalHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.realOpenUnitIntervalHomeomorph ``Submission.DifferentialGeometry.Topology.realOpenUnitIntervalHomeomorph



def euclideanCubeInteriorHomeomorph (N : Type*) : (N → ℝ) ≃ₜ cubeInterior N where
  toFun v := ⟨fun i => ⟨(realOpenUnitIntervalHomeomorph (v i)).val,
      (realOpenUnitIntervalHomeomorph (v i)).property.1.le,
      (realOpenUnitIntervalHomeomorph (v i)).property.2.le⟩,
    fun i => (realOpenUnitIntervalHomeomorph (v i)).property⟩
  invFun t i := realOpenUnitIntervalHomeomorph.symm ⟨(t.val i).val, t.property i⟩
  left_inv v := by
    funext i
    exact realOpenUnitIntervalHomeomorph.symm_apply_apply (v i)
  right_inv t := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    change (realOpenUnitIntervalHomeomorph
      (realOpenUnitIntervalHomeomorph.symm ⟨(t.val i).val, t.property i⟩)).val = (t.val i).val
    exact congrArg (fun z : _root_.Set.Ioo (0 : ℝ) 1 => z.val) (realOpenUnitIntervalHomeomorph.apply_symm_apply
      ⟨(t.val i).val, t.property i⟩)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_subtype_val.comp
      (realOpenUnitIntervalHomeomorph.continuous.comp (continuous_apply i))).subtype_mk _
  continuous_invFun := by
    apply continuous_pi
    intro i
    exact realOpenUnitIntervalHomeomorph.symm.continuous.comp
      ((continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val)).subtype_mk _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.euclideanCubeInteriorHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.euclideanCubeInteriorHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.euclideanCubeInteriorHomeomorph ``Submission.DifferentialGeometry.Topology.euclideanCubeInteriorHomeomorph

end DifferentialGeometry.Topology
