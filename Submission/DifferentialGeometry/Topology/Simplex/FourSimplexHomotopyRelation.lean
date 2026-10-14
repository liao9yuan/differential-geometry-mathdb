import Submission.DifferentialGeometry.Topology.Simplex.FourSimplexCubeRelation
import Submission.DifferentialGeometry.Topology.Simplex.TetrahedronGenLoop

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.ContinuousMap
open scoped _root_.unitInterval

namespace DifferentialGeometry.Simplex

theorem map_succAbove_mem_skeleton_of_mem_boundary {n : ℕ} (i : Fin (n + 3))
    {p : stdSimplex ℝ (Fin (n + 2))} (hp : p ∈ boundary (Fin (n + 2))) :
    stdSimplex.map i.succAbove p ∈ skeleton (Fin (n + 3)) n := by
  obtain ⟨j, hj⟩ := hp
  let s : Finset (Fin (n + 3)) := Finset.univ.erase i
  have hsc : s.card ≤ n + 2 := by simp [s]
  have hps : stdSimplex.map i.succAbove p ∈ supportFace s := by
    intro k hk
    by_cases hki : k = i
    · subst k
      exact map_succAbove_apply_pivot i p
    · have hkis : k ∈ s := by simp [s, hki]
      exact (hk hkis).elim
  exact mem_skeleton_of_zero_coordinate hsc hps
    (Finset.mem_erase.mpr ⟨Fin.succAbove_ne i j, Finset.mem_univ _⟩)
    ((map_succAbove_apply_image i p j).trans hj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.map_succAbove_mem_skeleton_of_mem_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.map_succAbove_mem_skeleton_of_mem_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.map_succAbove_mem_skeleton_of_mem_boundary ``Submission.DifferentialGeometry.Simplex.map_succAbove_mem_skeleton_of_mem_boundary

end DifferentialGeometry.Simplex

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x : X}

private def fourSimplexFace (F : C(stdSimplex ℝ (Fin 5), X)) (i : Fin 5) :
    C(stdSimplex ℝ (Fin 4), X) :=
  F.comp ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.fourSimplexFace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.fourSimplexFace target :: scope.openDecls } }

private theorem fourSimplexFace_boundary (F : C(stdSimplex ℝ (Fin 5), X))
    (hF : ∀ p ∈ Simplex.skeleton (Fin 5) 2, F p = x) (i : Fin 5) :
    ∀ p ∈ Simplex.boundary (Fin 4), fourSimplexFace F i p = x := by
  intro p hp
  exact hF _ (Simplex.map_succAbove_mem_skeleton_of_mem_boundary i hp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.fourSimplexFace_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.fourSimplexFace_boundary target :: scope.openDecls } }

private theorem fourSimplexCubeFace_first_one (F : C(stdSimplex ℝ (Fin 5), X))
    (hF : ∀ p ∈ Simplex.skeleton (Fin 5) 2, F p = x) :
    fourSimplexCubeFace F hF 0 1 (Or.inr rfl) =
      Simplex.tetrahedronConeGenLoop (fourSimplexFace F 0) x
        (fourSimplexFace_boundary F hF 0) := by
  ext v
  rw [fourSimplexCubeFace_apply]
  change F (Simplex.fourSimplexJoin (v 2, 1, v 1, v 0)) =
    F (stdSimplex.map (0 : Fin 5).succAbove (Simplex.tetrahedronCone (v 2, v 1, v 0)))
  rw [Simplex.fourSimplexJoin_second_one]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.fourSimplexCubeFace_first_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.fourSimplexCubeFace_first_one target :: scope.openDecls } }

private theorem fourSimplexCubeFace_first_zero (F : C(stdSimplex ℝ (Fin 5), X))
    (hF : ∀ p ∈ Simplex.skeleton (Fin 5) 2, F p = x) :
    fourSimplexCubeFace F hF 0 0 (Or.inl rfl) =
      Simplex.tetrahedronConeGenLoop (fourSimplexFace F 1) x
        (fourSimplexFace_boundary F hF 1) := by
  ext v
  rw [fourSimplexCubeFace_apply]
  change F (Simplex.fourSimplexJoin (v 2, 0, v 1, v 0)) =
    F (stdSimplex.map (1 : Fin 5).succAbove (Simplex.tetrahedronCone (v 2, v 1, v 0)))
  rw [Simplex.fourSimplexJoin_second_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.fourSimplexCubeFace_first_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.fourSimplexCubeFace_first_zero target :: scope.openDecls } }

private theorem fourSimplexCubeFace_second_one (F : C(stdSimplex ℝ (Fin 5), X))
    (hF : ∀ p ∈ Simplex.skeleton (Fin 5) 2, F p = x) :
    fourSimplexCubeFace F hF 1 1 (Or.inr rfl) =
      Simplex.tetrahedronGenLoop (fourSimplexFace F 2) x
        (fourSimplexFace_boundary F hF 2) := by
  ext v
  rw [fourSimplexCubeFace_apply]
  change F (Simplex.fourSimplexJoin (v 2, v 1, 1, v 0)) =
    F (stdSimplex.map (2 : Fin 5).succAbove (Simplex.tetrahedronJoin (v 2, v 1, v 0)))
  rw [Simplex.fourSimplexJoin_third_one]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.fourSimplexCubeFace_second_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.fourSimplexCubeFace_second_one target :: scope.openDecls } }

private theorem fourSimplexCubeFace_third_one (F : C(stdSimplex ℝ (Fin 5), X))
    (hF : ∀ p ∈ Simplex.skeleton (Fin 5) 2, F p = x) :
    fourSimplexCubeFace F hF 2 1 (Or.inr rfl) =
      Simplex.tetrahedronGenLoop (fourSimplexFace F 3) x
        (fourSimplexFace_boundary F hF 3) := by
  ext v
  rw [fourSimplexCubeFace_apply]
  change F (Simplex.fourSimplexJoin (v 2, v 1, v 0, 1)) =
    F (stdSimplex.map (3 : Fin 5).succAbove (Simplex.tetrahedronJoin (v 2, v 1, v 0)))
  rw [Simplex.fourSimplexJoin_fourth_one]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.fourSimplexCubeFace_third_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.fourSimplexCubeFace_third_one target :: scope.openDecls } }

private theorem fourSimplexCubeFace_third_zero (F : C(stdSimplex ℝ (Fin 5), X))
    (hF : ∀ p ∈ Simplex.skeleton (Fin 5) 2, F p = x) :
    fourSimplexCubeFace F hF 2 0 (Or.inl rfl) =
      Simplex.tetrahedronGenLoop (fourSimplexFace F 4) x
        (fourSimplexFace_boundary F hF 4) := by
  ext v
  rw [fourSimplexCubeFace_apply]
  change F (Simplex.fourSimplexJoin (v 2, v 1, v 0, 0)) =
    F (stdSimplex.map (4 : Fin 5).succAbove (Simplex.tetrahedronJoin (v 2, v 1, v 0)))
  rw [Simplex.fourSimplexJoin_fourth_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.fourSimplexCubeFace_third_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.fourSimplexCubeFace_third_zero target :: scope.openDecls } }

private theorem five_face_group_identity {A : Type*} [CommGroup A]
    (a b c d e : A) (h : a⁻¹ * d = b⁻¹ * c * e) : a * c * e = b * d := by
  have h' := congrArg (fun z => a * b * z) h
  calc
    a * c * e = a * b * (b⁻¹ * c * e) := by simp [mul_assoc]
    _ = a * b * (a⁻¹ * d) := h'.symm
    _ = (a * a⁻¹) * (b * d) := by ac_rfl
    _ = b * d := by rw [mul_inv_cancel, one_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.five_face_group_identity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.five_face_group_identity target :: scope.openDecls } }

theorem tetrahedronGenLoop_fourSimplex_face_relation
    (F : C(stdSimplex ℝ (Fin 5), X))
    (hF : ∀ p ∈ Simplex.skeleton (Fin 5) 2, F p = x) :
    let q : Fin 5 → HomotopyGroup (Fin 3) X x := fun i =>
      ⟦Simplex.tetrahedronGenLoop
        (F.comp ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩) x
        (fun p hp => hF (stdSimplex.map i.succAbove p)
          (Simplex.map_succAbove_mem_skeleton_of_mem_boundary i hp))⟧
    q 0 * q 2 * q 4 = q 1 * q 3 := by
  let q : Fin 5 → HomotopyGroup (Fin 3) X x := fun i =>
    ⟦Simplex.tetrahedronGenLoop (fourSimplexFace F i) x (fourSimplexFace_boundary F hF i)⟧
  change q 0 * q 2 * q 4 = q 1 * q 3
  have h := homotopyGroup_fourSimplexCubeFace_relation F hF
  dsimp only at h
  rw [fourSimplexCubeFace_first_one, fourSimplexCubeFace_first_zero,
    fourSimplexCubeFace_second_one, fourSimplexCubeFace_third_one,
    fourSimplexCubeFace_third_zero, Simplex.tetrahedronConeGenLoop_class_eq_inv,
    Simplex.tetrahedronConeGenLoop_class_eq_inv] at h
  exact five_face_group_identity (q 0) (q 1) (q 2) (q 3) (q 4) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.tetrahedronGenLoop_fourSimplex_face_relation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.tetrahedronGenLoop_fourSimplex_face_relation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.tetrahedronGenLoop_fourSimplex_face_relation ``Submission.DifferentialGeometry.Topology.tetrahedronGenLoop_fourSimplex_face_relation

end DifferentialGeometry.Topology
