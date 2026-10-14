import Submission.DifferentialGeometry.Topology.Simplex.FourSimplexJoin
import Submission.DifferentialGeometry.Topology.Simplex.Skeleton

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.unitInterval

namespace DifferentialGeometry.Simplex

private theorem mem_two_skeleton_of_two_zero_coordinates {p : stdSimplex ℝ (Fin 5)}
    (i j : Fin 5) (hij : i ≠ j) (hi : p i = 0) (hj : p j = 0) : p ∈ skeleton (Fin 5) 2 := by
  let s : Finset (Fin 5) := Finset.univ.erase i
  have hsc : s.card ≤ 4 := by simp [s]
  have hps : p ∈ supportFace s := by
    intro k hk
    by_cases hki : k = i
    · simpa [hki] using hi
    · have hkis : k ∈ s := by simp [s, hki]
      exact (hk hkis).elim
  have hmem : p ∈ skeleton (Fin 5) 2 :=
    mem_skeleton_of_zero_coordinate hsc hps (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩) hj
  exact hmem

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.mem_two_skeleton_of_two_zero_coordinates
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.mem_two_skeleton_of_two_zero_coordinates target :: scope.openDecls } }

theorem fourSimplexJoin_first_zero_mem_skeleton (t u v : unitInterval) :
    fourSimplexJoin (0, t, u, v) ∈ skeleton (Fin 5) 2 := by
  apply mem_two_skeleton_of_two_zero_coordinates 2 3 (by decide)
  · change (fourSimplexJoin (0, t, u, v)).val 2 = 0
    simp [fourSimplexJoin]
  · change (fourSimplexJoin (0, t, u, v)).val 3 = 0
    simp [fourSimplexJoin]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.fourSimplexJoin_first_zero_mem_skeleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.fourSimplexJoin_first_zero_mem_skeleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.fourSimplexJoin_first_zero_mem_skeleton ``Submission.DifferentialGeometry.Simplex.fourSimplexJoin_first_zero_mem_skeleton

theorem fourSimplexJoin_first_one_mem_skeleton (t u v : unitInterval) :
    fourSimplexJoin (1, t, u, v) ∈ skeleton (Fin 5) 2 := by
  apply mem_two_skeleton_of_two_zero_coordinates 0 1 (by decide)
  · change (fourSimplexJoin (1, t, u, v)).val 0 = 0
    simp [fourSimplexJoin]
  · change (fourSimplexJoin (1, t, u, v)).val 1 = 0
    simp [fourSimplexJoin]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.fourSimplexJoin_first_one_mem_skeleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.fourSimplexJoin_first_one_mem_skeleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.fourSimplexJoin_first_one_mem_skeleton ``Submission.DifferentialGeometry.Simplex.fourSimplexJoin_first_one_mem_skeleton

theorem fourSimplexJoin_third_zero_mem_skeleton (s t v : unitInterval) :
    fourSimplexJoin (s, t, 0, v) ∈ skeleton (Fin 5) 2 := by
  apply mem_two_skeleton_of_two_zero_coordinates 3 4 (by decide)
  · change (fourSimplexJoin (s, t, 0, v)).val 3 = 0
    simp [fourSimplexJoin]
  · change (fourSimplexJoin (s, t, 0, v)).val 4 = 0
    simp [fourSimplexJoin]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.fourSimplexJoin_third_zero_mem_skeleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.fourSimplexJoin_third_zero_mem_skeleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.fourSimplexJoin_third_zero_mem_skeleton ``Submission.DifferentialGeometry.Simplex.fourSimplexJoin_third_zero_mem_skeleton

theorem fourSimplexJoin_outer_edge_mem_skeleton (s t u v : unitInterval)
    (h : ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) ∨
      ((t = 0 ∨ t = 1) ∧ (v = 0 ∨ v = 1)) ∨
      ((u = 0 ∨ u = 1) ∧ (v = 0 ∨ v = 1))) :
    fourSimplexJoin (s, t, u, v) ∈ skeleton (Fin 5) 2 := by
  rcases h with ⟨(rfl | rfl), (rfl | rfl)⟩ |
    ⟨(rfl | rfl), (rfl | rfl)⟩ | ⟨(rfl | rfl), (rfl | rfl)⟩
  · exact fourSimplexJoin_third_zero_mem_skeleton s 0 v
  · apply mem_two_skeleton_of_two_zero_coordinates 1 2 (by decide)
    · change (fourSimplexJoin (s, 0, 1, v)).val 1 = 0
      simp [fourSimplexJoin]
    · change (fourSimplexJoin (s, 0, 1, v)).val 2 = 0
      simp [fourSimplexJoin]
  · exact fourSimplexJoin_third_zero_mem_skeleton s 1 v
  · apply mem_two_skeleton_of_two_zero_coordinates 0 2 (by decide)
    · change (fourSimplexJoin (s, 1, 1, v)).val 0 = 0
      simp [fourSimplexJoin]
    · change (fourSimplexJoin (s, 1, 1, v)).val 2 = 0
      simp [fourSimplexJoin]
  · apply mem_two_skeleton_of_two_zero_coordinates 1 4 (by decide)
    · change (fourSimplexJoin (s, 0, u, 0)).val 1 = 0
      simp [fourSimplexJoin]
    · change (fourSimplexJoin (s, 0, u, 0)).val 4 = 0
      simp [fourSimplexJoin]
  · apply mem_two_skeleton_of_two_zero_coordinates 1 3 (by decide)
    · change (fourSimplexJoin (s, 0, u, 1)).val 1 = 0
      simp [fourSimplexJoin]
    · change (fourSimplexJoin (s, 0, u, 1)).val 3 = 0
      simp [fourSimplexJoin]
  · apply mem_two_skeleton_of_two_zero_coordinates 0 4 (by decide)
    · change (fourSimplexJoin (s, 1, u, 0)).val 0 = 0
      simp [fourSimplexJoin]
    · change (fourSimplexJoin (s, 1, u, 0)).val 4 = 0
      simp [fourSimplexJoin]
  · apply mem_two_skeleton_of_two_zero_coordinates 0 3 (by decide)
    · change (fourSimplexJoin (s, 1, u, 1)).val 0 = 0
      simp [fourSimplexJoin]
    · change (fourSimplexJoin (s, 1, u, 1)).val 3 = 0
      simp [fourSimplexJoin]
  · exact fourSimplexJoin_third_zero_mem_skeleton s t 0
  · exact fourSimplexJoin_third_zero_mem_skeleton s t 1
  · apply mem_two_skeleton_of_two_zero_coordinates 2 4 (by decide)
    · change (fourSimplexJoin (s, t, 1, 0)).val 2 = 0
      simp [fourSimplexJoin]
    · change (fourSimplexJoin (s, t, 1, 0)).val 4 = 0
      simp [fourSimplexJoin]
  · apply mem_two_skeleton_of_two_zero_coordinates 2 3 (by decide)
    · change (fourSimplexJoin (s, t, 1, 1)).val 2 = 0
      simp [fourSimplexJoin]
    · change (fourSimplexJoin (s, t, 1, 1)).val 3 = 0
      simp [fourSimplexJoin]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.fourSimplexJoin_outer_edge_mem_skeleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.fourSimplexJoin_outer_edge_mem_skeleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.fourSimplexJoin_outer_edge_mem_skeleton ``Submission.DifferentialGeometry.Simplex.fourSimplexJoin_outer_edge_mem_skeleton

end DifferentialGeometry.Simplex
