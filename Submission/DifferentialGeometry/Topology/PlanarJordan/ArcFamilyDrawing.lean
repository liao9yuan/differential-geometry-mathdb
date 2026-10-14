/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.External.Schoenflies.Graph.Drawing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.Graph _root_.Submission.Graph

namespace Graph
open _root_.Graph

open _root_.Graph in
def curveGraph {α β : Type*} (f : β → ℝ → α) (W : Set α) : Graph α β where
  vertexSet := W ∪ _root_.Set.range (fun d => f d 0) ∪ _root_.Set.range (fun d => f d 1)
  edgeSet := _root_.Set.univ
  IsLink d x y := (x = f d 0 ∧ y = f d 1) ∨ (x = f d 1 ∧ y = f d 0)
  isLink_symm := by
    intro d _
    exact ⟨fun _ _ h => h.elim (fun h => Or.inr h.symm) (fun h => Or.inl h.symm)⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro d x y v w (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals simp
  edge_mem_iff_exists_isLink := fun d => ⟨fun _ => ⟨f d 0, f d 1, Or.inl ⟨rfl, rfl⟩⟩,
    fun _ => _root_.Set.mem_univ _⟩
  left_mem_of_isLink := by
    rintro d x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl (Or.inr (_root_.Set.mem_range_self d))
    · exact Or.inr (_root_.Set.mem_range_self d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.curveGraph then
    throwError "Refusing to shadow existing declaration Graph.curveGraph"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.curveGraph ``Submission.Graph.curveGraph

open _root_.Graph in
theorem finite_curveGraph {α β : Type*} [_root_.Finite β]
    (f : β → ℝ → α) {W : Set α} (hW : W.Finite) : (curveGraph f W).Finite :=
  ⟨(hW.union (_root_.Set.finite_range _)).union (_root_.Set.finite_range _), finite_univ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.finite_curveGraph then
    throwError "Refusing to shadow existing declaration Graph.finite_curveGraph"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.finite_curveGraph ``Submission.Graph.finite_curveGraph

open _root_.Submission.Schoenflies in
open _root_.Graph in
theorem isDrawing_curveGraph {β : Type*} {f : β → ℝ → Plane} {W : Set Plane}
    (hf : ∀ d, ContinuousOn (f d) unitInterval) (hi : ∀ d, _root_.Set.InjOn (f d) unitInterval)
    (hW : ∀ d, edgeArc f d ∩ W ⊆ {f d 0, f d 1})
    (hmeet : Pairwise fun d j => edgeArc f d ∩ edgeArc f j ⊆ {f d 0, f d 1}) :
    IsDrawing (curveGraph f W) f := by
  have hlink (d : β) : (curveGraph f W).IsLink d (f d 0) (f d 1) := Or.inl ⟨rfl, rfl⟩
  have hvertex (d : β) {v : Plane} (hv : v ∈ V(curveGraph f W))
      (hvd : v ∈ edgeArc f d) : v = f d 0 ∨ v = f d 1 := by
    rcases hv with (hv | ⟨j, rfl⟩) | ⟨j, rfl⟩
    · exact hW d ⟨hvd, hv⟩
    · by_cases hj : d = j
      · subst j
        exact Or.inl rfl
      exact hmeet hj ⟨hvd, _root_.Set.mem_image_of_mem (f j) zero_mem_I⟩
    · by_cases hj : d = j
      · subst j
        exact Or.inr rfl
      exact hmeet hj ⟨hvd, _root_.Set.mem_image_of_mem (f j) one_mem_I⟩
  refine ⟨fun {d} _ => ⟨hf d, hi d, hlink d⟩, ?_, ?_⟩
  · intro d x y v hxy hv hvd
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hvertex d hv hvd
    · exact (hvertex d hv hvd).symm
  · intro d j _ _ hdj p hpd hpj
    have hpdends := hmeet hdj ⟨hpd, hpj⟩
    have hpjends := hmeet (Ne.symm hdj) ⟨hpj, hpd⟩
    refine ⟨?_, ?_, ?_⟩
    · rcases hpdends with rfl | rfl
      · exact (hlink d).left_mem
      · exact (hlink d).right_mem
    · exact hpdends.elim (fun heq => heq ▸ (hlink d).inc_left)
        (fun heq => heq ▸ (hlink d).inc_right)
    · exact hpjends.elim (fun heq => heq ▸ (hlink j).inc_left)
        (fun heq => heq ▸ (hlink j).inc_right)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.isDrawing_curveGraph then
    throwError "Refusing to shadow existing declaration Graph.isDrawing_curveGraph"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.isDrawing_curveGraph ``Submission.Graph.isDrawing_curveGraph

end Graph
