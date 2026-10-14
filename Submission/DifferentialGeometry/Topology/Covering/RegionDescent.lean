import Submission.DifferentialGeometry.Topology.Covering.DeckGroup
import Submission.DifferentialGeometry.Topology.Connected.CoverBySides

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false

noncomputable section

open _root_.Set

namespace DifferentialGeometry

variable {E M S : Type*} [TopologicalSpace E] [PreconnectedSpace E]
  [TopologicalSpace M] [Nonempty S]
  {p : E → M} {e : S → M} {lift : S → E}

theorem coveringDeckGroup_eq_one_of_preserves_lift_range
    (hp : IsCoveringMap p) (he : Function.Injective e) (hlift : ∀ z, p (lift z) = e z)
    (gamma : coveringDeckGroup p)
    (hgamma : (fun y => gamma • y) '' _root_.Set.range lift = _root_.Set.range lift) : gamma = 1 := by
  obtain ⟨z⟩ := (inferInstance : Nonempty S)
  have hz : gamma • lift z ∈ _root_.Set.range lift := hgamma ▸ _root_.Set.mem_image_of_mem _ (_root_.Set.mem_range_self z)
  obtain ⟨w, hw⟩ := hz
  have hwz : w = z := he (by rw [← hlift w, hw, coveringDeckGroup_map (p := p) gamma (lift z), hlift z])
  subst w
  exact coveringDeckGroup_eq_one_of_apply_eq hp gamma (lift z) hw.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.coveringDeckGroup_eq_one_of_preserves_lift_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.coveringDeckGroup_eq_one_of_preserves_lift_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.coveringDeckGroup_eq_one_of_preserves_lift_range ``Submission.DifferentialGeometry.coveringDeckGroup_eq_one_of_preserves_lift_range

theorem coveringDeckGroup_eq_one_of_preserves_set_with_lifted_frontier
    (hp : IsCoveringMap p) (he : Function.Injective e) (hlift : ∀ z, p (lift z) = e z)
    {B : Set E} (hfrontier : frontier B = _root_.Set.range lift) (gamma : coveringDeckGroup p)
    (hgamma : (fun y => gamma • y) '' B = B) : gamma = 1 := by
  apply coveringDeckGroup_eq_one_of_preserves_lift_range hp he hlift gamma
  change (coveringDeckGroupHomeomorph gamma) '' _root_.Set.range lift = _root_.Set.range lift
  rw [← hfrontier, Homeomorph.image_frontier]
  exact congrArg frontier hgamma

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.coveringDeckGroup_eq_one_of_preserves_set_with_lifted_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.coveringDeckGroup_eq_one_of_preserves_set_with_lifted_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.coveringDeckGroup_eq_one_of_preserves_set_with_lifted_frontier ``Submission.DifferentialGeometry.coveringDeckGroup_eq_one_of_preserves_set_with_lifted_frontier

end DifferentialGeometry

end

end

section

set_option autoImplicit false

noncomputable section

open _root_.Set

namespace DifferentialGeometry

variable {E M S : Type*} [TopologicalSpace E] [SimplyConnectedSpace E]
  [LocallyPathConnectedSpace E] [TopologicalSpace M] [Nonempty S]
  {p : E → M} {e : S → M} {lift : S → E}

theorem IsCoveringMap.injOn_closure_of_lifted_frontier
    (hp : IsCoveringMap p) (he : Function.Injective e) (hlift : ∀ z, p (lift z) = e z)
    {B : Set E} (hBopen : IsOpen B) (hBconn : IsPreconnected B)
    (hfrontier : frontier B = _root_.Set.range lift) (havoid : Disjoint B (p ⁻¹' _root_.Set.range e)) :
    InjOn p (closure B) := by
  have hnot (y : E) (hy : y ∈ B) : p y ∉ _root_.Set.range e := fun hs => havoid.le_bot ⟨hy, hs⟩
  have hproj (y : E) (hy : y ∈ frontier B) : p y ∈ _root_.Set.range e := by
    obtain ⟨z, rfl⟩ := hfrontier ▸ hy
    exact ⟨z, (hlift z).symm⟩
  intro x hx y hy hxy
  by_cases hxB : x ∈ B
  · have hyB : y ∈ B := by
      by_contra hyB
      have hyF : y ∈ frontier B := ⟨hy, by simpa only [hBopen.interior_eq] using hyB⟩
      exact hnot x hxB (hxy ▸ hproj y hyF)
    obtain ⟨gamma, hgamma⟩ := (coveringDeckGroup_apply_eq_iff hp).mp hxy.symm
    let H := coveringDeckGroupHomeomorph gamma
    have hHproj (z : E) : p (H z) = p z := coveringDeckGroup_map gamma z
    have hmeet : (H '' B ∩ B).Nonempty := ⟨y, ⟨x, hxB, hgamma⟩, hyB⟩
    have hdis : Disjoint (H '' B) (frontier B) := by
      rw [Set.disjoint_left]
      rintro z ⟨w, hw, rfl⟩ hz
      exact hnot w hw (hHproj w ▸ hproj (H w) hz)
    have hsub : H '' B ⊆ B :=
      (Topology.isPreconnected_subset_interior_of_meets_of_disjoint_frontier
        (hBconn.image H H.continuous.continuousOn) hmeet hdis).trans interior_subset
    have hdis' : Disjoint B (frontier (H '' B)) := by
      rw [← H.image_frontier, Set.disjoint_left]
      rintro z hz ⟨w, hw, rfl⟩
      exact hnot (H w) hz ((hHproj w).symm ▸ hproj w hw)
    have hsub' : B ⊆ H '' B :=
      (Topology.isPreconnected_subset_interior_of_meets_of_disjoint_frontier
        hBconn (by simpa only [_root_.Set.inter_comm] using hmeet) hdis').trans interior_subset
    have hgamma' : gamma = 1 := coveringDeckGroup_eq_one_of_preserves_set_with_lifted_frontier
      hp he hlift hfrontier gamma (hsub.antisymm hsub')
    simpa only [hgamma', one_smul] using hgamma
  · have hxF : x ∈ frontier B := ⟨hx, by simpa only [hBopen.interior_eq] using hxB⟩
    have hyB : y ∉ B := fun hyB => hnot y hyB (hxy ▸ hproj x hxF)
    have hyF : y ∈ frontier B := ⟨hy, by simpa only [hBopen.interior_eq] using hyB⟩
    obtain ⟨a, rfl⟩ := hfrontier ▸ hxF
    obtain ⟨b, rfl⟩ := hfrontier ▸ hyF
    exact congrArg lift (he ((hlift a).symm.trans (hxy.trans (hlift b))))

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.IsCoveringMap
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.IsCoveringMap.injOn_closure_of_lifted_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.IsCoveringMap.injOn_closure_of_lifted_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.IsCoveringMap.injOn_closure_of_lifted_frontier ``Submission.DifferentialGeometry.IsCoveringMap.injOn_closure_of_lifted_frontier

end DifferentialGeometry

end

end
