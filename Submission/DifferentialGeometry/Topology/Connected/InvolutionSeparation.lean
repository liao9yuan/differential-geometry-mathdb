import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set

namespace DifferentialGeometry.Topology

theorem disjoint_image_of_involutive_of_disjoint_image_frontier
    {X : Type*} [TopologicalSpace X] (h : X ≃ₜ X) (hinv : Function.Involutive h)
    {K : Set X} (hclosed : IsClosed K) (hconn : IsPreconnected K)
    (hfront : (frontier K).Nonempty) (havoid : Disjoint K (h '' frontier K)) :
    Disjoint K (h '' K) := by
  have hhK : h '' (h '' K) = K := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      rwa [hinv]
    · intro hx
      exact ⟨h x, _root_.Set.mem_image_of_mem _ hx, hinv x⟩
  have htarget : IsClosed (h '' K) := h.isClosedMap K hclosed
  have hfrontier : frontier (h '' K) = h '' frontier K :=
    (h.image_frontier K).symm
  have hcover : K ⊆ interior (h '' K) ∪ (h '' K)ᶜ := by
    intro x hx
    have hf : x ∈ (frontier (h '' K))ᶜ := by
      rw [hfrontier]
      exact fun hh => havoid.le_bot ⟨hx, hh⟩
    rwa [compl_frontier_eq_union_interior, htarget.isOpen_compl.interior_eq] at hf
  rcases hconn.subset_or_subset isOpen_interior htarget.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hcover with hinside | hout
  · have hreverse : h '' K ⊆ interior K := by
      have hh := _root_.Set.image_mono hinside (f := h)
      rwa [h.image_interior, hhK] at hh
    have hall : K ⊆ interior K := (hinside.trans interior_subset).trans hreverse
    obtain ⟨x, hx⟩ := hfront
    exact False.elim (hx.2 (hall (hclosed.frontier_subset hx)))
  · exact Set.disjoint_left.mpr (fun x hx hh => hout hx hh)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.disjoint_image_of_involutive_of_disjoint_image_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.disjoint_image_of_involutive_of_disjoint_image_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.disjoint_image_of_involutive_of_disjoint_image_frontier ``Submission.DifferentialGeometry.Topology.disjoint_image_of_involutive_of_disjoint_image_frontier

end DifferentialGeometry.Topology
