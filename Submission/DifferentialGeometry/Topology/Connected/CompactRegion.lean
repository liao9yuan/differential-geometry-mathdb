import Submission.DifferentialGeometry.Topology.Connected.FrontierCover
import Mathlib.Topology.Compactness.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] [NoncompactSpace X]

theorem subset_of_isCompact_of_frontier_subset_of_isPreconnected_compl
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B)
    (hconn : IsPreconnected Bᶜ) (hfront : frontier A ⊆ B) : A ⊆ B := by
  intro x hxA
  by_contra hxB
  have hxint : x ∈ interior A := (mem_interior_iff_notMem_frontier hxA).mpr
    (fun hx => hxB (hfront hx))
  have hsub : Bᶜ ⊆ interior A :=
    subset_interior_of_isPreconnected_of_disjoint_frontier hconn
      (disjoint_compl_left.mono_right hfront) ⟨x, hxB, hxint⟩
  apply (hA.union hB).ne_univ
  apply _root_.Set.eq_univ_of_forall
  intro y
  by_cases hy : y ∈ B
  · exact Or.inr hy
  · exact Or.inl (interior_subset (hsub hy))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subset_of_isCompact_of_frontier_subset_of_isPreconnected_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subset_of_isCompact_of_frontier_subset_of_isPreconnected_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subset_of_isCompact_of_frontier_subset_of_isPreconnected_compl ``Submission.DifferentialGeometry.Topology.subset_of_isCompact_of_frontier_subset_of_isPreconnected_compl

variable [T2Space X]

theorem eq_of_isCompact_of_frontier_eq
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B)
    (hAreg : closure (interior A) = A) (hBreg : closure (interior B) = B)
    (hBint : IsPreconnected (interior B)) (hBext : IsPreconnected Bᶜ)
    (hne : A.Nonempty) (hfront : frontier A = frontier B) : A = B := by
  have hAB : A ⊆ B := subset_of_isCompact_of_frontier_subset_of_isPreconnected_compl
    hA hB hBext (hfront.subset.trans hB.isClosed.frontier_subset)
  have hAint : (interior A).Nonempty := by
    by_contra h
    have hempty := not_nonempty_iff_eq_empty.mp h
    rw [hempty, closure_empty] at hAreg
    exact hne.ne_empty hAreg.symm
  obtain ⟨x, hx⟩ := hAint
  exact Subset.antisymm hAB
    (subset_of_frontier_subset_of_closure_interior_eq hA.isClosed hBreg hBint
      hfront.subset ⟨x, interior_mono hAB hx, hx⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.eq_of_isCompact_of_frontier_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.eq_of_isCompact_of_frontier_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.eq_of_isCompact_of_frontier_eq ``Submission.DifferentialGeometry.Topology.eq_of_isCompact_of_frontier_eq

end DifferentialGeometry.Topology
