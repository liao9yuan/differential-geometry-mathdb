/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Connected.BallComplement
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SurfaceComplement
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifold.exists_bounded_connectedComponentIn_pair_compl
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdim : Module.finrank ℝ E = 3)
    (hconn : IsConnected K.space) :
    ∃ a ∈ K.spaceᶜ, ∃ b ∈ K.spaceᶜ,
      let A := connectedComponentIn K.spaceᶜ a
      let B := connectedComponentIn K.spaceᶜ b
      Bornology.IsBounded A ∧ Disjoint A B ∧ A ∪ B = K.spaceᶜ ∧
        closure A ∩ closure B = K.space ∧ frontier A = K.space ∧ frontier B = K.space := by
  obtain ⟨a, ha, b, hb, hdis, hcover, -, hmeet, hfrontA, hfrontB⟩ :=
    hK.exists_connectedComponentIn_pair_compl K hdim hconn
  obtain ⟨r, hr, hKr⟩ := (isPolyhedron_space K).isCompact.isBounded.exists_pos_norm_lt
  have hdimrank : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank', hdim]
    norm_num
  have hext := (Topology.isPathConnected_compl_closedBall hdimrank (0 : E) r).isConnected
  have hextK : (_root_.Metric.closedBall (0 : E) r)ᶜ ⊆ K.spaceᶜ := by
    intro x hx hxK
    exact hx (mem_closedBall_zero_iff.mpr (hKr x hxK).le)
  obtain ⟨c, hc⟩ := hext.nonempty
  have hsub := hext.isPreconnected.subset_connectedComponentIn hc hextK
  have hbounded : Bornology.IsBounded (connectedComponentIn K.spaceᶜ a) ∨
      Bornology.IsBounded (connectedComponentIn K.spaceᶜ b) := by
    rcases hcover.symm.subset (hextK hc) with hcA | hcB
    · rw [← connectedComponentIn_eq hcA] at hsub
      refine Or.inr ((_root_.Metric.isBounded_closedBall (x := (0 : E)) (r := r)).subset ?_)
      intro x hx
      by_contra hnot
      exact disjoint_left.mp hdis (hsub hnot) hx
    · rw [← connectedComponentIn_eq hcB] at hsub
      refine Or.inl ((_root_.Metric.isBounded_closedBall (x := (0 : E)) (r := r)).subset ?_)
      intro x hx
      by_contra hnot
      exact disjoint_left.mp hdis hx (hsub hnot)
  rcases hbounded with hA | hB
  · exact ⟨a, ha, b, hb, hA, hdis, hcover, hmeet, hfrontA, hfrontB⟩
  · exact ⟨b, hb, a, ha, hB, hdis.symm, (_root_.Set.union_comm _ _).trans hcover,
      (_root_.Set.inter_comm _ _).trans hmeet, hfrontB, hfrontA⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_bounded_connectedComponentIn_pair_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_bounded_connectedComponentIn_pair_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_bounded_connectedComponentIn_pair_compl ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_bounded_connectedComponentIn_pair_compl

theorem IsCombinatorialManifold.exists_isOpen_isBounded_frontier
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdim : Module.finrank ℝ E = 3)
    (hconn : IsConnected K.space) :
    ∃ U : Set E, IsOpen U ∧ IsConnected U ∧ Bornology.IsBounded U ∧
      frontier U = K.space ∧ IsPolyhedron (closure U) ∧
      interior (closure U) = U ∧ frontier (closure U) = K.space ∧
      IsConnected (closure U)ᶜ := by
  obtain ⟨a, ha, b, hb, hbounded, hdis, hcover, -, hfrontA, hfrontB⟩ :=
    hK.exists_bounded_connectedComponentIn_pair_compl K hdim hconn
  let A := connectedComponentIn K.spaceᶜ a
  let B := connectedComponentIn K.spaceᶜ b
  have hAopen : IsOpen A := (isPolyhedron_space K).isClosed.isOpen_compl.connectedComponentIn
  have hBopen : IsOpen B := (isPolyhedron_space K).isClosed.isOpen_compl.connectedComponentIn
  have hAB : closure A = Bᶜ := by
    rw [closure_eq_interior_union_frontier, hAopen.interior_eq, hfrontA]
    ext x
    constructor
    · rintro (hxA | hxK) hxB
      · exact disjoint_left.mp hdis hxA hxB
      · exact connectedComponentIn_subset _ _ hxB hxK
    · intro hxB
      by_cases hxK : x ∈ K.space
      · exact Or.inr hxK
      · exact Or.inl ((hcover.symm.subset hxK).resolve_right hxB)
  have hBA : closure B = Aᶜ := by
    rw [closure_eq_interior_union_frontier, hBopen.interior_eq, hfrontB]
    ext x
    constructor
    · rintro (hxB | hxK) hxA
      · exact disjoint_left.mp hdis hxA hxB
      · exact connectedComponentIn_subset _ _ hxA hxK
    · intro hxA
      by_cases hxK : x ∈ K.space
      · exact Or.inr hxK
      · exact Or.inl ((hcover.symm.subset hxK).resolve_left hxA)
  have hinter : interior (closure A) = A := by rw [hAB, interior_compl, hBA, compl_compl]
  have hfront : frontier (closure A) = K.space := by rw [hAB, frontier_compl, hfrontB]
  refine ⟨A, hAopen, isConnected_connectedComponentIn_iff.mpr ha, hbounded, hfrontA,
    isPolyhedron_closure_of_isPolyhedron_frontier hAopen hbounded
      (hfrontA.symm ▸ isPolyhedron_space K), hinter, hfront, ?_⟩
  rw [hAB, compl_compl]
  exact isConnected_connectedComponentIn_iff.mpr hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_isOpen_isBounded_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_isOpen_isBounded_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_isOpen_isBounded_frontier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_isOpen_isBounded_frontier

end DifferentialGeometry.Topology.PiecewiseLinear
