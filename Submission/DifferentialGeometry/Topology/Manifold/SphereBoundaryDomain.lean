import Submission.DifferentialGeometry.Topology.Embedding.LocalSeparation
import Submission.DifferentialGeometry.Topology.Connected.OpenPartition
import Submission.DifferentialGeometry.Topology.Connected.Frontier
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import Submission.DifferentialGeometry.Topology.OpenPartialHomeomorph.Images

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [PreconnectedSpace M] [T2Space M]

theorem isConnected_interior_and_compl_of_sphere_boundary
    {K : Set M} (hK : IsClosed K) (hne : (interior K).Nonempty)
    (e : S2 → M) (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hfront : frontier K = _root_.Set.range e) :
    IsConnected (interior K) ∧ IsConnected Kᶜ := by
  let _ : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp))
      (0 : E3) zero_le_one)
  have hout : Kᶜ.Nonempty := by
    by_contra h
    have hKU : K = univ := _root_.Set.eq_univ_of_forall fun x => by
      by_contra hx
      exact h ⟨x, hx⟩
    have hfne : (frontier K).Nonempty := hfront.symm ▸ _root_.Set.range_nonempty e
    simp only [hKU, frontier_univ, Set.not_nonempty_empty] at hfne
  have hcover : interior K ∪ Kᶜ = (frontier K)ᶜ := by
    rw [compl_frontier_eq_union_interior, hK.isOpen_compl.interior_eq]
  have hcard : ENat.card (ConnectedComponents ↥(interior K ∪ Kᶜ)) ≤ 2 := by
    rw [hcover, hfront]
    exact he.card_connectedComponents_compl_le_two_of_compact (by simp)
  exact DifferentialGeometry.Topology.isConnected_open_partition_of_card_connectedComponents_le_two
    isOpen_interior hK.isOpen_compl (disjoint_compl_right.mono_left interior_subset) hne hout hcard

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.isConnected_interior_and_compl_of_sphere_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.isConnected_interior_and_compl_of_sphere_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.isConnected_interior_and_compl_of_sphere_boundary ``Submission.DifferentialGeometry.Topology.Manifold.isConnected_interior_and_compl_of_sphere_boundary

omit [ChartedSpace E3 M] [PreconnectedSpace M] [T2Space M] in
theorem subset_or_union_eq_univ_of_frontier_subset_interior
    {A K : Set M} (hA : IsClosed A) (hKcompl : IsPreconnected Kᶜ)
    (hfront : frontier A ⊆ interior K) : A ⊆ K ∨ A ∪ K = univ := by
  have havoid : Kᶜ ⊆ (frontier A)ᶜ :=
    fun _ h hA => h (interior_subset (hfront hA))
  have hcover : Kᶜ ⊆ interior A ∪ Aᶜ := by
    rw [← hA.isOpen_compl.interior_eq, ← compl_frontier_eq_union_interior]
    exact havoid
  rcases hKcompl.subset_or_subset isOpen_interior hA.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hcover with hin | hout
  · right
    apply _root_.Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ K
    · exact Or.inr hx
    · exact Or.inl (interior_subset (hin hx))
  · exact Or.inl (fun x hx => by by_contra h; exact hout h hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.subset_or_union_eq_univ_of_frontier_subset_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.subset_or_union_eq_univ_of_frontier_subset_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.subset_or_union_eq_univ_of_frontier_subset_interior ``Submission.DifferentialGeometry.Topology.Manifold.subset_or_union_eq_univ_of_frontier_subset_interior

theorem ball_union_eq_univ_of_sphere_boundary_and_point_outside
    {K : Set M} (hK : IsClosed K) (hne : (interior K).Nonempty)
    (e : S2 → M) (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hfrontK : frontier K = _root_.Set.range e)
    (B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hB : _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source)
    (hinside : B '' _root_.Metric.sphere (0 : E3) 1 ⊆ interior K)
    {y : M} (hy : y ∈ B '' _root_.Metric.closedBall (0 : E3) 1) (hyK : y ∉ K) :
    B '' _root_.Metric.closedBall (0 : E3) 1 ∪ K = univ := by
  have hBc : IsClosed (B '' _root_.Metric.closedBall (0 : E3) 1) :=
    ((_root_.ProperSpace.isCompact_closedBall _ _).image_of_continuousOn
      (B.contMDiffOn_toFun.continuousOn.mono hB)).isClosed
  have hBfront : frontier (B '' _root_.Metric.closedBall (0 : E3) 1) = B '' _root_.Metric.sphere (0 : E3) 1 := by
    have h := B.toOpenPartialHomeomorph.image_frontier_of_subset_source hB _root_.Metric.isClosed_closedBall hBc
    rw [frontier_closedBall _ one_ne_zero] at h
    exact h.symm
  have hconn := (isConnected_interior_and_compl_of_sphere_boundary hK hne e he hfrontK).2
  rcases subset_or_union_eq_univ_of_frontier_subset_interior hBc hconn.isPreconnected
    (hBfront ▸ hinside) with h | h
  · exact (hyK (h hy)).elim
  · exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.ball_union_eq_univ_of_sphere_boundary_and_point_outside then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.ball_union_eq_univ_of_sphere_boundary_and_point_outside"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.ball_union_eq_univ_of_sphere_boundary_and_point_outside ``Submission.DifferentialGeometry.Topology.Manifold.ball_union_eq_univ_of_sphere_boundary_and_point_outside

end DifferentialGeometry.Topology.Manifold
