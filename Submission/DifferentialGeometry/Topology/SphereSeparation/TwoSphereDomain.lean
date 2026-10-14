import Submission.DifferentialGeometry.Topology.SphereSeparation.SchoenfliesSides
import Submission.DifferentialGeometry.Topology.SphereSeparation.OuterBoundary
import Submission.DifferentialGeometry.Topology.VanKampen.SphereBoundaryInjection
import Submission.DifferentialGeometry.Topology.Connected.DomainEquality
import Submission.DifferentialGeometry.Geometry.Boundary.NestedBallInterior

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Topology _root_.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem shell_of_outer_side
    {K S₀ S₁ : Set EuclideanThree} (hK : IsCompact K)
    (hregular : closure (interior K) = K) (hconn : IsPreconnected (interior K))
    (hfront : frontier K = S₀ ∪ S₁) (hd : Disjoint S₀ S₁)
    (hS₀ : S₀.Nonempty) (hS₁ : IsConnected S₁)
    (s : SphereSides S₀) (t : SphereSides S₁)
    (D₀ D₁ : Diffeomorph (𝓡 3) (𝓡 3) EuclideanThree EuclideanThree ∞)
    (hD₀ : s.compactSide = D₀ '' _root_.Metric.ball 0 1)
    (hD₀c : closure s.compactSide = D₀ '' _root_.Metric.closedBall 0 1)
    (hD₁ : t.compactSide = D₁ '' _root_.Metric.ball 0 1)
    (hD₁c : closure t.compactSide = D₁ '' _root_.Metric.closedBall 0 1)
    (houter : interior K ⊆ s.compactSide) :
    D₁ '' _root_.Metric.closedBall 0 1 ⊆ D₀ '' _root_.Metric.ball 0 1 ∧
      K = D₀ '' _root_.Metric.closedBall 0 1 \ D₁ '' _root_.Metric.ball 0 1 := by
  have hS₀K : S₀ ⊆ K := fun _ hx ↦ hK.isClosed.frontier_subset (hfront ▸ Or.inl hx)
  have hS₁K : S₁ ⊆ K := fun _ hx ↦ hK.isClosed.frontier_subset (hfront ▸ Or.inr hx)
  have hKB : K ⊆ closure s.compactSide := hregular ▸ closure_mono houter
  have hS₁B : S₁ ⊆ s.compactSide := by
    intro x hx
    have hxc := hKB (hS₁K hx)
    rw [s.closure_compactSide] at hxc
    exact hxc.resolve_right (fun hx₀ ↦ hd.le_bot ⟨hx₀, hx⟩)
  have hnest : closure t.compactSide ⊆ s.compactSide :=
    s.closure_compactSide_subset_of_sphere_subset t hd hS₁ hS₁B
  have hinner : interior K ⊆ t.endSide := by
    have havoid : interior K ⊆ S₁ᶜ := by
      intro x hx hf
      exact (disjoint_interior_frontier (s := K)).le_bot ⟨hx, hfront ▸ Or.inr hf⟩
    rcases t.subset_compactSide_or_subset_endSide hconn havoid with hi | hi
    · have hKB₁ : K ⊆ closure t.compactSide := hregular ▸ closure_mono hi
      obtain ⟨x, hx⟩ := hS₀
      exact False.elim (s.compactSide_disjoint_sphere.le_bot ⟨hnest (hKB₁ (hS₀K hx)), hx⟩)
    · exact hi
  have hKC : K ⊆ t.compactSideᶜ := by
    rw [← t.closure_endSide_eq_compl]
    exact hregular ▸ closure_mono hinner
  let A := closure s.compactSide \ t.compactSide
  have hKA : K ⊆ A := fun _ hx ↦ ⟨hKB hx, hKC hx⟩
  have hAeq : A = D₀ '' _root_.Metric.closedBall 0 1 \ D₁ '' _root_.Metric.ball 0 1 := by
    rw [show A = closure s.compactSide \ t.compactSide from rfl, hD₀c, hD₁]
  have hnestD : D₁ '' _root_.Metric.closedBall 0 1 ⊆ D₀ '' _root_.Metric.ball 0 1 := by
    rwa [hD₁c, hD₀] at hnest
  have hAc : IsPreconnected (interior A) := by
    rw [hAeq]
    exact DifferentialGeometry.Geometry.Boundary.isPreconnected_interior_nestedBallShell
      D₀.toPartialDiffeomorph D₁.toPartialDiffeomorph zero_lt_one
      (_root_.Set.subset_univ _) (_root_.Set.subset_univ _) hnestD (Classical.arbitrary SphereTwo)
  have hAr : closure (interior A) = A := by
    rw [hAeq]
    exact DifferentialGeometry.Geometry.Boundary.closure_interior_nestedBallShell
      D₀.toPartialDiffeomorph D₁.toPartialDiffeomorph zero_lt_one
      (_root_.Set.subset_univ _) (_root_.Set.subset_univ _) hnestD (Classical.arbitrary SphereTwo)
  have hiB : interior A ⊆ s.compactSide := by
    rw [← s.interior_closure_compactSide]
    exact interior_mono _root_.Set.sdiff_subset
  have hiC : interior A ⊆ (closure t.compactSide)ᶜ := by
    rw [← interior_compl]
    exact interior_mono (fun _ hx ↦ hx.2)
  have hdisj : Disjoint (frontier K) (interior A) := by
    rw [hfront, Set.disjoint_left]
    rintro x (hx | hx) hi
    · exact s.compactSide_disjoint_sphere.le_bot ⟨hiB hi, hx⟩
    · apply hiC hi
      rw [t.closure_compactSide]
      exact Or.inr hx
  refine ⟨hnestD, ?_⟩
  rw [← hAeq]
  exact eq_of_regularClosed_subset_of_frontier_disjoint hregular hAr hAc
    (hS₀.mono hS₀K) hKA hdisj

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.shell_of_outer_side
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.shell_of_outer_side target :: scope.openDecls } }

theorem exists_nested_ball_shell_of_two_spherical_boundaries
    (hSch : smoothSchoenfliesThree) {K : Set EuclideanThree}
    (hK : IsCompact K) (hregular : closure (interior K) = K)
    (hconn : IsPreconnected (interior K)) (e₀ e₁ : SphereTwo → EuclideanThree)
    (he₀ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₀)
    (he₁ : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₁)
    (hfront : frontier K = _root_.Set.range e₀ ∪ _root_.Set.range e₁)
    (hd : Disjoint (_root_.Set.range e₀) (_root_.Set.range e₁)) :
    ∃ outer inner : Diffeomorph (𝓡 3) (𝓡 3) EuclideanThree EuclideanThree ∞,
      inner '' _root_.Metric.closedBall 0 1 ⊆ outer '' _root_.Metric.ball 0 1 ∧
      K = outer '' _root_.Metric.closedBall 0 1 \ inner '' _root_.Metric.ball 0 1 := by
  obtain ⟨D₀, s, _, hD₀, hD₀c⟩ := exists_ball_sphereSides_of_smoothSchoenflies hSch e₀ he₀
  obtain ⟨D₁, t, _, hD₁, hD₁c⟩ := exists_ball_sphereSides_of_smoothSchoenflies hSch e₁ he₁
  obtain ⟨c, hc⟩ := exists_outward_collar_of_two_spherical_boundaries
    hregular e₀ e₁ he₀ he₁ hfront hd
  have hside := interior_subset_compactSide_or_of_two_boundary_collars
    c.inl c.inr s t hK hconn hfront
    (fun p ↦ hc (Sum.inl p.1, p.2)) (fun p ↦ hc (Sum.inr p.1, p.2))
  rcases hside with hs | ht
  · exact ⟨D₀, D₁, shell_of_outer_side hK hregular hconn hfront hd
      (_root_.Set.range_nonempty e₀) (isConnected_range he₁.contMDiff.continuous) s t D₀ D₁
      hD₀ hD₀c hD₁ hD₁c hs⟩
  · exact ⟨D₁, D₀, shell_of_outer_side hK hregular hconn (hfront.trans (_root_.Set.union_comm _ _)) hd.symm
      (_root_.Set.range_nonempty e₁) (isConnected_range he₀.contMDiff.continuous) t s D₁ D₀
      hD₁ hD₁c hD₀ hD₀c ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.exists_nested_ball_shell_of_two_spherical_boundaries then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.exists_nested_ball_shell_of_two_spherical_boundaries"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.exists_nested_ball_shell_of_two_spherical_boundaries ``Submission.DifferentialGeometry.Topology.SphereSeparation.exists_nested_ball_shell_of_two_spherical_boundaries

end DifferentialGeometry.Topology.SphereSeparation
