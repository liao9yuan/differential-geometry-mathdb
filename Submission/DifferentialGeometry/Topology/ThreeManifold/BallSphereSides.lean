import Submission.DifferentialGeometry.Topology.Manifold.SphereBoundaryDomain
import Submission.DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import Submission.DifferentialGeometry.Topology.Embedding.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.ThreeManifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.E3 target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by norm_num [Module.finrank_fin_fun]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private abbrev S2 := _root_.Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.S2 target :: scope.openDecls } }

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [PreconnectedSpace M]

theorem eq_ball_or_complement_of_connected_sphere_frontier
    (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hG : _root_.Metric.closedBall (0 : E3) 1 ⊆ G.source)
    {C : Set M} (hC : IsOpen C) (hconn : IsConnected C)
    (hfront : frontier C = G '' _root_.Metric.sphere (0 : E3) 1) :
    C = G '' _root_.Metric.ball (0 : E3) 1 ∨ C = (G '' _root_.Metric.closedBall (0 : E3) 1)ᶜ := by
  let K := G '' _root_.Metric.closedBall (0 : E3) 1
  have hK : IsCompact K := (_root_.ProperSpace.isCompact_closedBall _ _).image_of_continuousOn
    (G.contMDiffOn_toFun.continuousOn.mono hG)
  have hKi : interior K = G '' _root_.Metric.ball (0 : E3) 1 := by
    have hh := G.toOpenPartialHomeomorph.image_interior_of_subset_source hG
    change G '' interior (_root_.Metric.closedBall (0 : E3) 1) = interior K at hh
    rw [interior_closedBall _ one_ne_zero] at hh
    exact hh.symm
  have hKf : frontier K = G '' _root_.Metric.sphere (0 : E3) 1 := by
    have hh := G.image_frontier_of_isCompact (_root_.ProperSpace.isCompact_closedBall (0 : E3) 1) hG
    rw [frontier_closedBall _ one_ne_zero] at hh
    exact hh.symm
  let e : S2 → M := G ∘ Subtype.val
  have he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph G
      (isSmoothEmbedding_coe_sphere (E := E3) (n := 2))
      (by rw [Subtype.range_val]; exact sphere_subset_closedBall.trans hG)
  have hfr : frontier K = _root_.Set.range e := by rw [hKf, _root_.Set.range_comp, Subtype.range_val]
  have hi : (interior K).Nonempty := by
    rw [hKi]
    exact (nonempty_ball.mpr zero_lt_one).image G
  have hsides :=
    DifferentialGeometry.Topology.Manifold.isConnected_interior_and_compl_of_sphere_boundary
    hK.isClosed hi e he hfr
  have havoid : Disjoint C (frontier K) := by
    rw [hKf, ← hfront]
    exact disjoint_left.mpr fun x hx hxf => hxf.2 (hC.interior_eq.symm ▸ hx)
  have hcover : C ⊆ interior K ∪ Kᶜ := by
    intro x hx
    have hh : x ∈ (frontier K)ᶜ := fun h => havoid.le_bot ⟨hx, h⟩
    rwa [compl_frontier_eq_union_interior, hK.isClosed.isOpen_compl.interior_eq] at hh
  have hreverse {U : Set M} (hU : IsPreconnected U) (hUK : Disjoint U (frontier K))
      (hCU : C ⊆ U) : U ⊆ C := by
    apply hU.subset_of_closure_inter_subset hC
    · obtain ⟨x, hx⟩ := hconn.nonempty
      exact ⟨x, hCU hx, hx⟩
    · rintro x ⟨hxc, hxU⟩
      by_contra hxn
      have hxf : x ∈ frontier C := ⟨hxc, fun h => hxn (interior_subset h)⟩
      exact hUK.le_bot ⟨hxU, (hfront.trans hKf.symm) ▸ hxf⟩
  rcases hconn.isPreconnected.subset_or_subset isOpen_interior hK.isClosed.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hcover with hiC | hoC
  · left
    rw [← hKi]
    exact subset_antisymm hiC (hreverse hsides.1.isPreconnected disjoint_interior_frontier hiC)
  · right
    exact subset_antisymm hoC (hreverse hsides.2.isPreconnected
      (disjoint_compl_left.mono_right hK.isClosed.frontier_subset) hoC)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.eq_ball_or_complement_of_connected_sphere_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.eq_ball_or_complement_of_connected_sphere_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.eq_ball_or_complement_of_connected_sphere_frontier ``Submission.DifferentialGeometry.Topology.ThreeManifold.eq_ball_or_complement_of_connected_sphere_frontier

end DifferentialGeometry.Topology.ThreeManifold
