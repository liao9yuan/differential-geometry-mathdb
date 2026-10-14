import Submission.DifferentialGeometry.Topology.ThreeManifold.ChartSphereBall
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import Submission.DifferentialGeometry.Topology.Embedding.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.ThreeManifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.E3 target :: scope.openDecls } }
private abbrev S2 := _root_.Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.S2 target :: scope.openDecls } }

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M] [IsManifold (𝓡 3) ∞ M]

theorem exists_complementary_ball_chart_of_ball_cap_cover
    (A B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hA : _root_.Metric.closedBall (0 : E3) 1 ⊆ A.source)
    (hB : _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source)
    (hcover : B '' _root_.Metric.closedBall (0 : E3) 1 ∪ A '' _root_.Metric.closedBall (0 : E3) 1 = _root_.Set.univ) :
    ∃ G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      _root_.Metric.closedBall (0 : E3) 1 ⊆ G.source ∧
      G '' _root_.Metric.ball (0 : E3) 1 = (B '' _root_.Metric.closedBall (0 : E3) 1)ᶜ ∧
      G '' _root_.Metric.closedBall (0 : E3) 1 = (B '' _root_.Metric.ball (0 : E3) 1)ᶜ ∧
      G '' _root_.Metric.sphere (0 : E3) 1 = B '' _root_.Metric.sphere (0 : E3) 1 := by
  let C : Set M := (B '' _root_.Metric.closedBall (0 : E3) 1)ᶜ
  have hBA : IsCompact (B '' _root_.Metric.closedBall (0 : E3) 1) :=
    (_root_.ProperSpace.isCompact_closedBall _ _).image_of_continuousOn
      (B.contMDiffOn_toFun.continuousOn.mono hB)
  have hAA : IsCompact (A '' _root_.Metric.closedBall (0 : E3) 1) :=
    (_root_.ProperSpace.isCompact_closedBall _ _).image_of_continuousOn
      (A.contMDiffOn_toFun.continuousOn.mono hA)
  have hCsub : C ⊆ A '' _root_.Metric.closedBall (0 : E3) 1 := by
    intro x hx
    have hh : x ∈ B '' _root_.Metric.closedBall (0 : E3) 1 ∪ A '' _root_.Metric.closedBall (0 : E3) 1 := by
      rw [hcover]
      exact _root_.Set.mem_univ x
    exact hh.resolve_left hx
  have hclsub : closure C ⊆ A '' _root_.Metric.closedBall (0 : E3) 1 :=
    closure_minimal hCsub hAA.isClosed
  have hcompact : IsCompact (closure C) := hAA.of_isClosed_subset isClosed_closure hclsub
  have hsource : closure C ⊆ A.target := by
    rintro x hx
    obtain ⟨y, hy, rfl⟩ := hclsub hx
    exact A.map_source (hA hy)
  let e : S2 → M := B ∘ Subtype.val
  have he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph B
      (isSmoothEmbedding_coe_sphere (E := E3) (n := 2))
      (by rw [Subtype.range_val]; exact sphere_subset_closedBall.trans hB)
  have hfront : frontier C = _root_.Set.range e := by
    have hh := B.image_frontier_of_isCompact (_root_.ProperSpace.isCompact_closedBall (0 : E3) 1) hB
    rw [frontier_closedBall _ one_ne_zero] at hh
    change frontier (B '' _root_.Metric.closedBall (0 : E3) 1)ᶜ = _root_.Set.range (B ∘ Subtype.val)
    rw [frontier_compl, ← hh, _root_.Set.range_comp, Subtype.range_val]
  have hne : C.Nonempty := by
    by_contra hh
    have hall : B '' _root_.Metric.closedBall (0 : E3) 1 = univ := by
      apply _root_.Set.eq_univ_of_forall
      intro z
      by_contra hz
      exact hh ⟨z, hz⟩
    have hfrontne : (frontier C).Nonempty := by
      rw [hfront]
      exact _root_.Set.range_nonempty e
    change (frontier (B '' _root_.Metric.closedBall (0 : E3) 1)ᶜ).Nonempty at hfrontne
    simp only [hall, _root_.Set.compl_univ, frontier_empty, Set.not_nonempty_empty] at hfrontne
  obtain ⟨G, hGs, hGo, hGc, hGf⟩ :=
    exists_ball_chart_of_compact_closure_sphere_frontier A hBA.isClosed.isOpen_compl
      hne hcompact hsource e he hfront
  have hclosure : closure C = (B '' _root_.Metric.ball (0 : E3) 1)ᶜ := by
    change closure (B '' _root_.Metric.closedBall (0 : E3) 1)ᶜ = _
    rw [closure_compl]
    congr 1
    have hh := B.toOpenPartialHomeomorph.image_interior_of_subset_source hB
    change B '' interior (_root_.Metric.closedBall (0 : E3) 1) =
      interior (B '' _root_.Metric.closedBall (0 : E3) 1) at hh
    rw [interior_closedBall _ one_ne_zero] at hh
    exact hh.symm
  refine ⟨G, hGs, hGo, hGc.trans hclosure, ?_⟩
  simpa only [e, _root_.Set.range_comp, Subtype.range_val] using hGf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.exists_complementary_ball_chart_of_ball_cap_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.exists_complementary_ball_chart_of_ball_cap_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.exists_complementary_ball_chart_of_ball_cap_cover ``Submission.DifferentialGeometry.Topology.ThreeManifold.exists_complementary_ball_chart_of_ball_cap_cover

end DifferentialGeometry.Topology.ThreeManifold
