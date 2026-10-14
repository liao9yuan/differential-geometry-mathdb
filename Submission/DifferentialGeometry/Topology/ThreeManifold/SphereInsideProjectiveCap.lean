import Submission.DifferentialGeometry.Topology.ThreeManifold.AntipodalQuotientBall
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.Topology.ThreeManifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.E4 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.S2 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.S3 target :: scope.openDecls } }

variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z] [T2Space Z]

theorem exists_ball_or_complement_avoiding_closed_ball_of_projective_sphere_embedding
    (p : S3 → Z) (hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p)
    (honto : Function.Surjective p)
    (hfib : ∀ x y : S3, p x = p y ↔ x = y ∨ (x : E4) = -(y : E4))
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (hC : _root_.Metric.closedBall (0 : E3) 1 ⊆ C.source)
    (e : S2 → Z) (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (havoid : Disjoint (C '' _root_.Metric.closedBall (0 : E3) 1) (_root_.Set.range e)) :
    ∃ B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞,
      _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source ∧
      B '' _root_.Metric.sphere (0 : E3) 1 = _root_.Set.range e ∧
      (B '' _root_.Metric.closedBall (0 : E3) 1 ⊆ (C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ ∨
        (B '' _root_.Metric.ball (0 : E3) 1)ᶜ ⊆ (C '' _root_.Metric.closedBall (0 : E3) 1)ᶜ) := by
  obtain ⟨B, hB, hBs⟩ :=
    exists_ball_chart_of_antipodal_quotient_sphere_embedding p hp honto hfib e he
  let K := B '' _root_.Metric.closedBall (0 : E3) 1
  let O := C '' _root_.Metric.closedBall (0 : E3) 1
  have hK : IsCompact K :=
    (_root_.ProperSpace.isCompact_closedBall _ _).image_of_continuousOn (B.contMDiffOn_toFun.continuousOn.mono hB)
  have hKfront : frontier K = _root_.Set.range e := by
    rw [← B.image_frontier_of_isCompact (_root_.ProperSpace.isCompact_closedBall _ _) hB,
      frontier_closedBall _ one_ne_zero, hBs]
  have hKint : interior K = B '' _root_.Metric.ball (0 : E3) 1 := by
    have h := B.toOpenPartialHomeomorph.image_interior_of_subset_source hB
    change B '' interior (_root_.Metric.closedBall (0 : E3) 1) = interior K at h
    rw [interior_closedBall _ one_ne_zero] at h
    exact h.symm
  have hO : IsPreconnected O :=
    (convex_closedBall (0 : E3) 1).isPreconnected.image C (C.contMDiffOn_toFun.continuousOn.mono hC)
  have hcover : O ⊆ interior K ∪ Kᶜ := by
    intro x hx
    have hxnot : x ∈ (frontier K)ᶜ := by
      rw [hKfront]
      exact fun h => disjoint_left.mp havoid hx h
    rwa [compl_frontier_eq_union_interior, hK.isClosed.isOpen_compl.interior_eq] at hxnot
  refine ⟨B, hB, hBs, ?_⟩
  rcases hO.subset_or_subset isOpen_interior hK.isClosed.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hcover with hin | hout
  · right
    intro x hx hy
    exact hx (hKint ▸ hin hy)
  · left
    exact fun x hx hy => hout hy hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.exists_ball_or_complement_avoiding_closed_ball_of_projective_sphere_embedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.exists_ball_or_complement_avoiding_closed_ball_of_projective_sphere_embedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.exists_ball_or_complement_avoiding_closed_ball_of_projective_sphere_embedding ``Submission.DifferentialGeometry.Topology.ThreeManifold.exists_ball_or_complement_avoiding_closed_ball_of_projective_sphere_embedding

end DifferentialGeometry.Topology.ThreeManifold
