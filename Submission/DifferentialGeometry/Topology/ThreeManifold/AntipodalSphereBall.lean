import Submission.DifferentialGeometry.Topology.ThreeManifold.SphereBallAvoidingPoint
import Submission.DifferentialGeometry.Topology.Connected.InvolutionSeparation
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import Submission.DifferentialGeometry.Topology.Manifold.StereographicAntipodal

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

theorem exists_ball_chart_disjoint_antipodal_of_sphere_embedding
    (e : S2 → S3) (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hdisj : Disjoint (_root_.Set.range e) (_root_.Set.range (fun x => -(e x)))) :
    ∃ B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞,
      _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source ∧ B '' _root_.Metric.sphere (0 : E3) 1 = _root_.Set.range e ∧
      Disjoint (B '' _root_.Metric.closedBall (0 : E3) 1)
        ((Neg.neg : S3 → S3) '' (B '' _root_.Metric.closedBall (0 : E3) 1)) := by
  let z : S2 := DifferentialGeometry.Topology.sphereTwoNorth
  let p : S3 := -(e z)
  have hp : p ∉ _root_.Set.range e := fun hx => hdisj.le_bot ⟨hx, z, rfl⟩
  obtain ⟨B, hB, hBs, hpB⟩ := exists_ball_chart_of_sphere_embedding_avoiding_point e he p hp
  let K := B '' _root_.Metric.closedBall (0 : E3) 1
  have hK : IsCompact K := (_root_.ProperSpace.isCompact_closedBall _ _).image_of_continuousOn
    (B.contMDiffOn_toFun.continuousOn.mono hB)
  have hfront : frontier K = _root_.Set.range e := by
    have hh := B.image_frontier_of_isCompact (_root_.ProperSpace.isCompact_closedBall (0 : E3) 1) hB
    rw [frontier_closedBall _ one_ne_zero] at hh
    exact hh.symm.trans hBs
  let h := (DifferentialGeometry.Topology.Manifold.sphereAntipodalDiffeomorph
    (E := E4) (n := 3)).toHomeomorph
  have hother : IsPreconnected (_root_.Set.range (fun x => -(e x))) := by
    let : PreconnectedSpace S2 := Subtype.preconnectedSpace
      (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [E3])) 0 1)
    exact (isPreconnected_range (h.continuous.comp he.contMDiff.continuous))
  have hcover : _root_.Set.range (fun x => -(e x)) ⊆ interior K ∪ Kᶜ := by
    intro y hy
    have hf : y ∈ (frontier K)ᶜ := by
      rw [hfront]
      exact fun hx => hdisj.le_bot ⟨hx, hy⟩
    rwa [compl_frontier_eq_union_interior, hK.isClosed.isOpen_compl.interior_eq] at hf
  have hout : _root_.Set.range (fun x => -(e x)) ⊆ Kᶜ := by
    rcases hother.subset_or_subset isOpen_interior hK.isClosed.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) hcover with hi | ho
    · exact False.elim (hpB (interior_subset (hi (_root_.Set.mem_range_self z))))
    · exact ho
  have havoid : Disjoint K (h '' frontier K) := by
    rw [hfront]
    apply disjoint_left.mpr
    rintro y hy ⟨v, ⟨x, rfl⟩, rfl⟩
    exact hout (_root_.Set.mem_range_self x) hy
  have hconn : IsPreconnected K := (convex_closedBall (0 : E3) 1).isPreconnected.image
    B (B.contMDiffOn_toFun.continuousOn.mono hB)
  refine ⟨B, hB, hBs, ?_⟩
  exact DifferentialGeometry.Topology.disjoint_image_of_involutive_of_disjoint_image_frontier
    h (fun x => neg_neg x) hK.isClosed hconn (hfront.symm ▸ _root_.Set.range_nonempty e) havoid

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_disjoint_antipodal_of_sphere_embedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_disjoint_antipodal_of_sphere_embedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_disjoint_antipodal_of_sphere_embedding ``Submission.DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_disjoint_antipodal_of_sphere_embedding

end DifferentialGeometry.Topology.ThreeManifold
