import Submission.DifferentialGeometry.Topology.ThreeManifold.SmoothSchoenflies
import Submission.DifferentialGeometry.Topology.SphereSeparation.SmoothSchoenfliesBallFilling
import Submission.DifferentialGeometry.Topology.SphereSeparation.BallSideRelations
import Submission.DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import Submission.DifferentialGeometry.Topology.OpenPartialHomeomorph.Images

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
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.S2 target :: scope.openDecls } }

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]

theorem exists_ball_chart_inside_ball_of_sphere_embedding
    (C : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hC : _root_.Metric.closedBall (0 : E3) 1 ⊆ C.source)
    (e : S2 → M) (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hinside : _root_.Set.range e ⊆ C '' _root_.Metric.ball (0 : E3) 1) :
    ∃ B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞,
      _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source ∧
      B '' _root_.Metric.sphere (0 : E3) 1 = _root_.Set.range e ∧
      B '' _root_.Metric.closedBall (0 : E3) 1 ⊆ C '' _root_.Metric.ball (0 : E3) 1 := by
  have hes : _root_.Set.range e ⊆ C.target := by
    rintro x hx
    obtain ⟨y, hy, rfl⟩ := hinside hx
    exact C.map_source (hC (_root_.Metric.ball_subset_closedBall hy))
  let f : S2 → E3 := C.symm ∘ e
  have hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph C.symm he hes
  have hfball : _root_.Set.range f ⊆ _root_.Metric.ball (0 : E3) 1 := by
    rintro x ⟨q, rfl⟩
    obtain ⟨z, hz, heq⟩ := hinside (_root_.Set.mem_range_self q)
    change C.symm (e q) ∈ _
    rw [← heq]
    have hinv : C.toPartialEquiv.symm (C.toPartialEquiv z) = z :=
      C.toPartialEquiv.left_inv (hC (_root_.Metric.ball_subset_closedBall hz))
    change C.toPartialEquiv.symm (C.toPartialEquiv z) ∈ _root_.Metric.ball (0 : E3) 1
    rw [hinv]
    exact hz
  have hfconn : IsConnected (_root_.Set.range f) := by
    have hs : IsConnected (_root_.Set.univ : Set S2) := by
      let _ : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
        (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [E3]))
          (0 : E3) zero_le_one)
      exact isConnected_univ
    simpa only [_root_.Set.image_univ] using hs.image f hf.contMDiff.continuous.continuousOn
  let d := SphereSeparation.jordanBrouwer_openThreeSpace f hf (Diffeomorph.refl (𝓡 3) E3 ∞)
  have hdsub : closure d.compactSide ⊆ _root_.Metric.ball (0 : E3) 1 := by
    apply SphereSeparation.standardUnitSphereSides.closure_compactSide_subset_of_sphere_subset
      d.toSphereSides ?_ hfconn hfball
    rw [_root_.Set.disjoint_left]
    intro x hxS hxf
    have hball := hfball hxf
    exact (mem_ball.mp hball).ne (mem_sphere.mp hxS)
  have hSch : SphereSeparation.smoothSchoenfliesThree :=
    SphereSeparation.smoothSchoenfliesThree_iff_exists_ambient_diffeomorph.mpr
      smooth_schoenflies_three
  obtain ⟨D, hD⟩ :=
    SphereSeparation.smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling.mp hSch f hf
  have hDclosed : D '' _root_.Metric.closedBall (0 : E3) 1 = closure d.compactSide := by
    calc
      _ = D '' closure (_root_.Metric.ball (0 : E3) 1) := by rw [closure_ball _ one_ne_zero]
      _ = closure (D '' _root_.Metric.ball (0 : E3) 1) := D.toHomeomorph.image_closure _
      _ = _ := by rw [hD]
  have hDsphere : D '' _root_.Metric.sphere (0 : E3) 1 = _root_.Set.range f := by
    calc
      _ = D '' frontier (_root_.Metric.ball (0 : E3) 1) := by rw [frontier_ball _ one_ne_zero]
      _ = frontier (D '' _root_.Metric.ball (0 : E3) 1) := D.toHomeomorph.image_frontier _
      _ = _ := by rw [hD]; exact d.frontier_compactSide
  let B := D.toPartialDiffeomorph.trans C
  refine ⟨B, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨mem_univ _, hC (_root_.Metric.ball_subset_closedBall (hdsub (hDclosed ▸ _root_.Set.mem_image_of_mem D hx)))⟩
  · change (C ∘ D) '' _root_.Metric.sphere (0 : E3) 1 = _root_.Set.range e
    rw [_root_.Set.image_comp, hDsphere, ← _root_.Set.range_comp]
    apply congrArg _root_.Set.range
    funext q
    exact C.right_inv (hes (_root_.Set.mem_range_self q))
  · change (C ∘ D) '' _root_.Metric.closedBall (0 : E3) 1 ⊆ C '' _root_.Metric.ball (0 : E3) 1
    rw [_root_.Set.image_comp, hDclosed]
    exact _root_.Set.image_mono hdsub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_inside_ball_of_sphere_embedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_inside_ball_of_sphere_embedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_inside_ball_of_sphere_embedding ``Submission.DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_inside_ball_of_sphere_embedding

end DifferentialGeometry.Topology.ThreeManifold
