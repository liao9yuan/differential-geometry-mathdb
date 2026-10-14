import Submission.DifferentialGeometry.Topology.ThreeManifold.TwoBallCharts
import Submission.DifferentialGeometry.Topology.ThreeManifold.BallCapTrim

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E4 target :: scope.openDecls } }
private abbrev S3 := _root_.Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S3 target :: scope.openDecls } }

theorem exists_sphere_diffeomorph_of_ball_chart_cover
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (A B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hA : _root_.Metric.closedBall (0 : E3) 1 ⊆ A.source)
    (hB : _root_.Metric.closedBall (0 : E3) 1 ⊆ B.source)
    (hcover : B '' _root_.Metric.closedBall (0 : E3) 1 ∪ A '' _root_.Metric.closedBall (0 : E3) 1 = _root_.Set.univ) :
    ∃ (e : M ≃ₘ⟮𝓡 3,𝓡 3⟯ S3)
      (a b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞)
      (G : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞),
      a.source = _root_.Set.univ ∧ b.source = _root_.Set.univ ∧ _root_.Metric.closedBall (0 : E3) 1 ⊆ G.source ∧
      G '' _root_.Metric.ball (0 : E3) 1 = (B '' _root_.Metric.closedBall (0 : E3) 1)ᶜ ∧
      G '' _root_.Metric.closedBall (0 : E3) 1 = (B '' _root_.Metric.ball (0 : E3) 1)ᶜ ∧
      G '' _root_.Metric.sphere (0 : E3) 1 = B '' _root_.Metric.sphere (0 : E3) 1 ∧
      a '' _root_.Metric.closedBall (0 : E3) 1 = (b '' _root_.Metric.ball (0 : E3) 1)ᶜ ∧
      (∀ z ∈ _root_.Metric.closedBall (0 : E3) 1, e (B z) = a z) ∧
      (∃ D : E3 ≃ₘ[ℝ] E3,
        D '' _root_.Metric.closedBall (0 : E3) 1 = _root_.Metric.closedBall (0 : E3) 1 ∧
        ∀ z ∈ _root_.Metric.closedBall (0 : E3) 1, e (G (D z)) = b z) ∧
      ∃ U : Set M, IsOpen U ∧ B '' _root_.Metric.closedBall (0 : E3) 1 ⊆ U ∧
        U ⊆ (B.symm.trans a).source ∧ _root_.Set.EqOn e (B.symm.trans a) U := by
  obtain ⟨G,hG,hGo,hGc,hGs⟩ :=
    DifferentialGeometry.Topology.ThreeManifold.exists_complementary_ball_chart_of_ball_cap_cover
      A B hA hB hcover
  obtain ⟨e,a,b,ha,hb,hab,heB,D,hD,heG,U,hU,hBU,hUs,hEq⟩ :=
    exists_sphere_diffeomorph_of_complementary_ball_charts_eqOn_neighborhood B G hB hG hGo
  refine ⟨e.symm,a,b,G,ha,hb,hG,hGo,hGc,hGs,hab,?_,⟨D,hD,?_⟩,U,hU,hBU,hUs,hEq⟩
  · intro z hz
    exact (congrArg e.symm (heB z hz)).symm.trans (e.symm_apply_apply _)
  · intro z hz
    exact (congrArg e.symm (heG z hz)).symm.trans (e.symm_apply_apply _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_ball_chart_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_ball_chart_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_ball_chart_cover ``Submission.DifferentialGeometry.Topology.Manifold.exists_sphere_diffeomorph_of_ball_chart_cover

end DifferentialGeometry.Topology.Manifold
