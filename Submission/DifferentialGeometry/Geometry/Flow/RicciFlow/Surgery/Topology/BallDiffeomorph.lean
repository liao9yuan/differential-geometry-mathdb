import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapCompletion
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import Submission.DifferentialGeometry.Topology.Manifold.ClosedBall

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (DifferentialGeometry.Topology.ClosedCell (m + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc m

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell (m : ℕ) :
    IsManifold (𝓡∂ (m + 1)) (⊤ : ℕ∞) (DifferentialGeometry.Topology.ClosedCell (m + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold m

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell target :: scope.openDecls } }

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage}

noncomputable def closedCellBallDiffeomorph (X : SmoothCutCapTransition P Q D N) :
    letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := X.ballCharts
    letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := X.ballSmooth
    DifferentialGeometry.Topology.ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall := by
  letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := X.ballCharts
  letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := X.ballSmooth
  let e0 : DifferentialGeometry.Topology.ClosedCell 3 ≃ ThreeBall :=
    Equiv.subtypeEquivRight (fun x => by simp [Metric.mem_closedBall, dist_eq_norm])
  have hcont : Continuous (e0 : DifferentialGeometry.Topology.ClosedCell 3 → ThreeBall) :=
    continuous_subtype_val.subtype_mk _
  have hcont' : Continuous (e0.symm : ThreeBall → DifferentialGeometry.Topology.ClosedCell 3) :=
    continuous_subtype_val.subtype_mk _
  have hto : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞
      (e0 : DifferentialGeometry.Topology.ClosedCell 3 → ThreeBall) := by
    intro x
    refine (ContMDiffAt.iff_comp_isImmersionAt
      (hφ := X.ball_induced.isImmersion.isImmersionAt (e0 x))).mpr ⟨hcont.continuousAt, ?_⟩
    have h : (Subtype.val ∘ (e0 : DifferentialGeometry.Topology.ClosedCell 3 → ThreeBall)) =
        (Subtype.val : DifferentialGeometry.Topology.ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) := by
      funext y
      rfl
    rw [h]
    exact (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion 2).contMDiff.contMDiffAt
  have hfrom : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞
      (e0.symm : ThreeBall → DifferentialGeometry.Topology.ClosedCell 3) := by
    intro y
    refine (ContMDiffAt.iff_comp_isImmersionAt
      (hφ := (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion
        2).isImmersion.isImmersionAt (e0.symm y))).mpr ⟨hcont'.continuousAt, ?_⟩
    have h : (Subtype.val ∘ (e0.symm : ThreeBall → DifferentialGeometry.Topology.ClosedCell 3)) =
        (Subtype.val : ThreeBall → EuclideanSpace ℝ (Fin 3)) := by
      funext z
      rfl
    rw [h]
    exact X.ball_induced.contMDiff.contMDiffAt
  exact ⟨e0, hto, hfrom⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.closedCellBallDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.closedCellBallDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.closedCellBallDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.closedCellBallDiffeomorph

theorem cap_isSmoothEmbedding_closedCell (X : SmoothCutCapTransition P Q D N)
    (b : X.trace.tubes.Boundary) :
    letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := X.ballCharts
    letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := X.ballSmooth
    _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
      (fun z : DifferentialGeometry.Topology.ClosedCell 3 =>
        X.trace.capping.cap b (X.closedCellBallDiffeomorph z)) := by
  let thisBall : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := X.ballCharts
  let thisSmooth : IsManifold (𝓡∂ 3) ∞ ThreeBall := X.ballSmooth
  exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_precomp
    (I := 𝓡∂ 3) (J := ThreeModel) (M := ThreeBall) (N := N.Carrier)
    (P := DifferentialGeometry.Topology.ClosedCell 3)
    (X.trace.capping.cap b) (X.cap_smooth b) (X.closedCellBallDiffeomorph)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.cap_isSmoothEmbedding_closedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.cap_isSmoothEmbedding_closedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.cap_isSmoothEmbedding_closedCell ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.cap_isSmoothEmbedding_closedCell

theorem closedCellBallDiffeomorph_sphereToClosedCell (X : SmoothCutCapTransition P Q D N)
    (z : Sphere 2) :
    letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := X.ballCharts
    letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := X.ballSmooth
    X.closedCellBallDiffeomorph (DifferentialGeometry.Topology.sphereToClosedCell z) =
      sphereToThreeBall z := by
  let thisBall : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := X.ballCharts
  let thisSmooth : IsManifold (𝓡∂ 3) ∞ ThreeBall := X.ballSmooth
  apply Subtype.ext
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.closedCellBallDiffeomorph_sphereToClosedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.closedCellBallDiffeomorph_sphereToClosedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.closedCellBallDiffeomorph_sphereToClosedCell ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.closedCellBallDiffeomorph_sphereToClosedCell

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
