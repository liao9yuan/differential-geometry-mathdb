import Submission.DifferentialGeometry.Topology.Manifold.ClosedBallBoundaryOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Module _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E3 target :: scope.openDecls } }
private abbrev E2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E2 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }
private abbrev Ball (L : ℝ) := {x : E3 // ‖x‖ ≤ L}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Ball target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instNonemptyBoundaryHEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace : Nonempty (HasSmoothBoundary.boundaryH (𝓡∂ 3)) :=
  show Nonempty E2 from inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instNonemptyBoundaryHEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instNonemptyBoundaryHEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instChartedSpaceE2BoundaryManifoldEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceOfIsManifoldSomeENatTop {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] : ChartedSpace E2 (BoundaryManifold (𝓡∂ 3) M) :=
  BoundaryManifold.chartedSpace (I := 𝓡∂ 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instChartedSpaceE2BoundaryManifoldEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceOfIsManifoldSomeENatTop
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instChartedSpaceE2BoundaryManifoldEuclideanSpaceRealFinOfNatNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceOfIsManifoldSomeENatTop target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] : IsManifold (𝓡 2) ∞ (BoundaryManifold (𝓡∂ 3) M) :=
  BoundaryManifold.isManifold (I := 𝓡∂ 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopBoundaryManifoldEuclideanHalfSpaceModelWithCornersEuclideanHalfSpace target :: scope.openDecls } }
private def b2 : _root_.Module.Basis (Fin 2) ℝ E2 := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.b2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.b2 target :: scope.openDecls } }
private def i2 : Fin 2 ≃ Fin (Module.finrank ℝ E2) := finCongr (by simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.i2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.i2 target :: scope.openDecls } }

private def i3 : Fin 3 ≃ Fin (Module.finrank ℝ E3) := finCongr (by simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.i3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.i3 target :: scope.openDecls } }
private def ballInclusionDerivative {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    Ball L → E3 ≃L[ℝ] E3 := by
  let := closedBallChartedSpace hL
  exact differentialEquivOfBijective (𝓡∂ 3) (𝓡 3) (Subtype.val : Ball L → E3)
    (closedBall_inclusion_mfderiv_bijective hL)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.ballInclusionDerivative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.ballInclusionDerivative target :: scope.openDecls } }

def closedBallTangentOrientationThree {L : ℝ} (hL : 0 < L) (o : Orientation ℝ E3 (Fin 3)) :
    letI := closedBallChartedSpace hL
    Ball L → Orientation ℝ E3 (Fin 3) := by
  let := closedBallChartedSpace hL
  exact fun x => Orientation.map (Fin 3) (ballInclusionDerivative hL x).symm.toLinearEquiv o

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedBallTangentOrientationThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedBallTangentOrientationThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedBallTangentOrientationThree ``Submission.DifferentialGeometry.Topology.Manifold.closedBallTangentOrientationThree

theorem closedBallTangentOrientationThree_eq {L : ℝ} (hL : 0 < L) (o : Orientation ℝ E3 (Fin 3)) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ x : Ball L, Orientation.reindex ℝ E3 i3 (closedBallTangentOrientationThree hL o x) =
      (closedBallSmoothOrientation hL (Orientation.reindex ℝ E3 i3 o)).val x := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro x
  change Orientation.reindex ℝ E3 i3 (Orientation.map (Fin 3) (ballInclusionDerivative hL x).symm.toLinearEquiv o) =
    tangentOrientationEquiv (ballInclusionDerivative hL x).symm.toLinearEquiv (Orientation.reindex ℝ E3 i3 o)
  rw [tangentOrientationEquiv_self]
  induction o using Module.Ray.ind
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedBallTangentOrientationThree_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedBallTangentOrientationThree_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedBallTangentOrientationThree_eq ``Submission.DifferentialGeometry.Topology.Manifold.closedBallTangentOrientationThree_eq

def closedBallBoundaryIntrinsicFrame {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    BoundaryManifold (𝓡∂ 3) (Ball L) → (ℝ × E2) ≃ₗ[ℝ] E3 := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  exact fun b => (hypersurfaceNormalFrameEquiv (closedBallBoundaryAmbient hL)
    (closedBallBoundaryRadialNormal hL) (closedBallBoundaryNormalFrame_bijective hL) b).toLinearEquiv.trans
      (ballInclusionDerivative hL b.val).symm.toLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedBallBoundaryIntrinsicFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedBallBoundaryIntrinsicFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedBallBoundaryIntrinsicFrame ``Submission.DifferentialGeometry.Topology.Manifold.closedBallBoundaryIntrinsicFrame

private def boundaryInclusionDerivative {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    BoundaryManifold (𝓡∂ 3) (Ball L) → E2 →L[ℝ] E3 := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  exact fun b => mfderiv (𝓡 2) (𝓡∂ 3) (boundaryInclusion (𝓡∂ 3) (Ball L)) b

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.boundaryInclusionDerivative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.boundaryInclusionDerivative target :: scope.openDecls } }
private def boundaryAmbientDerivative {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    BoundaryManifold (𝓡∂ 3) (Ball L) → E2 →L[ℝ] E3 := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  exact fun b => mfderiv (𝓡 2) (𝓡 3) (closedBallBoundaryAmbient hL) b

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.boundaryAmbientDerivative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.boundaryAmbientDerivative target :: scope.openDecls } }
private theorem boundary_inclusion_chain {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ b : BoundaryManifold (𝓡∂ 3) (Ball L),
      boundaryAmbientDerivative hL b = (ballInclusionDerivative hL b.val : E3 →L[ℝ] E3).comp
        (boundaryInclusionDerivative hL b) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro b
  exact mfderiv_comp b ((isSmoothEmbedding_closedBall_inclusion hL).contMDiff.mdifferentiableAt (by simp))
    ((boundaryInclusion_contMDiff (I := 𝓡∂ 3) (M := Ball L)).mdifferentiableAt (by simp))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.boundary_inclusion_chain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.boundary_inclusion_chain target :: scope.openDecls } }

theorem closedBallBoundaryIntrinsicFrame_apply {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ b : BoundaryManifold (𝓡∂ 3) (Ball L), ∀ t : ℝ, ∀ v : E2,
      let D : E2 →L[ℝ] E3 := mfderiv (𝓡 2) (𝓡∂ 3) (boundaryInclusion (𝓡∂ 3) (Ball L)) b
      closedBallBoundaryIntrinsicFrame hL b (t,v) =
        t • (differentialEquivOfBijective (𝓡∂ 3) (𝓡 3) (Subtype.val : Ball L → E3)
          (closedBall_inclusion_mfderiv_bijective hL) b.val).symm (closedBallBoundaryRadialNormal hL b) + D v := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro b t v
  change (ballInclusionDerivative hL b.val).symm
    (t • closedBallBoundaryRadialNormal hL b + boundaryAmbientDerivative hL b v) =
      t • (ballInclusionDerivative hL b.val).symm (closedBallBoundaryRadialNormal hL b) + boundaryInclusionDerivative hL b v
  rw [map_add, map_smul, boundary_inclusion_chain hL b]
  change t • (ballInclusionDerivative hL b.val).symm (closedBallBoundaryRadialNormal hL b) +
    (ballInclusionDerivative hL b.val).symm ((ballInclusionDerivative hL b.val) (boundaryInclusionDerivative hL b v)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedBallBoundaryIntrinsicFrame_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedBallBoundaryIntrinsicFrame_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedBallBoundaryIntrinsicFrame_apply ``Submission.DifferentialGeometry.Topology.Manifold.closedBallBoundaryIntrinsicFrame_apply

theorem closedBallBoundarySmoothOrientation_induced {L : ℝ} (hL : 0 < L) (o : Orientation ℝ E3 (Fin 3)) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ b : BoundaryManifold (𝓡∂ 3) (Ball L),
      (closedBallBoundarySmoothOrientation hL o).val b = Orientation.reindex ℝ E2 i2
        (normalFirstOrientation (closedBallBoundaryIntrinsicFrame hL b) b2 (closedBallTangentOrientationThree hL o b.val)) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro b
  rw [closedBallBoundarySmoothOrientation_apply]
  have h := normalFirstOrientation_map
    (hypersurfaceNormalFrameEquiv (closedBallBoundaryAmbient hL) (closedBallBoundaryRadialNormal hL)
      (closedBallBoundaryNormalFrame_bijective hL) b).toLinearEquiv
    (ballInclusionDerivative hL b.val).symm.toLinearEquiv b2 o
  exact congrArg (Orientation.reindex ℝ E2 i2) h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedBallBoundarySmoothOrientation_induced then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedBallBoundarySmoothOrientation_induced"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedBallBoundarySmoothOrientation_induced ``Submission.DifferentialGeometry.Topology.Manifold.closedBallBoundarySmoothOrientation_induced
end DifferentialGeometry.Topology.Manifold
