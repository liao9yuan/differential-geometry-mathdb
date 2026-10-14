import Submission.DifferentialGeometry.Topology.Manifold.ScaledClosedBall
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E3 target :: scope.openDecls } }
private abbrev Ball (L : ℝ) := {x : E3 // ‖x‖ ≤ L}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.Ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.Ball target :: scope.openDecls } }

theorem closedBall_inclusion_mfderiv_bijective {L : ℝ} (hL : 0 < L) (x : Ball L) :
    letI := closedBallChartedSpace hL
    Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : Ball L → E3) x) := by
  let := closedBallChartedSpace hL
  exact bijective_mfderiv_of_isImmersionAt (𝓡∂ 3) (𝓡 3) _ x
    ((isSmoothEmbedding_closedBall_inclusion hL).isImmersion.isImmersionAt x) rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedBall_inclusion_mfderiv_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedBall_inclusion_mfderiv_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedBall_inclusion_mfderiv_bijective ``Submission.DifferentialGeometry.Topology.Manifold.closedBall_inclusion_mfderiv_bijective

def closedBallSmoothOrientation {L : ℝ} (hL : 0 < L)
    (o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3))) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    SmoothOrientation (𝓡∂ 3) (Ball L) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  exact pullbackSmoothOrientation (𝓡∂ 3) (𝓡 3) (Subtype.val : Ball L → E3)
    (isSmoothEmbedding_closedBall_inclusion hL).contMDiff
    (closedBall_inclusion_mfderiv_bijective hL) (euclideanSmoothOrientation E3 o)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedBallSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedBallSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedBallSmoothOrientation ``Submission.DifferentialGeometry.Topology.Manifold.closedBallSmoothOrientation

theorem closedBallSmoothOrientation_pushforward {L : ℝ} (hL : 0 < L)
    (o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3))) (x : Ball L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    tangentOrientationEquiv (differentialEquivOfBijective (𝓡∂ 3) (𝓡 3)
      (Subtype.val : Ball L → E3) (closedBall_inclusion_mfderiv_bijective hL) x).toLinearEquiv
        ((closedBallSmoothOrientation hL o).val x) = o := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  exact pullbackSmoothOrientation_pushforward (𝓡∂ 3) (𝓡 3) (Subtype.val : Ball L → E3)
    (isSmoothEmbedding_closedBall_inclusion hL).contMDiff
    (closedBall_inclusion_mfderiv_bijective hL) (euclideanSmoothOrientation E3 o) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedBallSmoothOrientation_pushforward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedBallSmoothOrientation_pushforward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedBallSmoothOrientation_pushforward ``Submission.DifferentialGeometry.Topology.Manifold.closedBallSmoothOrientation_pushforward
end DifferentialGeometry.Topology.Manifold
