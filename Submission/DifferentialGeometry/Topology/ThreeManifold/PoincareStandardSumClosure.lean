import Submission.DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormOrientationClosure
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardModels
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedLawsAssembly
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ChoiceIndependence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem isPoincareStandard_connectedSum {M : ConnectedClosedOrientedManifold.{u} 3}
    {N : ConnectedClosedOrientedManifold.{u} 3}
    (hM : isPoincareStandard M.Carrier) (hN : isPoincareStandard N.Carrier) :
    isPoincareStandard (connectedSum M N).Carrier := by
  refine poincareStandardSumClosed_holds [M, N] ?_
  intro F hF
  rcases List.mem_cons.mp hF with rfl | hF
  · exact hM
  · rw [List.mem_singleton] at hF
    subst hF
    exact hN

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPoincareStandard_connectedSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPoincareStandard_connectedSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPoincareStandard_connectedSum ``Submission.DifferentialGeometry.Topology.isPoincareStandard_connectedSum

theorem isOrientedPoincareStandardSumClosed_holds :
    isOrientedPoincareStandardSumClosed.{u} :=
  isOrientedPoincareStandardSumClosed_of_connectedSumLaws connectedSumLaws_holds

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isOrientedPoincareStandardSumClosed_holds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isOrientedPoincareStandardSumClosed_holds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isOrientedPoincareStandardSumClosed_holds ``Submission.DifferentialGeometry.Topology.isOrientedPoincareStandardSumClosed_holds

theorem nonempty_smoothConnectedSum_sphere_sphereTwoTimesCircle :
    Nonempty (SmoothConnectedSum (orientedBallChart standardThreeSphereLift.{0})
      (orientedBallChart sphereTwoTimesCircleLift) boundaryAttachment) :=
  ⟨smoothConnectedSum standardThreeSphereLift.{0} sphereTwoTimesCircleLift
    (orientedBallChart standardThreeSphereLift.{0})
    (orientedBallChart sphereTwoTimesCircleLift) boundaryAttachment⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_smoothConnectedSum_sphere_sphereTwoTimesCircle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_smoothConnectedSum_sphere_sphereTwoTimesCircle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_smoothConnectedSum_sphere_sphereTwoTimesCircle ``Submission.DifferentialGeometry.Topology.nonempty_smoothConnectedSum_sphere_sphereTwoTimesCircle

theorem isPoincareStandard_connectedSum_sphere_sphereTwoTimesCircle :
    isPoincareStandard
      (connectedSum standardThreeSphereLift.{0} sphereTwoTimesCircleLift).Carrier :=
  isPoincareStandard_connectedSum isPoincareStandard_sphere
    isPoincareStandard_sphereTwoTimesCircleLift

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPoincareStandard_connectedSum_sphere_sphereTwoTimesCircle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPoincareStandard_connectedSum_sphere_sphereTwoTimesCircle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPoincareStandard_connectedSum_sphere_sphereTwoTimesCircle ``Submission.DifferentialGeometry.Topology.isPoincareStandard_connectedSum_sphere_sphereTwoTimesCircle

theorem isOrientedPoincareStandard_sphereTwoTimesCircleLift :
    isOrientedPoincareStandard sphereTwoTimesCircleLift.toClosedOrientedManifold :=
  isOrientedPoincareStandard_of_standard_factor sphereTwoTimesCircleLift
    isStandardFactor_sphereTwoTimesCircleLift

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isOrientedPoincareStandard_sphereTwoTimesCircleLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isOrientedPoincareStandard_sphereTwoTimesCircleLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isOrientedPoincareStandard_sphereTwoTimesCircleLift ``Submission.DifferentialGeometry.Topology.isOrientedPoincareStandard_sphereTwoTimesCircleLift

theorem nonempty_orientedDiffeomorph_connectedSum_sphere_sphereTwoTimesCircle :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum standardThreeSphereLift.{0} sphereTwoTimesCircleLift).toClosedOrientedManifold
      sphereTwoTimesCircleLift.toClosedOrientedManifold) :=
  connectedSum_sphere_left_of_binaryConnectedSumLaws binaryConnectedSumLaws_holds
    sphereTwoTimesCircleLift

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_connectedSum_sphere_sphereTwoTimesCircle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_connectedSum_sphere_sphereTwoTimesCircle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_connectedSum_sphere_sphereTwoTimesCircle ``Submission.DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_connectedSum_sphere_sphereTwoTimesCircle

theorem SphericalCutCapTransition.componentwise_isPoincareStandard_of_localReconstruction
    {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)
    (h : E.localReconstruction) (hctrl : E.poincareControlled)
    (hnext : ∀ C : ConnectedComponents Q.Carrier, isPoincareStandard (Q.component C).Carrier) :
    ∀ C : ConnectedComponents M.Carrier, isPoincareStandard (M.component C).Carrier :=
  E.componentwise_isPoincareStandard h hctrl hnext poincareStandardSumClosed_holds

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.componentwise_isPoincareStandard_of_localReconstruction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.componentwise_isPoincareStandard_of_localReconstruction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.componentwise_isPoincareStandard_of_localReconstruction ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.componentwise_isPoincareStandard_of_localReconstruction

theorem FiniteCutCapTrace.componentwise_isPoincareStandard_of_localReconstruction
    (T : FiniteCutCapTrace.{u})
    (h : ∀ i : Fin T.eventCount, (T.transition i).localReconstruction)
    (hctrl : T.poincareControlled) (hext : T.extinct) :
    ∀ i : Fin (T.eventCount + 1), ∀ C : ConnectedComponents (T.stage i).Carrier,
      isPoincareStandard ((T.stage i).component C).Carrier :=
  T.componentwise_isPoincareStandard h hctrl hext poincareStandardSumClosed_holds

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.componentwise_isPoincareStandard_of_localReconstruction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.componentwise_isPoincareStandard_of_localReconstruction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.componentwise_isPoincareStandard_of_localReconstruction ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.componentwise_isPoincareStandard_of_localReconstruction

theorem FiniteCutCapTrace.isPoincareStandard_of_initialIdentification_of_localReconstruction
    (T : FiniteCutCapTrace.{u})
    (h : ∀ i : Fin T.eventCount, (T.transition i).localReconstruction)
    (hctrl : T.poincareControlled) (hext : T.extinct)
    (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier]
    (Φ : T.InitialIdentification M) : isPoincareStandard M.Carrier :=
  T.isPoincareStandard_of_initialIdentification h hctrl hext
    poincareStandardSumClosed_holds M Φ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.isPoincareStandard_of_initialIdentification_of_localReconstruction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.isPoincareStandard_of_initialIdentification_of_localReconstruction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.isPoincareStandard_of_initialIdentification_of_localReconstruction ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.isPoincareStandard_of_initialIdentification_of_localReconstruction

end DifferentialGeometry.Topology

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem isPoincareStandard_smoothConnectedSum
    (M N : ConnectedClosedOrientedManifold.{u} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold)
    (hM : isPoincareStandard M.Carrier) (hN : isPoincareStandard N.Carrier) :
    isPoincareStandard
      (smoothConnectedSum M N c d boundaryAttachment).toConnectedClosedOrientedManifold.Carrier := by
  obtain ⟨e⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts
    c (orientedBallChart M) d (orientedBallChart N) boundaryAttachment
  exact isPoincareStandard_of_diffeomorph e.val
    (isPoincareStandard_connectedSum hM hN)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPoincareStandard_smoothConnectedSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPoincareStandard_smoothConnectedSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPoincareStandard_smoothConnectedSum ``Submission.DifferentialGeometry.Topology.isPoincareStandard_smoothConnectedSum

end DifferentialGeometry.Topology
