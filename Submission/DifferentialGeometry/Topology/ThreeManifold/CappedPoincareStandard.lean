import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapCappedPresentationRealization
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardSumClosure
import Submission.DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormOrientationClosure

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.SphericalCutCapTransition

universe u
variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem isOrientedPoincareStandard_capComponent
    (hnext : ∀ K : ConnectedComponents Q.Carrier,
      isOrientedPoincareStandard (Q.component K).toClosedOrientedManifold)
    (hdiscard : ∀ K : ConnectedComponents E.discarded.Carrier,
      isOrientedPoincareStandard (E.discarded.component K).toClosedOrientedManifold)
    (K : ConnectedComponents E.capped.Carrier) :
    isOrientedPoincareStandard (E.capped.component K).toClosedOrientedManifold := by
  let e : ClosedOrientedManifold.OrientedDiffeomorph E.capped
      (ClosedOrientedManifold.sum Q E.discarded) :=
    ⟨E.presentation, E.presentation_preservesOrientation⟩
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe K
  let F := e.component (ConnectedComponents.mk x)
  apply isOrientedPoincareStandard_of_orientedDiffeomorph F
  have hcomponent : e.val.continuous.connectedComponentsMap (ConnectedComponents.mk x) =
      ConnectedComponents.mk (E.presentation x) := Continuous.connectedComponentsMap_mk _ _
  rw [hcomponent]
  cases hy : E.presentation x with
  | inl q =>
    exact isOrientedPoincareStandard_of_orientedDiffeomorph
      (ClosedOrientedManifold.sumComponentInl_orientedDiffeomorph (X := Q) (Y := E.discarded) q)
      (hnext (ConnectedComponents.mk q))
  | inr d =>
    exact isOrientedPoincareStandard_of_orientedDiffeomorph
      (ClosedOrientedManifold.sumComponentInr_orientedDiffeomorph (X := Q) (Y := E.discarded) d)
      (hdiscard (ConnectedComponents.mk d))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isOrientedPoincareStandard_capComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isOrientedPoincareStandard_capComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isOrientedPoincareStandard_capComponent ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isOrientedPoincareStandard_capComponent

theorem isOrientedPoincareStandard_capComponent_of_poincareControlled
    (hctrl : E.poincareControlled)
    (hnext : ∀ K : ConnectedComponents Q.Carrier,
      isPoincareStandard (Q.component K).Carrier)
    (K : ConnectedComponents E.capped.Carrier) :
    isOrientedPoincareStandard (E.capped.component K).toClosedOrientedManifold :=
  E.isOrientedPoincareStandard_capComponent
    (fun K => poincareStandardOrientationRefinement_holds (Q.component K) (hnext K))
    (fun K => poincareStandardOrientationRefinement_holds (E.discarded.component K) (hctrl K)) K

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isOrientedPoincareStandard_capComponent_of_poincareControlled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isOrientedPoincareStandard_capComponent_of_poincareControlled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isOrientedPoincareStandard_capComponent_of_poincareControlled ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isOrientedPoincareStandard_capComponent_of_poincareControlled

theorem isOrientedPoincareStandard_capComponent_finiteConnectedSum
    (hnext : ∀ K : ConnectedComponents Q.Carrier,
      isOrientedPoincareStandard (Q.component K).toClosedOrientedManifold)
    (hdiscard : ∀ K : ConnectedComponents E.discarded.Carrier,
      isOrientedPoincareStandard (E.discarded.component K).toClosedOrientedManifold)
    (L : List (ConnectedComponents E.capped.Carrier)) (k : ℕ) :
    isOrientedPoincareStandard
      (finiteConnectedSum (L.map E.capped.component ++
        List.replicate k (sphereTwoTimesCircleLift.ulift.{0, u}))).toClosedOrientedManifold := by
  apply isOrientedPoincareStandardSumClosed_holds
  intro F hF
  rcases List.mem_append.mp hF with hF | hF
  · obtain ⟨K, _, rfl⟩ := List.mem_map.mp hF
    exact E.isOrientedPoincareStandard_capComponent hnext hdiscard K
  · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hF
    apply isOrientedPoincareStandard_of_standard_factor
    apply isStandardFactor_of_isSphereTwoTimesCircleFactor
    obtain ⟨f, hf⟩ := isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift
    let U := (ClosedOrientedManifold.uliftOrientedDiffeomorph.{0, u}
      sphereTwoTimesCircleLift.toClosedOrientedManifold).symm
    exact ⟨U.val.trans f, Diffeomorph.preservesOrientation_trans U.property hf⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.isOrientedPoincareStandard_capComponent_finiteConnectedSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.isOrientedPoincareStandard_capComponent_finiteConnectedSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.isOrientedPoincareStandard_capComponent_finiteConnectedSum ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.isOrientedPoincareStandard_capComponent_finiteConnectedSum

end DifferentialGeometry.Topology.SphericalCutCapTransition
