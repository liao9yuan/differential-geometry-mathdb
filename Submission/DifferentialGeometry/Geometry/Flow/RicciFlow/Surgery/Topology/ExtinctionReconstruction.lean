import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapPoincareStandard
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinction
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapIncidence
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapGluing
import Submission.DifferentialGeometry.Topology.ThreeManifold.CutCapReconstruction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

namespace PoincareControlledExtinction

variable {M : ClosedOrientedManifold.{u} 3}
  {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}

theorem isPoincareStandard [ConnectedSpace M.Carrier] (W : PoincareControlledExtinction M g)
    (hsum : ∀ i : Fin W.history.eventCount,
      (W.history.cutCapTrace.transition i).componentConnectedSumDecomposition)
    (hsumClosed : poincareStandardSumClosed.{u}) :
    isPoincareStandard M.Carrier :=
  W.history.cutCapTrace.isPoincareStandard_of_initialIdentification
    (fun i => (W.history.cutCapTrace.transition i).localReconstruction_of_incidenceGluing
      (fun C => FiniteCutCapTrace.cutIncidenceGraph_connected _ i C) (hsum i))
    W.controlled (W.history.extinct_trace W.extinct) hsumClosed M W.initial.cutCapIdentification

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.isPoincareStandard then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.isPoincareStandard"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.isPoincareStandard ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.isPoincareStandard

end PoincareControlledExtinction


namespace PoincareControlledExtinction
variable {M : ClosedOrientedManifold.{u} 3}
  {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}

theorem isPoincareStandard_of_controlledExtinction [ConnectedSpace M.Carrier]
    (W : PoincareControlledExtinction M g) :
    DifferentialGeometry.Topology.isPoincareStandard M.Carrier :=
  W.history.cutCapTrace.isPoincareStandard_of_initialIdentification_of_poincareControlled_extinct
    W.controlled_extinct_trace.1 W.controlled_extinct_trace.2 M W.initialCutCapIdentification

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.isPoincareStandard_of_controlledExtinction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.isPoincareStandard_of_controlledExtinction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.isPoincareStandard_of_controlledExtinction ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.PoincareControlledExtinction.isPoincareStandard_of_controlledExtinction

end PoincareControlledExtinction

end DifferentialGeometry.PDE.RicciFlow.Surgery
