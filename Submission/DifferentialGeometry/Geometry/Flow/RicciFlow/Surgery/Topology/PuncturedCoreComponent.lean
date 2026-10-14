import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCoreRetraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

def componentwiseSimplyConnected : Prop :=
  ∀ c : ConnectedComponents ↥T.puncturedCore, SimplyConnectedSpace (ComponentCarrier c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.componentwiseSimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.componentwiseSimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.componentwiseSimplyConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.componentwiseSimplyConnected

theorem componentwiseSimplyConnected_of_simplyConnectedSpace
    [SimplyConnectedSpace ↥T.puncturedCore] : T.componentwiseSimplyConnected := by
  intro c
  have hsub : Subsingleton (ConnectedComponents ↥T.puncturedCore) := inferInstance
  have hset : {x : ↥T.puncturedCore | ConnectedComponents.mk x = c} = univ := by
    ext x
    exact ⟨fun _ => trivial, fun _ => hsub.elim _ _⟩
  have he : ComponentCarrier c ≃ₜ ↥T.puncturedCore :=
    (Homeomorph.setCongr hset).trans (Homeomorph.Set.univ ↥T.puncturedCore)
  exact he.toHomotopyEquiv.simplyConnectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.componentwiseSimplyConnected_of_simplyConnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.componentwiseSimplyConnected_of_simplyConnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.componentwiseSimplyConnected_of_simplyConnectedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.componentwiseSimplyConnected_of_simplyConnectedSpace

theorem componentwiseSimplyConnected_of_isEmpty [IsEmpty T.Index] [SimplyConnectedSpace M] :
    T.componentwiseSimplyConnected :=
  @componentwiseSimplyConnected_of_simplyConnectedSpace M _ T
    ((simplyConnectedSpace_puncturedCore_iff_of_isEmpty T).mpr inferInstance)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.componentwiseSimplyConnected_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.componentwiseSimplyConnected_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.componentwiseSimplyConnected_of_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem.componentwiseSimplyConnected_of_isEmpty

end TubeSystem

theorem not_forall_simplyConnectedSpace_puncturedCore :
    ¬ (∀ (M : Type) (_ : TopologicalSpace M) (T : TubeSystem M),
      SimplyConnectedSpace ↥T.puncturedCore) := by
  intro h
  obtain ⟨M, htop, T, _, hcon⟩ :=
    exists_tubeSystem_nonemptyIndex_not_simplyConnectedSpace_puncturedCore
  exact hcon (h M htop T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_forall_simplyConnectedSpace_puncturedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_forall_simplyConnectedSpace_puncturedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_forall_simplyConnectedSpace_puncturedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_forall_simplyConnectedSpace_puncturedCore

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
