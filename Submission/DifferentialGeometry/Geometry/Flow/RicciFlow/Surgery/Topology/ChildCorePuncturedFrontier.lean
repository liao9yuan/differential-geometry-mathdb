import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCarrierSeamCollarReduction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PuncturedCoreComponent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Topology

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem puncturedCore_global_hypothesis_refuted :
    (∃ (M : Type) (_ : TopologicalSpace M) (T : TubeSystem M),
        ¬ SimplyConnectedSpace ↥T.puncturedCore) ∧
      (∃ (M : Type) (_ : TopologicalSpace M) (T : TubeSystem M),
        Nonempty T.Index ∧ ¬ SimplyConnectedSpace ↥T.puncturedCore) :=
  ⟨exists_tubeSystem_not_simplyConnectedSpace_puncturedCore,
    exists_tubeSystem_nonemptyIndex_not_simplyConnectedSpace_puncturedCore⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.puncturedCore_global_hypothesis_refuted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.puncturedCore_global_hypothesis_refuted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.puncturedCore_global_hypothesis_refuted ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.puncturedCore_global_hypothesis_refuted

theorem componentwiseSimplyConnected_emptyTubeSystem_of_totallyDisconnected
    (M : Type*) [TopologicalSpace M] [TotallyDisconnectedSpace M] :
    (emptyTubeSystem M).componentwiseSimplyConnected := by
  intro c
  have hne : Nonempty (ComponentCarrier c) := by
    obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe c
    exact ⟨⟨x, hx⟩⟩
  have hsub : Subsingleton (ComponentCarrier c) :=
    ⟨fun x y => Subtype.ext (by
      have hcomp : x.1 ∈ connectedComponent y.1 :=
        ConnectedComponents.coe_eq_coe'.mp (x.2.trans y.2.symm)
      have hsing : connectedComponent y.1 = {y.1} := connectedComponent_eq_singleton y.1
      rw [hsing] at hcomp
      simpa using hcomp)⟩
  exact SimplyConnectedSpace.ofContractible (ComponentCarrier c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.componentwiseSimplyConnected_emptyTubeSystem_of_totallyDisconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.componentwiseSimplyConnected_emptyTubeSystem_of_totallyDisconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.componentwiseSimplyConnected_emptyTubeSystem_of_totallyDisconnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.componentwiseSimplyConnected_emptyTubeSystem_of_totallyDisconnected

theorem exists_tubeSystem_componentwiseSimplyConnected_not_simplyConnectedSpace :
    ∃ (M : Type) (_ : TopologicalSpace M) (T : TubeSystem M),
      T.componentwiseSimplyConnected ∧ ¬ SimplyConnectedSpace ↥T.puncturedCore :=
  ⟨Bool, inferInstance, emptyTubeSystem Bool,
    componentwiseSimplyConnected_emptyTubeSystem_of_totallyDisconnected Bool,
    @TubeSystem.not_simplyConnectedSpace_puncturedCore_of_not_pathConnected
      Bool _ (emptyTubeSystem Bool) ⟨fun a => a.elim⟩
      (not_pathConnectedSpace_of_totallyDisconnectedSpace_of_nontrivial (X := Bool))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_tubeSystem_componentwiseSimplyConnected_not_simplyConnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_tubeSystem_componentwiseSimplyConnected_not_simplyConnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_tubeSystem_componentwiseSimplyConnected_not_simplyConnectedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_tubeSystem_componentwiseSimplyConnected_not_simplyConnectedSpace

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

def ComponentwisePuncturedCoreSimpleConnected : Prop :=
  ∀ c : ConnectedComponents Q.Carrier,
    SimplyConnectedSpace ↥(E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ComponentwisePuncturedCoreSimpleConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ComponentwisePuncturedCoreSimpleConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ComponentwisePuncturedCoreSimpleConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.ComponentwisePuncturedCoreSimpleConnected

theorem nonempty_puncturedCoreComponent_childCoreComponent (c : ConnectedComponents Q.Carrier) :
    (E.trace.tubes.puncturedCoreComponent (E.childCoreComponent c)).Nonempty := by
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (E.childCoreComponent c)
  exact ⟨⟨(x : E.trace.tubes.core), E.trace.tubes.core_subset_puncturedCore x.2⟩,
    E.trace.tubes.mem_puncturedCoreComponent_of_mem_connectedComponents hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_puncturedCoreComponent_childCoreComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_puncturedCoreComponent_childCoreComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_puncturedCoreComponent_childCoreComponent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.nonempty_puncturedCoreComponent_childCoreComponent

theorem componentwisePuncturedCore_of_childCoreSimplyConnected
    (h : ∀ c : ConnectedComponents Q.Carrier, SimplyConnectedSpace (E.ChildCore c)) :
    E.ComponentwisePuncturedCoreSimpleConnected :=
  fun c => (E.trace.tubes.simplyConnectedSpace_puncturedCoreComponent_iff_coreComponent
    (fun a => E.tube_smooth a) (E.childCoreComponent c)).mpr (h c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.componentwisePuncturedCore_of_childCoreSimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.componentwisePuncturedCore_of_childCoreSimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.componentwisePuncturedCore_of_childCoreSimplyConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.componentwisePuncturedCore_of_childCoreSimplyConnected

theorem childCoreSimplyConnected_of_componentwisePuncturedCore
    (h : E.ComponentwisePuncturedCoreSimpleConnected) :
    ∀ c : ConnectedComponents Q.Carrier, SimplyConnectedSpace (E.ChildCore c) :=
  fun c => E.simplyConnectedSpace_childCore_of_puncturedCoreComponent c (h c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreSimplyConnected_of_componentwisePuncturedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreSimplyConnected_of_componentwisePuncturedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreSimplyConnected_of_componentwisePuncturedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.childCoreSimplyConnected_of_componentwisePuncturedCore

theorem child_simplyConnected_of_frontiers
    (hcover : E.childCoreCapCoverProducer)
    (hpc : E.ComponentwisePuncturedCoreSimpleConnected)
    (c : ConnectedComponents Q.Carrier)
    [SimplyConnectedSpace (P.component (E.childParent c)).Carrier] :
    SimplyConnectedSpace (Q.component c).Carrier :=
  E.child_simplyConnected_of_childCarrierCoreCapCover
    (fun c' h' => Classical.choice (hcover c' h')) (fun c' => hpc c') c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.child_simplyConnected_of_frontiers then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.child_simplyConnected_of_frontiers"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.child_simplyConnected_of_frontiers ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.child_simplyConnected_of_frontiers

theorem child_simplyConnected_of_frontiers_apply
    (hcover : E.childCoreCapCoverProducer)
    (hpc : E.ComponentwisePuncturedCoreSimpleConnected)
    (c : ConnectedComponents Q.Carrier)
    (h : SimplyConnectedSpace (P.component (E.childParent c)).Carrier) :
    SimplyConnectedSpace (Q.component c).Carrier :=
  @SmoothCutCapTransition.child_simplyConnected_of_frontiers P Q D N E hcover hpc c h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.child_simplyConnected_of_frontiers_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.child_simplyConnected_of_frontiers_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.child_simplyConnected_of_frontiers_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition.child_simplyConnected_of_frontiers_apply

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
