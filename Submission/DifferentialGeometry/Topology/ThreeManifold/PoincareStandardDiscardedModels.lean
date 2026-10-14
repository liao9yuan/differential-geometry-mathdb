import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscarded
import Submission.DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormProjective

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u

def projectiveThreeSpaceLift : ConnectedClosedOrientedManifold.{u} 3 :=
  ConnectedClosedOrientedManifold.ulift.{0, u} SphericalSpaceFormGroup.antipodal.manifold

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.projectiveThreeSpaceLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.projectiveThreeSpaceLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.projectiveThreeSpaceLift ``Submission.DifferentialGeometry.Topology.projectiveThreeSpaceLift

theorem isStandardFactor_projectiveThreeSpaceLift :
    isStandardFactor projectiveThreeSpaceLift.{u} :=
  Or.inl ⟨SphericalSpaceFormGroup.antipodal,
    ⟨(ClosedOrientedManifold.uliftOrientedDiffeomorph
      SphericalSpaceFormGroup.antipodal.manifold.toClosedOrientedManifold).symm⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isStandardFactor_projectiveThreeSpaceLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isStandardFactor_projectiveThreeSpaceLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isStandardFactor_projectiveThreeSpaceLift ``Submission.DifferentialGeometry.Topology.isStandardFactor_projectiveThreeSpaceLift

theorem isPoincareStandard_projectiveThreeSpaceLift :
    isPoincareStandard projectiveThreeSpaceLift.{u}.Carrier :=
  isPoincareStandard_of_standard_factor projectiveThreeSpaceLift.{u}
    isStandardFactor_projectiveThreeSpaceLift

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPoincareStandard_projectiveThreeSpaceLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPoincareStandard_projectiveThreeSpaceLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPoincareStandard_projectiveThreeSpaceLift ``Submission.DifferentialGeometry.Topology.isPoincareStandard_projectiveThreeSpaceLift

theorem nonempty_projectiveThreeSpaceLift :
    Nonempty projectiveThreeSpaceLift.{u}.Carrier := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_projectiveThreeSpaceLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_projectiveThreeSpaceLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_projectiveThreeSpaceLift ``Submission.DifferentialGeometry.Topology.nonempty_projectiveThreeSpaceLift

def isProjectiveThreeSpaceConnectedSum
    (M : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  Nonempty (ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
    (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isProjectiveThreeSpaceConnectedSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isProjectiveThreeSpaceConnectedSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isProjectiveThreeSpaceConnectedSum ``Submission.DifferentialGeometry.Topology.isProjectiveThreeSpaceConnectedSum

theorem isPoincareStandard_of_isProjectiveThreeSpaceConnectedSum
    {M : ConnectedClosedOrientedManifold.{u} 3}
    (h : isProjectiveThreeSpaceConnectedSum M) : isPoincareStandard M.Carrier := by
  obtain ⟨ρ⟩ := h
  exact isPoincareStandard_of_diffeomorph ρ.1
    (isPoincareStandard_connectedSum_of_standardFactor projectiveThreeSpaceLift
      projectiveThreeSpaceLift isStandardFactor_projectiveThreeSpaceLift
      isStandardFactor_projectiveThreeSpaceLift)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPoincareStandard_of_isProjectiveThreeSpaceConnectedSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPoincareStandard_of_isProjectiveThreeSpaceConnectedSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPoincareStandard_of_isProjectiveThreeSpaceConnectedSum ``Submission.DifferentialGeometry.Topology.isPoincareStandard_of_isProjectiveThreeSpaceConnectedSum

theorem isProjectiveThreeSpaceConnectedSum_self :
    isProjectiveThreeSpaceConnectedSum
      (connectedSum projectiveThreeSpaceLift.{u} projectiveThreeSpaceLift.{u}) :=
  ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isProjectiveThreeSpaceConnectedSum_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isProjectiveThreeSpaceConnectedSum_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isProjectiveThreeSpaceConnectedSum_self ``Submission.DifferentialGeometry.Topology.isProjectiveThreeSpaceConnectedSum_self

theorem nonempty_connectedSum_projectiveThreeSpaceLift :
    Nonempty (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).Carrier := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_connectedSum_projectiveThreeSpaceLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_connectedSum_projectiveThreeSpaceLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_connectedSum_projectiveThreeSpaceLift ``Submission.DifferentialGeometry.Topology.nonempty_connectedSum_projectiveThreeSpaceLift

theorem isPoincareStandard_connectedSum_projectiveThreeSpaceLift :
    isPoincareStandard (connectedSum projectiveThreeSpaceLift.{u}
      projectiveThreeSpaceLift.{u}).Carrier :=
  isPoincareStandard_of_isProjectiveThreeSpaceConnectedSum
    isProjectiveThreeSpaceConnectedSum_self

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPoincareStandard_connectedSum_projectiveThreeSpaceLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPoincareStandard_connectedSum_projectiveThreeSpaceLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPoincareStandard_connectedSum_projectiveThreeSpaceLift ``Submission.DifferentialGeometry.Topology.isPoincareStandard_connectedSum_projectiveThreeSpaceLift

def ClosedOrientedManifold.componentwiseStandardFactorOrProjectiveThreeSpaceSum
    (D : ClosedOrientedManifold.{u} 3) : Prop :=
  ∀ C : ConnectedComponents D.Carrier,
    isStandardFactor (D.component C) ∨
      isProjectiveThreeSpaceConnectedSum (D.component C)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentwiseStandardFactorOrProjectiveThreeSpaceSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentwiseStandardFactorOrProjectiveThreeSpaceSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentwiseStandardFactorOrProjectiveThreeSpaceSum ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentwiseStandardFactorOrProjectiveThreeSpaceSum

theorem componentwise_isPoincareStandard_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum
    (D : ClosedOrientedManifold.{u} 3)
    (h : D.componentwiseStandardFactorOrProjectiveThreeSpaceSum) :
    ∀ C : ConnectedComponents D.Carrier, isPoincareStandard (D.component C).Carrier := by
  intro C
  rcases h C with h | h
  · exact isPoincareStandard_of_standard_factor (D.component C) h
  · exact isPoincareStandard_of_isProjectiveThreeSpaceConnectedSum h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.componentwise_isPoincareStandard_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.componentwise_isPoincareStandard_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.componentwise_isPoincareStandard_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum ``Submission.DifferentialGeometry.Topology.componentwise_isPoincareStandard_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum

theorem componentwiseConnectedSumStandardFactor_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum
    (D : ClosedOrientedManifold.{u} 3)
    (h : D.componentwiseStandardFactorOrProjectiveThreeSpaceSum) :
    D.componentwiseConnectedSumStandardFactor := by
  intro C
  rcases h C with h | h
  · exact ⟨[D.component C], by simpa using h, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩
  · obtain ⟨ρ⟩ := h
    refine ⟨[projectiveThreeSpaceLift.{u}, projectiveThreeSpaceLift.{u}], ?_, ?_⟩
    · intro F hF
      rw [List.mem_cons, List.mem_cons, List.mem_nil_iff] at hF
      rcases hF with rfl | rfl | hF
      · exact isStandardFactor_projectiveThreeSpaceLift
      · exact isStandardFactor_projectiveThreeSpaceLift
      · exact absurd hF (by simp)
    · exact ⟨ρ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.componentwiseConnectedSumStandardFactor_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.componentwiseConnectedSumStandardFactor_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.componentwiseConnectedSumStandardFactor_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum ``Submission.DifferentialGeometry.Topology.componentwiseConnectedSumStandardFactor_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3}

theorem poincareControlled_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum
    (E : SphericalCutCapTransition M Q)
    (h : E.discarded.componentwiseStandardFactorOrProjectiveThreeSpaceSum) :
    E.poincareControlled :=
  E.poincareControlled_of_componentwiseConnectedSumStandardFactor
    (componentwiseConnectedSumStandardFactor_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum
      E.discarded h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphericalCutCapTransition.poincareControlled_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphericalCutCapTransition.poincareControlled_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphericalCutCapTransition.poincareControlled_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum ``Submission.DifferentialGeometry.Topology.SphericalCutCapTransition.poincareControlled_of_componentwiseStandardFactorOrProjectiveThreeSpaceSum

end SphericalCutCapTransition

end DifferentialGeometry.Topology
