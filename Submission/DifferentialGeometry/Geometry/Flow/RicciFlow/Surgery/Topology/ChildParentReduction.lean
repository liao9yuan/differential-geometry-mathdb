import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCarrierCollaredStarCover
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildParent
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StandardNeckCutCapInstance
import Mathlib.Topology.Homotopy.Equiv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem simplyConnectedSpace_componentCarrier_of_connected {X : Type u} [TopologicalSpace X]
    [ConnectedSpace X] [SimplyConnectedSpace X] (c : ConnectedComponents X) :
    SimplyConnectedSpace (ComponentCarrier c) := by
  have hmk : ∀ x : X, ConnectedComponents.mk x = c := by
    intro x
    obtain ⟨y, hy⟩ := ConnectedComponents.surjective_coe c
    rw [← hy]
    exact ConnectedComponents.coe_eq_coe'.mpr (by
      rw [PreconnectedSpace.connectedComponent_eq_univ]
      exact Set.mem_univ x)
  let e : ComponentCarrier c ≃ₜ X :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, hmk x⟩
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun x => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk fun x => hmk x }
  exact e.toHomotopyEquiv.simplyConnectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.simplyConnectedSpace_componentCarrier_of_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.simplyConnectedSpace_componentCarrier_of_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.simplyConnectedSpace_componentCarrier_of_connected ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.simplyConnectedSpace_componentCarrier_of_connected

theorem sphereThreeStage_componentCarrier_simplyConnected
    (c : ConnectedComponents sphereThreeStage.Carrier) :
    SimplyConnectedSpace (sphereThreeStage.component c).Carrier := by
  have hconn : ConnectedSpace (Sphere 3) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := EuclideanSpace ℝ (Fin 4))
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num))
  exact @simplyConnectedSpace_componentCarrier_of_connected sphereThreeStage.Carrier _
    hconn (inferInstance : SimplyConnectedSpace
      DifferentialGeometry.Topology.SphereThree) c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeStage_componentCarrier_simplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeStage_componentCarrier_simplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeStage_componentCarrier_simplyConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeStage_componentCarrier_simplyConnected

theorem not_simplyConnectedSpace_childCarrier_of_capRange_eq_univ
    {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)
    (c : ConnectedComponents Q.Carrier) {b₁ b₂ : E.ChildCapBoundary c} (hne : b₁ ≠ b₂)
    (huniv : (⋃ b : E.ChildCapBoundary c, Set.range (E.childCap c b)) = Set.univ) :
    ¬ SimplyConnectedSpace (E.ChildCarrier c) := by
  intro hsc
  have hiff : SimplyConnectedSpace ↥(_root_.Set.univ : Set (E.ChildCarrier c)) ↔
      SimplyConnectedSpace (E.ChildCarrier c) :=
    (Homeomorph.Set.univ (E.ChildCarrier c)).toHomotopyEquiv.simplyConnectedSpace_iff
  exact E.not_simplyConnectedSpace_of_capRange_subset_of_two_caps c hne
    (W := Set.univ) (_root_.Set.subset_univ _) (_root_.Set.subset_univ _) (by rw [huniv])
    (hiff.mpr hsc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_simplyConnectedSpace_childCarrier_of_capRange_eq_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_simplyConnectedSpace_childCarrier_of_capRange_eq_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_simplyConnectedSpace_childCarrier_of_capRange_eq_univ ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_simplyConnectedSpace_childCarrier_of_capRange_eq_univ

theorem exists_child_simplyConnected_witness (h : StandardNeckCutCapInputs) :
    ∃ E : SmoothCutCapTransition sphereThreeStage sphereThreeStage sphereThreeStage
        (sphereThreeStage.sum sphereThreeStage),
      (∀ c : ConnectedComponents sphereThreeStage.Carrier,
        SimplyConnectedSpace (sphereThreeStage.component (E.childParent c)).Carrier) ∧
      (∀ c : ConnectedComponents sphereThreeStage.Carrier,
        SimplyConnectedSpace (sphereThreeStage.component c).Carrier) := by
  obtain ⟨E⟩ := nonempty_smoothCutCapTransition_of_standardNeckInputs h
  exact ⟨E, fun c => sphereThreeStage_componentCarrier_simplyConnected _,
    fun c => sphereThreeStage_componentCarrier_simplyConnected _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_child_simplyConnected_witness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_child_simplyConnected_witness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_child_simplyConnected_witness ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_child_simplyConnected_witness

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
