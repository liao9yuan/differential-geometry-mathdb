import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreSelection
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapQuotient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Geometry.Neck
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M] [LocallyPathConnectedSpace M]
variable {precision : ι → ℝ} {L : ℝ}
variable (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
local notation "LabelQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

private def componentOnSum : IndexedCaps ι L ⊕ cutCore f → ConnectedComponents (cutCore f) :=
  Sum.elim (fun p => cuttingSphereComponent hδ f hf hdisj p.1) ConnectedComponents.mk

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.componentOnSum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.componentOnSum target :: scope.openDecls } }

private theorem componentOnSum_rel (a b : IndexedCaps ι L ⊕ cutCore f)
    (h : adjunctionRel (indexedCapBoundary (ι := ι) hL)
      (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) a b) :
    componentOnSum hδ f hf hdisj a = componentOnSum hδ f hf hdisj b := by
  rcases h with ⟨s, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
  · exact (cuttingSphere_component_eq hδ f hf hdisj s.1 s.2).symm
  · exact cuttingSphere_component_eq hδ f hf hdisj s.1 s.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.componentOnSum_rel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.componentOnSum_rel target :: scope.openDecls } }

def finiteCapComponentLabel : LabelQ → ConnectedComponents (cutCore f) :=
  Quot.lift (componentOnSum hδ f hf hdisj) (componentOnSum_rel hL hδ f hf hdisj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapComponentLabel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapComponentLabel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapComponentLabel ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapComponentLabel

theorem finiteCapComponentLabel_core (x : cutCore f) :
    finiteCapComponentLabel hL hδ f hf hdisj
      (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj x) = ConnectedComponents.mk x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapComponentLabel_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapComponentLabel_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapComponentLabel_core ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapComponentLabel_core

theorem finiteCapComponentLabel_cap (p : IndexedCaps ι L) :
    finiteCapComponentLabel hL hδ f hf hdisj
      (finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj p) =
        cuttingSphereComponent hδ f hf hdisj p.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapComponentLabel_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapComponentLabel_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapComponentLabel_cap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapComponentLabel_cap

theorem continuous_finiteCapComponentLabel : Continuous (finiteCapComponentLabel hL hδ f hf hdisj) := by
  apply continuous_quot_lift
  apply continuous_sumElim.mpr
  refine ⟨continuous_sigma (fun b => ?_), ConnectedComponents.continuous_coe⟩
  change Continuous (fun _ : {x : EuclideanSpace ℝ (Fin 3) // ‖x‖ ≤ L} => cuttingSphereComponent hδ f hf hdisj b)
  exact continuous_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.continuous_finiteCapComponentLabel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.continuous_finiteCapComponentLabel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.continuous_finiteCapComponentLabel ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.continuous_finiteCapComponentLabel

theorem finiteCapComponentLabel_surjective : _root_.Function.Surjective (finiteCapComponentLabel hL hδ f hf hdisj) := by
  intro c
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  exact ⟨finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj p, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapComponentLabel_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapComponentLabel_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapComponentLabel_surjective ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapComponentLabel_surjective
end DifferentialGeometry.Topology.ThreeManifold.Surgery
