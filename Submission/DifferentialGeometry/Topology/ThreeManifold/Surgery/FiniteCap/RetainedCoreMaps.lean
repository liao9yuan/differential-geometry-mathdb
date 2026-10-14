import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapPatchSelection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace
open _root_.Submission.DifferentialGeometry.Geometry.Neck
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev CoreMapE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreMapE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreMapE3 target :: scope.openDecls } }
private abbrev CoreMapS2 := Metric.sphere (0 : CoreMapE3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreMapS2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.CoreMapS2 target :: scope.openDecls } }
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M] [LocallyPathConnectedSpace M]
variable {precision : ι → ℝ} {L B : ℝ}
variable (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (R : Set (ConnectedComponents (cutCore f)))

def finiteRetainedCoreInclusion : retainedCore f R → finiteCapRetained hL hδ f hf hdisj R :=
  fun p => ⟨finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj p.val, p.property⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCoreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCoreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCoreInclusion ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCoreInclusion

def retainedCoreDomainMap (U : _root_.TopologicalSpace.Opens M)
    (hRet : _root_.Set.MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U) : retainedCore f R → U :=
  fun p => ⟨p.val.val, hRet p.property⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreDomainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreDomainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreDomainMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreDomainMap

def finiteRetainedCollarCoreMap (b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R})
    (hfit : B ≤ cuttingCollarWidth (precision b.val.1)) :
    CoreMapS2 × _root_.Set.Ico (0 : ℝ) B → retainedCore f R := fun q =>
  ⟨cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b.val
    (q.1, ⟨q.2.val, q.2.property.1, q.2.property.2.trans_le hfit⟩),
    (finiteCapRestrictedNeighborhood_subset_retained hL hδ f hf hdisj R b.val b.property B)
      ((finiteCapRestrictedNeighborhood_collar_iff hL hδ f hf hdisj b.val B _).mpr q.2.property.2)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCollarCoreMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCollarCoreMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCollarCoreMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCollarCoreMap

theorem finiteRetainedCollarCoreMap_zero
    (b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R})
    (hfit : B ≤ cuttingCollarWidth (precision b.val.1)) (hB : 0 < B) (y : CoreMapS2) :
    (finiteRetainedCollarCoreMap hL hδ f hf hdisj R b hfit (y, ⟨0, le_rfl, hB⟩)).val =
      cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b.val, y⟩ :=
  cuttingCollarMap_zero hδ f (fun i => (hf i).injective) hdisj b.val y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCollarCoreMap_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCollarCoreMap_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCollarCoreMap_zero ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteRetainedCollarCoreMap_zero
end DifferentialGeometry.Topology.ThreeManifold.Surgery
