import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapComponentSelection
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapNeckManifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev SelectedE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.SelectedE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.SelectedE3 target :: scope.openDecls } }
private abbrev SelectedIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.SelectedIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.SelectedIC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealSelectedE3HAddOfNat : Fact (Module.finrank ℝ SelectedE3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealSelectedE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealSelectedE3HAddOfNat target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M]

include I in
theorem originalModel_locallyPathConnected (hdim : Module.finrank ℝ E = 3) : LocallyPathConnectedSpace M := by
  let : LocallyPathConnectedSpace H := (modelThreeHomeomorph I hdim).isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.originalModel_locallyPathConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.originalModel_locallyPathConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.originalModel_locallyPathConnected ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.originalModel_locallyPathConnected

variable {ι : Type*} [Finite ι] [T2Space M] [IsManifold I ∞ M]
variable {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
local notation "CappedQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

theorem finiteCapSelected_isManifold
    (hs : ∀ i, IsLocalDiffeomorph SelectedIC I ∞ (f i)) (R : Set (ConnectedComponents (cutCore f))) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace SelectedE3 CappedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsManifold (𝓡 3) ∞ (finiteCapRetained hL hδ f hf hdisj R) ∧
      IsManifold (𝓡 3) ∞ (finiteCapDiscarded hL hδ f hf hdisj R) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace SelectedE3 CappedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ CappedQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  exact ⟨inferInstance, inferInstance⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelected_isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelected_isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelected_isManifold ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelected_isManifold

theorem finiteCapSelected_closedManifold_properties [CompactSpace M]
    (hs : ∀ i, IsLocalDiffeomorph SelectedIC I ∞ (f i)) (R : Set (ConnectedComponents (cutCore f))) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace SelectedE3 CappedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsManifold (𝓡 3) ∞ (finiteCapRetained hL hδ f hf hdisj R) ∧
      IsManifold (𝓡 3) ∞ (finiteCapDiscarded hL hδ f hf hdisj R) ∧
      CompactSpace (finiteCapRetained hL hδ f hf hdisj R) ∧
      CompactSpace (finiteCapDiscarded hL hδ f hf hdisj R) ∧
      T2Space (finiteCapRetained hL hδ f hf hdisj R) ∧
      T2Space (finiteCapDiscarded hL hδ f hf hdisj R) ∧
      SecondCountableTopology (finiteCapRetained hL hδ f hf hdisj R) ∧
      SecondCountableTopology (finiteCapDiscarded hL hδ f hf hdisj R) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace SelectedE3 CappedQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  have htop := finiteCapQuotient_topological_properties I hdim hL hδ f hf hdisj
  let : T2Space CappedQ := htop.2.1
  let : SecondCountableTopology CappedQ := htop.2.2.1
  have hc := finiteCapRetained_discarded_compactSpace hL hδ f hf hdisj R
  have hs' := finiteCapSelected_isManifold I hdim hL hδ f hf hdisj hs R
  exact ⟨hs'.1, hs'.2, hc.1, hc.2, inferInstance, inferInstance, inferInstance, inferInstance⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelected_closedManifold_properties then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelected_closedManifold_properties"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelected_closedManifold_properties ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelected_closedManifold_properties
end DifferentialGeometry.Topology.ThreeManifold.Surgery
