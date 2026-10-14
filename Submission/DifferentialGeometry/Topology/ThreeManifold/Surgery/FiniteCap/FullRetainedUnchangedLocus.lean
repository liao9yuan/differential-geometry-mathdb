import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCutCapGeometry
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RetainedCoreDomainSmooth

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.E3 target :: scope.openDecls } }
private abbrev E2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.E2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.E2 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.S2 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IC target :: scope.openDecls } }
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IR target :: scope.openDecls } }
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IH target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
  (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
  (f : ∀ i : ι, bufferedCylinder (precision i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
  (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))
  (hδ1 : ∀ i, precision i < 1) (R : Set (ConnectedComponents (cutCore f))) (U : Opens M)
  (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def FullRetainedUnchangedLocusGeometry : Prop :=
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  let : IsManifold IR ∞ (retainedCore f R) := retainedCore_isManifold I hdim hδ f hf hdisj R hs
  let : ChartedSpace E3 Q := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let Φ := finiteRetainedCoreInclusion hL hδ f hf hdisj R
  let Ψ := retainedCoreDomainMap f R U hRet
  let ν := fun i => originalTubularMap (hδ i) (hδ1 i) (f i)
  ∃ K : Set (retainedCore f R), K = _root_.Set.univ ∧ IsCompact K ∧
    _root_.Manifold.IsSmoothEmbedding IR IR ∞ (id : retainedCore f R → retainedCore f R) ∧
    _root_.Manifold.IsSmoothEmbedding IR I ∞ Ψ ∧ _root_.Manifold.IsSmoothEmbedding IR (𝓡 3) ∞ Φ ∧
    _root_.Set.MapsTo (fun p : retainedCore f R => p.val.val) K U ∧
    ((_root_.Set.univ : Set (retainedCore f R)) \ (fun p => p.val.val) ⁻¹'
      (⋃ i, ν i '' {q : S2 × _root_.Set.Icc (-2 : ℝ) 2 | q.2.val ∈ _root_.Set.Ioo (-2 : ℝ) 2})) ⊆ K ∧
    (∀ q : finiteCapRetained hL hδ f hf hdisj R,
      ∃ p : retainedCore f R, p ∈ K ∧ Φ p ∈ connectedComponent q) ∧
    (IsEmpty (finiteCapRetained hL hδ f hf hdisj R) → K = ∅)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.FullRetainedUnchangedLocusGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.FullRetainedUnchangedLocusGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.FullRetainedUnchangedLocusGeometry ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FullRetainedUnchangedLocusGeometry

theorem fullRetainedUnchangedLocusGeometry [CompactSpace M] :
    FullRetainedUnchangedLocusGeometry I hdim hL hδ f hf hdisj hs hδ1 R U hRet := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace IH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  let : IsManifold IR ∞ (retainedCore f R) := retainedCore_isManifold I hdim hδ f hf hdisj R hs
  let : ChartedSpace E3 Q := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let : CompactSpace (retainedCore f R) := isCompact_iff_compactSpace.mp
    (isCompact_retained_discardedCore hδ f hf hdisj R).1
  refine ⟨univ, rfl, isCompact_univ, IsSmoothEmbedding.id, ?_, ?_, ?_, _root_.Set.subset_univ _, ?_, ?_⟩
  · exact retainedCoreDomainMap_isSmoothEmbedding I hdim hδ f hf hdisj hs R U hRet
  · exact finiteRetainedCoreInclusion_isSmoothEmbedding I hdim hL hδ f hf hdisj hs R
  · intro p _
    exact hRet p.property
  · intro q
    obtain ⟨p, hp⟩ := finiteCapRetained_component_meets_original_core hL hδ f hf hdisj R q
    exact ⟨p, _root_.Set.mem_univ _, hp⟩
  · intro hEmpty
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p _
    exact hEmpty.false (finiteRetainedCoreInclusion hL hδ f hf hdisj R p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.fullRetainedUnchangedLocusGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.fullRetainedUnchangedLocusGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.fullRetainedUnchangedLocusGeometry ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.fullRetainedUnchangedLocusGeometry
end DifferentialGeometry.Topology.ThreeManifold.Surgery
