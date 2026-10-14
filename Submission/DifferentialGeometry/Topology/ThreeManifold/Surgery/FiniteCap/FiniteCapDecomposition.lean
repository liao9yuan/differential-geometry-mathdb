import Submission.DifferentialGeometry.Topology.Manifold.ClopenDecomposition
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSelectedManifolds

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
private abbrev DecompositionE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.DecompositionE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.DecompositionE3 target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
local notation "DecompQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteCapSelectedDiffeomorph (R : Set (ConnectedComponents (cutCore f))) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace DecompositionE3 DecompQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Diffeomorph (𝓡 3) (𝓡 3)
      (finiteCapRetained hL hδ f hf hdisj R ⊕ finiteCapDiscarded hL hδ f hf hdisj R) DecompQ ∞ := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace DecompositionE3 DecompQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact DifferentialGeometry.Topology.Manifold.clopenSumDiffeomorph (𝓡 3)
    (finiteCapRetained hL hδ f hf hdisj R)
    (isClopen_finiteCapRetained_discarded hL hδ f hf hdisj R).1.isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph

theorem finiteCapSelectedDiffeomorph_inl (R : Set (ConnectedComponents (cutCore f))) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    ∀ p : finiteCapRetained hL hδ f hf hdisj R,
      finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R (Sum.inl p) = p.val := by
  dsimp only
  intro p
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph_inl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph_inl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph_inl ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph_inl

theorem finiteCapSelectedDiffeomorph_inr (R : Set (ConnectedComponents (cutCore f))) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    ∀ p : finiteCapDiscarded hL hδ f hf hdisj R,
      finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R (Sum.inr p) = p.val := by
  dsimp only
  intro p
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph_inr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph_inr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph_inr ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph_inr

theorem finiteCapSelectedDiffeomorph_symm_retained (R : Set (ConnectedComponents (cutCore f)))
    : let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
      let : ChartedSpace DecompositionE3 DecompQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
      ∀ (q : DecompQ) (hq : finiteCapComponentLabel hL hδ f hf hdisj q ∈ R),
    (finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R).symm q = Sum.inl ⟨q, hq⟩ := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace DecompositionE3 DecompQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  dsimp only
  intro q hq
  apply (finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R).injective
  exact (finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R).apply_symm_apply q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph_symm_retained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph_symm_retained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph_symm_retained ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph_symm_retained

theorem finiteCapSelectedDiffeomorph_symm_discarded (R : Set (ConnectedComponents (cutCore f)))
    : let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
      let : ChartedSpace DecompositionE3 DecompQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
      ∀ (q : DecompQ) (hq : finiteCapComponentLabel hL hδ f hf hdisj q ∉ R),
    (finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R).symm q = Sum.inr ⟨q, hq⟩ := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace DecompositionE3 DecompQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  dsimp only
  intro q hq
  apply (finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R).injective
  exact (finiteCapSelectedDiffeomorph I hdim hL hδ f hf hdisj R).apply_symm_apply q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph_symm_discarded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph_symm_discarded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph_symm_discarded ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapSelectedDiffeomorph_symm_discarded
end DifferentialGeometry.Topology.ThreeManifold.Surgery
