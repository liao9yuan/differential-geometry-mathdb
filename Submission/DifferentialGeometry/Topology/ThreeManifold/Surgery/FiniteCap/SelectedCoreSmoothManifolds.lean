import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingRestriction
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreSmoothEmbedding
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSelectedManifolds

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
private abbrev SelectedCoreE2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.SelectedCoreE2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.SelectedCoreE2 target :: scope.openDecls } }
private abbrev SelectedCoreIR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.SelectedCoreIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.SelectedCoreIR target :: scope.openDecls } }
private abbrev SelectedCoreIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.SelectedCoreIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.SelectedCoreIC target :: scope.openDecls } }
private abbrev SelectedCoreIH := ModelProd SelectedCoreE2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.SelectedCoreIH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.SelectedCoreIH target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (R : Set (ConnectedComponents (cutCore f)))

def retainedCoreOpen : _root_.TopologicalSpace.Opens (cutCore f) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  exact ⟨retainedCore f R, (isClopen_retained_discardedCore hδ f hf hdisj R).1.isOpen⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreOpen ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreOpen

@[instance_reducible] def retainedCoreChartedSpace : ChartedSpace SelectedCoreIH (retainedCore f R) := by
  let : ChartedSpace SelectedCoreIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  exact inferInstanceAs (ChartedSpace SelectedCoreIH (retainedCoreOpen I hdim hδ f hf hdisj R))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreChartedSpace ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreChartedSpace

variable (hs : ∀ i, IsLocalDiffeomorph SelectedCoreIC I ∞ (f i))

include hs in
theorem retainedCore_isManifold :
    let : ChartedSpace SelectedCoreIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    IsManifold SelectedCoreIR ∞ (retainedCore f R) := by
  let : ChartedSpace SelectedCoreIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold SelectedCoreIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact inferInstanceAs (IsManifold SelectedCoreIR ∞ (retainedCoreOpen I hdim hδ f hf hdisj R))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_isManifold ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_isManifold

include hs in
theorem retainedCore_ambientInclusion_isSmoothEmbedding :
    let : ChartedSpace SelectedCoreIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    IsSmoothEmbedding SelectedCoreIR I ∞ (fun p : retainedCore f R => p.val.val) := by
  let : ChartedSpace SelectedCoreIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : IsManifold SelectedCoreIR ∞ (cutCore f) := cutCore_isManifold I hdim hδ f hf hdisj hs
  exact isSmoothEmbedding_restrictOpen SelectedCoreIR I (Subtype.val : cutCore f → M)
    (cutCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj hs)
    (retainedCoreOpen I hdim hδ f hf hdisj R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_ambientInclusion_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_ambientInclusion_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_ambientInclusion_isSmoothEmbedding ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_ambientInclusion_isSmoothEmbedding

include hs in
theorem retainedCore_boundary_eq_cuttingSpheres :
    let : ChartedSpace SelectedCoreIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    SelectedCoreIR.boundary (retainedCore f R) = (Subtype.val : retainedCore f R → cutCore f) ⁻¹'
      range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) := by
  let : ChartedSpace SelectedCoreIH (cutCore f) := cutCoreBoundaryChartedSpace I hdim hδ f hf hdisj
  let : ChartedSpace SelectedCoreIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  have hb : SelectedCoreIR.boundary (cutCore f) =
      range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) :=
    cutCore_boundary_eq_cuttingSpheres I hdim hδ f hf hdisj hs
  have hu := SelectedCoreIR.boundary_open (u := retainedCoreOpen I hdim hδ f hf hdisj R)
  exact hu.trans (congrArg ((Subtype.val : retainedCore f R → cutCore f) ⁻¹' ·) hb)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_boundary_eq_cuttingSpheres then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_boundary_eq_cuttingSpheres"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_boundary_eq_cuttingSpheres ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_boundary_eq_cuttingSpheres

include hs in
theorem retained_discardedCore_smooth_embeddings :
    let : ChartedSpace SelectedCoreIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    let : ChartedSpace SelectedCoreIH (discardedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj Rᶜ
    IsManifold SelectedCoreIR ∞ (retainedCore f R) ∧
    IsManifold SelectedCoreIR ∞ (discardedCore f R) ∧
    _root_.Manifold.IsSmoothEmbedding SelectedCoreIR I ∞ (fun p : retainedCore f R => p.val.val) ∧
    IsSmoothEmbedding SelectedCoreIR I ∞ (fun p : discardedCore f R => p.val.val) := by
  exact ⟨retainedCore_isManifold I hdim hδ f hf hdisj R hs,
    retainedCore_isManifold I hdim hδ f hf hdisj Rᶜ hs,
    retainedCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj R hs,
    retainedCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj Rᶜ hs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.retained_discardedCore_smooth_embeddings then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.retained_discardedCore_smooth_embeddings"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.retained_discardedCore_smooth_embeddings ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.retained_discardedCore_smooth_embeddings
end DifferentialGeometry.Topology.ThreeManifold.Surgery
