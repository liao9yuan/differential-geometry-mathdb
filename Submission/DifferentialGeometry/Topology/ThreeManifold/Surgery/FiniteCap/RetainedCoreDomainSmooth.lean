import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.SelectedCoreSmoothManifolds
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RetainedCoreMaps

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
private abbrev DomainCoreE2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.DomainCoreE2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.DomainCoreE2 target :: scope.openDecls } }
private abbrev DomainCoreIR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.DomainCoreIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.DomainCoreIR target :: scope.openDecls } }
private abbrev DomainCoreIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.DomainCoreIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.DomainCoreIC target :: scope.openDecls } }
private abbrev DomainCoreIH := ModelProd DomainCoreE2 (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.DomainCoreIH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.DomainCoreIH target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph DomainCoreIC I ∞ (f i))
variable (R : Set (ConnectedComponents (cutCore f))) (U : Opens M)
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)

include hs in
theorem retainedCoreDomainMap_isSmoothEmbedding :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace DomainCoreIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    IsSmoothEmbedding DomainCoreIR I ∞ (retainedCoreDomainMap f R U hRet) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace DomainCoreIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  exact isSmoothEmbedding_intoOpen DomainCoreIR I U (retainedCoreDomainMap f R U hRet)
    (retainedCore_ambientInclusion_isSmoothEmbedding I hdim hδ f hf hdisj R hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreDomainMap_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreDomainMap_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreDomainMap_isSmoothEmbedding ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreDomainMap_isSmoothEmbedding

include hs in
theorem retainedCoreDomainMap_mfderiv (p : retainedCore f R) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace DomainCoreIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
    mfderiv DomainCoreIR I (retainedCoreDomainMap f R U hRet) p =
      mfderiv DomainCoreIR I (fun q : retainedCore f R => q.val.val) p := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace DomainCoreIH (retainedCore f R) := retainedCoreChartedSpace I hdim hδ f hf hdisj R
  have hF : ContMDiff DomainCoreIR I ∞ (retainedCoreDomainMap f R U hRet) :=
    (retainedCoreDomainMap_isSmoothEmbedding I hdim hδ f hf hdisj hs R U hRet).contMDiff
  have hd := mfderiv_comp p
    ((contMDiff_subtype_val (I := I) (U := U) (n := ∞)).mdifferentiableAt (by simp))
    (hF.mdifferentiableAt (by simp))
  rw [DifferentialGeometry.mfderiv_subtype_val] at hd
  dsimp only [TangentSpace] at hd ⊢
  apply ContinuousLinearMap.ext
  intro v
  exact (congrArg (fun A : (DomainCoreE2 × EuclideanSpace ℝ (Fin 1)) →L[ℝ] E => A v) hd).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreDomainMap_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreDomainMap_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreDomainMap_mfderiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCoreDomainMap_mfderiv
end DifferentialGeometry.Topology.ThreeManifold.Surgery
