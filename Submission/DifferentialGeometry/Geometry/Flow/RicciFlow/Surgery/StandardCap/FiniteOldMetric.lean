import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteRetainedInterior
import Submission.DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev OldE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.OldE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.OldE3 target :: scope.openDecls } }
private abbrev OldIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.OldIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.OldIC target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph OldIC I ∞ (f i))
local notation "OldQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteOldMetric (U : _root_.TopologicalSpace.Opens M) (g : SmoothRiemannianMetric I U)
    (R : Set (ConnectedComponents (cutCore f)))
    (hRet : _root_.Set.MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace OldE3 OldQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ OldQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    SmoothRiemannianMetric (𝓡 3) (finiteRetainedInteriorOpens hL hδ f hf hdisj R) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace OldE3 OldQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ OldQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let : T2Space OldQ := finiteCapQuotient_t2Space hL hδ f hf hdisj
  exact pullbackMetricOfInjectiveLocalDiffeomorph g
    (finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet)
    (isLocalDiffeomorph_finiteRetainedInteriorOriginalMap hL hδ f hf hdisj I hdim hs U R hRet)
    (injective_finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteOldMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteOldMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteOldMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteOldMetric

theorem finiteOldMetric_inner (U : _root_.TopologicalSpace.Opens M) (g : SmoothRiemannianMetric I U)
    (R : Set (ConnectedComponents (cutCore f)))
    (hRet : _root_.Set.MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace OldE3 OldQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ OldQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    ∀ (q : finiteRetainedInteriorOpens hL hδ f hf hdisj R) (v w : TangentSpace (𝓡 3) q),
      (finiteOldMetric I hdim hL hδ f hf hdisj hs U g R hRet).inner q v w =
        g.inner (finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet q)
          (mfderiv (𝓡 3) I (finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet) q v)
          (mfderiv (𝓡 3) I (finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet) q w) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace OldE3 OldQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ OldQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let : T2Space OldQ := finiteCapQuotient_t2Space hL hδ f hf hdisj
  dsimp only
  intro q v w
  exact pullbackMetricOfInjectiveLocalDiffeomorph_inner g
    (finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet)
    (isLocalDiffeomorph_finiteRetainedInteriorOriginalMap hL hδ f hf hdisj I hdim hs U R hRet)
    (injective_finiteRetainedInteriorOriginalMap hL hδ f hf hdisj U R hRet) q v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteOldMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteOldMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteOldMetric_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteOldMetric_inner

theorem finiteOldMetric_original_inner (U : _root_.TopologicalSpace.Opens M) (g : SmoothRiemannianMetric I U)
    (R : Set (ConnectedComponents (cutCore f)))
    (hRet : _root_.Set.MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
    (p : coreInteriorDomain f)
    (hp : (⟨p.val, interior_subset p.property⟩ : cutCore f) ∈ retainedCore f R)
    (v w : TangentSpace I p) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
    let : ChartedSpace OldE3 OldQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ OldQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    (finiteOldMetric I hdim hL hδ f hf hdisj hs U g R hRet).inner
      (finiteRetainedInteriorImage hL hδ f hf hdisj R p hp)
      (mfderiv I (𝓡 3) (finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj) p v)
      (mfderiv I (𝓡 3) (finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj) p w) =
        g.inner ⟨p.val, hRet hp⟩ v w := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I hdim
  let : ChartedSpace OldE3 OldQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ OldQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  have hd := finiteRetainedInteriorOriginalMap_mfderiv_image_comp hL hδ f hf hdisj I hdim hs U R hRet p hp
  have hv := congrArg (fun A : TangentSpace I p →L[ℝ] TangentSpace I p => A v) hd
  have hw := congrArg (fun A : TangentSpace I p →L[ℝ] TangentSpace I p => A w) hd
  dsimp only
  have ht := finiteOldMetric_inner I hdim hL hδ f hf hdisj hs U g R hRet
    (finiteRetainedInteriorImage hL hδ f hf hdisj R p hp)
    (mfderiv I (𝓡 3) (finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj) p v)
    (mfderiv I (𝓡 3) (finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj) p w)
  refine ht.trans ?_
  dsimp only [TangentSpace] at hv hw ⊢
  rw [finiteRetainedInteriorOriginalMap_image]
  erw [hv, hw]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteOldMetric_original_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteOldMetric_original_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteOldMetric_original_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteOldMetric_original_inner
end DifferentialGeometry.PDE.RicciFlow.StandardCap
