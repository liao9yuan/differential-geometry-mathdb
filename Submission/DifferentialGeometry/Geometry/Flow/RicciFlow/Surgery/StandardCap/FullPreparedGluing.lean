import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteFullWitnessMap
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FiniteCapFullMetric
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FiniteGluedMetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev FullGE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.FullGE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.FullGE3 target :: scope.openDecls } }
private abbrev FullGIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.FullGIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.FullGIC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceFullGE3InsertionQuotient {B : ℝ} {hB : 0 < B} : ChartedSpace FullGE3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceFullGE3InsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceFullGE3InsertionQuotient target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph FullGIC I ∞ (f i))
local notation "FullGQ" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (R : Set (ConnectedComponents (cutCore f)))
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
variable (c : ℝ) (hc : 4 ≤ c)
local notation "FullGRet" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "FullGOld" => finiteRetainedInteriorOpens transitionEnd_pos hδ f hf hdisj R
local notation "FullGB" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
variable (x₀ : ι → U) (order : ι → ℕ)
variable (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
variable (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i))
variable {k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ}
variable (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
variable (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
  ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
variable (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
variable (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).retainedSide = true)
variable {A D ε : ℝ} {hA : 0 < A} {m : ℕ}
variable (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, CanonicalStaticInsertionWitness (d b) A hA D m ε)

def finiteFullPreparedMetric :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace FullGE3 FullGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ FullGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    SmoothRiemannianMetric (𝓡 3) FullGRet := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace FullGE3 FullGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ FullGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  exact finiteGluedMetric I hδ f hf hdisj hs U g R hRet
    (fun b => (c * precision b.1)⁻¹) (fun b => (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).1)
    x₀ order d₀ hOriginal hrec d hmap hside w
    (fun b => (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le) (fun _ => le_rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric

theorem finiteFullPreparedMetric_witness_inner (b : FullGB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace FullGE3 FullGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ FullGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    ∀ (q : InsertionQuotient (inv_pos.mpr (d b).precision_pos)) (v z : TangentSpace (𝓡 3) q),
      (finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w).inner
        (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b q)
        (mfderiv (𝓡 3) (𝓡 3) (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b) q v)
        (mfderiv (𝓡 3) (𝓡 3) (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b) q z) =
          (w b).data.outMetric.inner q v z := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace FullGE3 FullGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ FullGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space FullGQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro q v z
  rw [finiteFullWitnessMap_mfderiv]
  let F := finiteCapFullInsertionDiffeomorph I Fact.out transitionEnd_pos hδ f hf hdisj hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le (inv_pos.mpr (d b).precision_pos)
  exact (finiteGluedMetric_inner_cap I hδ f hf hdisj hs U g R hRet
    (fun b => (c * precision b.1)⁻¹) (fun b => (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).1)
    x₀ order d₀ hOriginal hrec d hmap hside w
    (fun b => (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le) (fun _ => le_rfl) b (F.symm q)
    (mfderiv (𝓡 3) (𝓡 3) F.symm q v) (mfderiv (𝓡 3) (𝓡 3) F.symm q z)).trans
      (finiteCapFullWitnessMetric_inverse_inner I Fact.out hδ f hf hdisj hs (d b) (w b) b.val
        (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le q v z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_witness_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_witness_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_witness_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_witness_inner

theorem finiteFullPreparedMetric_original_inner (p : coreInteriorDomain f)
    (hp : (⟨p.val, interior_subset p.property⟩ : cutCore f) ∈ retainedCore f R)
    (v z : TangentSpace I p) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace FullGE3 FullGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ FullGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    (finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w).inner
      (Opens.inclusion inf_le_left (finiteRetainedInteriorImage transitionEnd_pos hδ f hf hdisj R p hp))
      (mfderiv I (𝓡 3) (finiteCoreInteriorMap transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) p v)
      (mfderiv I (𝓡 3) (finiteCoreInteriorMap transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) p z) =
        g.inner ⟨p.val, hRet hp⟩ v z := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace FullGE3 FullGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ FullGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  exact finiteGluedMetric_original_inner I hδ f hf hdisj hs U g R hRet
    (fun b => (c * precision b.1)⁻¹) (fun b => (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).1)
    x₀ order d₀ hOriginal hrec d hmap hside w
    (fun b => (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le) (fun _ => le_rfl) p hp v z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_original_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_original_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_original_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_original_inner
end DifferentialGeometry.PDE.RicciFlow.StandardCap
