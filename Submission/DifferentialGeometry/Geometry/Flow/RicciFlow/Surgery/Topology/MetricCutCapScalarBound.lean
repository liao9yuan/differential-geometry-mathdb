import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricScalarBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.WorldBridges

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Metric
  DifferentialGeometry.Topology.ThreeManifold.Surgery
  DifferentialGeometry.Topology.Manifold.Attachment
open _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.E3 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceE3InsertionQuotient {B : ℝ} {hB : 0 < B} : ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceE3InsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instChartedSpaceE3InsertionQuotient target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instT2SpaceInsertionQuotient {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instT2SpaceInsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instT2SpaceInsertionQuotient target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))
local notation "Q" => FiniteCapQuotient transitionEnd_pos hδ f (fun i =>
  _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i)))
  hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (R : Set (ConnectedComponents (cutCore f)))
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
variable (c : ℝ) (hc : 4 ≤ c)
local notation "Ret" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "Boundary" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
variable (x₀ : ι → U) (order : ι → ℕ)
variable (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
variable (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i))
variable {k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ}
variable (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (c * precision
  b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
variable (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
  ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
variable (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map =
  (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
variable (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d
  b).retainedSide = true)
variable {A D ε : ℝ} {hA : 0 < A} {m : ℕ}
variable (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
  CanonicalStaticInsertionWitness (d b) A hA D m ε)

theorem MetricCutCapEvent.scalar_le_of_finiteFullPreparedMetric
    {C : ℕ → ℝ} (hw : ∀ b : Boundary, StaticInsertionAdditionalProperties C (w b))
    (hC : 0 ≤ C 0)
    (hratio : ∀ b : Boundary,
      |metricScalarAt g ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) /
        metricScalarAt g (x₀ b.val.1) - 1| ≤ c * precision b.val.1)
    (K Qmax : ℝ) (hQmax : 0 ≤ Qmax)
    (hin : ∀ p : retainedCore f R,
      metricScalarAt g (retainedCoreDomainMap f R U hRet p) ≤ K)
    (hscale : ∀ b : Boundary, metricScalarAt g (x₀ b.val.1) ≤ Qmax) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace E3 Q :=
      finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ Q :=
      finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    ∀ [CompactSpace Ret] (oRet : SmoothOrientation (𝓡 3) Ret)
      {P : OrientedThreeStage} {a s : ℝ}
      (event : MetricCutCapEvent P
        (OrientedThreeStage.ofSmoothOrientation Ret oRet) a s),
      event.outputMetric = finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc
        x₀ order d₀ hOriginal hrec d hmap hside w →
      ∀ q : Ret, metricScalarAt event.outputMetric q ≤ _root_.Max.max K (2 * C 0 * Qmax) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace E3 Q :=
    finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ Q :=
    finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space Q := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro hcompact oRet P a s event hout q
  rw [hout]
  exact finiteFullPreparedMetric_scalar_le_of_neck_scale_bound I hδ f hf hdisj hs U g R hRet
    c hc x₀ order d₀ hOriginal hrec d hmap hside w hw hC hratio K Qmax hQmax hin hscale q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.scalar_le_of_finiteFullPreparedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.scalar_le_of_finiteFullPreparedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.scalar_le_of_finiteFullPreparedMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.scalar_le_of_finiteFullPreparedMetric

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
