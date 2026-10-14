import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedCutCapPresentation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticCapWitness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullPreparedGluing
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import Submission.DifferentialGeometry.Geometry.Metric.EmbeddingComposition
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricBoundaryCollar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Metric
open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery
open _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Topology
universe u
local notation "I" => ThreeModel
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
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient target :: scope.openDecls } }
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [T2Space M] [IsManifold ThreeModel ∞ M]
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealThreeSpaceOfNat : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealThreeSpaceOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealThreeSpaceOfNat target :: scope.openDecls } }
variable {ι : Type} [Finite ι] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph FullGIC I ∞ (f i))
local notation "FullGQ" => FiniteCapQuotient transitionEnd_pos hδ f
  (fun i => _root_.Topology.IsEmbedding.injective
    (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
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
variable (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
  (c * precision b.val.1)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
variable (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
  normalizedDatum g
  ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (c * precision b.val.1) (k' b))
variable (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
  (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
variable (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
  (d b).retainedSide = true)
variable {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ}
variable (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
  CanonicalStaticInsertionWitness (d b) fixed.collarLength fixed.collar_pos D m ε)


def finiteStaticCapInclusion (b : FullGB) (hD : 0 < D) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace FullGE3 FullGQ :=
      finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ FullGQ :=
      finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    C(((w b).toStaticCapWitness hD).Output, FullGRet) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace FullGE3 FullGQ :=
    finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ FullGQ :=
    finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  have hF := contMDiff_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  exact ⟨finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b ∘ ULift.down,
    hF.continuous.comp continuous_uliftDown⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion


theorem finiteStaticCapInclusion_smooth (b : FullGB) (hD : 0 < D) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace FullGE3 FullGQ :=
      finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ FullGQ :=
      finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    _root_.Manifold.IsSmoothEmbedding ThreeModel ThreeModel ∞
      (finiteStaticCapInclusion hδ f hf hdisj hs U g R c hc x₀ order d₀ d w b hD) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace FullGE3 FullGQ :=
    finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ FullGQ :=
    finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : ChartedSpace FullGE3 (ULift.{u} (InsertionQuotient (inv_pos.mpr (d b).precision_pos))) :=
    uliftChartedSpace FullGE3 _
  let : IsManifold ThreeModel ∞ (ULift.{u} (InsertionQuotient (inv_pos.mpr (d b).precision_pos))) :=
    isManifold_ulift ThreeModel _
  let e : InsertionQuotient (inv_pos.mpr (d b).precision_pos) ≃ₘ⟮ThreeModel, ThreeModel⟯
      ULift.{u} (InsertionQuotient (inv_pos.mpr (d b).precision_pos)) :=
    uliftDiffeomorph ThreeModel _
  have hF := isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
    (isLocalDiffeomorph_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
    (injective_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
  exact isSmoothEmbedding_diffeomorph_precomp _ hF e.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_smooth ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_smooth

theorem finiteFullPreparedMetric_staticCap_inclusion_inner (b : FullGB) (hD : 0 < D) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace FullGE3 FullGQ :=
      finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ FullGQ :=
      finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let S := (w b).toStaticCapWitness hD
    let F := finiteStaticCapInclusion hδ f hf hdisj hs U g R c hc x₀ order d₀ d w b hD
    ∀ (q : S.Output) (v z : TangentSpace ThreeModel q),
      S.metric.inner q v z =
        (finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc
          x₀ order d₀ hOriginal hrec d hmap hside w).inner (F q)
          (mfderiv ThreeModel ThreeModel F q v) (mfderiv ThreeModel ThreeModel F q z) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace FullGE3 FullGQ :=
    finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ FullGQ :=
    finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : ChartedSpace FullGE3 (ULift.{u} (InsertionQuotient (inv_pos.mpr (d b).precision_pos))) :=
    uliftChartedSpace FullGE3 _
  let : IsManifold ThreeModel ∞ (ULift.{u} (InsertionQuotient (inv_pos.mpr (d b).precision_pos))) :=
    isManifold_ulift ThreeModel _
  let e : InsertionQuotient (inv_pos.mpr (d b).precision_pos) ≃ₘ⟮ThreeModel, ThreeModel⟯
      ULift.{u} (InsertionQuotient (inv_pos.mpr (d b).precision_pos)) :=
    uliftDiffeomorph ThreeModel _
  let F := finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
  let gr := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc
    x₀ order d₀ hOriginal hrec d hmap hside w
  have haux (q : ULift.{u} (InsertionQuotient (inv_pos.mpr (d b).precision_pos)))
      (v z : TangentSpace ThreeModel q) :
      (Diffeomorph.pullbackMetricCross (w b).data.outMetric e.symm).inner q v z =
        gr.inner ((F ∘ e.symm) q) (mfderiv ThreeModel ThreeModel (F ∘ e.symm) q v)
          (mfderiv ThreeModel ThreeModel (F ∘ e.symm) q z) := by
    rw [Diffeomorph.pullbackMetricCross_inner]
    exact (metric_inner_comp_of_isometry (w b).data.outMetric gr F
      (contMDiff_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
      (finiteFullPreparedMetric_witness_inner I hδ f hf hdisj hs U g R hRet c hc
        x₀ order d₀ hOriginal hrec d hmap hside w b)
      e.symm e.symm.contMDiff q v z).symm
  dsimp only
  intro q v z
  exact haux q v z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_staticCap_inclusion_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_staticCap_inclusion_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_staticCap_inclusion_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_staticCap_inclusion_inner


def finiteStaticRetainedPoint (b : FullGB) :
    neckRetainedCollar (c * precision b.val.1) → retainedCore f R :=
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b
    (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le ∘
      neckRetainedCollarHomeomorph (c * precision b.val.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedPoint ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedPoint

theorem finiteStaticCapInclusion_retained (b : FullGB) (hD : 0 < D)
    (x : neckRetainedCollar (c * precision b.val.1)) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace FullGE3 FullGQ :=
      finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ FullGQ :=
      finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    finiteStaticCapInclusion hδ f hf hdisj hs U g R c hc x₀ order d₀ d w b hD
      (((w b).toStaticCapWitness hD).retained x) =
        finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R
          (finiteStaticRetainedPoint hδ f hf hdisj R c hc b x) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace FullGE3 FullGQ :=
    finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ FullGQ :=
    finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  exact (congrFun (finiteFullWitnessMap_closed_collar I hδ f hf hdisj hs U g R c hc
    x₀ order d₀ d w b) (neckRetainedCollarHomeomorph _ x)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_retained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_retained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_retained ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_retained

include hOriginal hmap hside in
theorem finiteStaticRetainedPoint_eq_neck (b : FullGB)
    (x : neckRetainedCollar (c * precision b.val.1))
    (hx : x.val ∈ neckBuffer (c * precision b.val.1)) :
    (finiteStaticRetainedPoint hδ f hf hdisj R c hc b x).val.val =
      (((d b).oriented.toNormalizedNeck).chart ⟨x.val, hx⟩).val := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace FullGE3 FullGQ :=
    finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let q := neckRetainedCollarHomeomorph (c * precision b.val.1) x
  change f b.val.1 (cuttingCollarCylinderMap (hδ b.val.1) b.val.2
    (q.1, ⟨q.2.val, q.2.property.1,
      q.2.property.2.trans_le (preparedFullCapWidth_bounds c (precision b.val.1) hc
        (hδ b.val.1)).2.le⟩)) = ((d b).oriented.positiveRetainedMap q).val
  rw [hOriginal b.val.1]
  exact congrArg Subtype.val
    (preparedDatum_closed_collar (d₀ b.val.1) b.val.2 (hrec b) (d b) (hmap b) (hside b)
      (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le q).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedPoint_eq_neck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedPoint_eq_neck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedPoint_eq_neck ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedPoint_eq_neck

theorem finiteStaticCapInclusion_cap (b : FullGB) (hD : 0 < D) (x : ThreeBall) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace FullGE3 FullGQ :=
      finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ FullGQ :=
      finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    finiteStaticCapInclusion hδ f hf hdisj hs U g R c hc x₀ order d₀ d w b hD
      (((w b).toStaticCapWitness hD).cap x) =
        (⟨finiteCapInclusion transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
          ⟨b.val, standardCapBallDiffeomorph x⟩, b.property⟩ : FullGRet) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace FullGE3 FullGQ :=
    finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ FullGQ :=
    finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  change finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
    ((w b).data.capInclusion (standardCapBallDiffeomorph x)) = _
  rw [(w b).properties.capInclusion_eq]
  apply Subtype.ext
  exact congrArg (fun p : finiteCapRestrictedNeighborhood transitionEnd_pos hδ f hf hdisj b.val
      ((c * precision b.val.1)⁻¹) => p.val)
    (finiteCapFullInsertionDiffeomorph_symm_cap I Fact.out transitionEnd_pos hδ f hf hdisj hs b.val
      (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le
      (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1
      (standardCapBallDiffeomorph x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_cap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_cap


variable [Fintype ι] (hδ1 : ∀ i, precision i < 1)
  (hnontrivial : Nonempty ι ∨ Nonempty (retainedCore f Rᶜ))

def finiteStaticRetainedTubePoint (b : FullGB) :
    neckRetainedCollar (c * precision b.val.1) →
      (TubeSystem.ofBufferedCharts hδ hδ1 f hf hdisj).core :=
  fun x => (bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj).symm
    (finiteStaticRetainedPoint hδ f hf hdisj R c hc b x).val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedTubePoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedTubePoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedTubePoint ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedTubePoint

omit [IsManifold I ∞ M] in
theorem finiteStaticRetainedTubePoint_mem (b : FullGB)
    (x : neckRetainedCollar (c * precision b.val.1)) :
    finiteStaticRetainedTubePoint hδ f hf hdisj R c hc hδ1 b x ∈
      (CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R
        hnontrivial).retainedCore := by
  rw [CutCapTopology.ofBufferedFiniteCaps_retainedCore]
  change bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj
    ((bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj).symm _) ∈ retainedCore f R
  rw [Homeomorph.apply_symm_apply]
  exact (finiteStaticRetainedPoint hδ f hf hdisj R c hc b x).property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedTubePoint_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedTubePoint_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedTubePoint_mem ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedTubePoint_mem

include hOriginal hmap hside in
theorem finiteStaticRetainedTubePoint_eq_neck (b : FullGB)
    (x : neckRetainedCollar (c * precision b.val.1))
    (hx : x.val ∈ neckBuffer (c * precision b.val.1)) :
    (finiteStaticRetainedTubePoint hδ f hf hdisj R c hc hδ1 b x).val =
      (((d b).oriented.toNormalizedNeck).chart ⟨x.val, hx⟩).val :=
  finiteStaticRetainedPoint_eq_neck hδ f hf hdisj U g R c hc
    x₀ order d₀ hOriginal hrec d hmap hside b x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedTubePoint_eq_neck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedTubePoint_eq_neck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedTubePoint_eq_neck ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticRetainedTubePoint_eq_neck

theorem finiteStaticCapInclusion_cap_presentation (b : FullGB) (hD : 0 < D)
    (x : ThreeBall) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace FullGE3 FullGQ :=
      finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ FullGQ :=
      finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    (CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R
      hnontrivial).presentation
        ((Capping.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj).cap b.val x) =
      Sum.inl (finiteStaticCapInclusion hδ f hf hdisj hs U g R c hc
        x₀ order d₀ d w b hD (((w b).toStaticCapWitness hD).cap x)) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace FullGE3 FullGQ :=
    finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ FullGQ :=
    finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  rw [finiteStaticCapInclusion_cap]
  exact finiteCapSelectedDiffeomorph_symm_retained I Fact.out transitionEnd_pos hδ f hf hdisj R
    (finiteCapInclusion transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      ⟨b.val, standardCapBallDiffeomorph x⟩) b.property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_cap_presentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_cap_presentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_cap_presentation ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_cap_presentation

theorem finiteStaticCapInclusion_retained_presentation (b : FullGB) (hD : 0 < D)
    (x : neckRetainedCollar (c * precision b.val.1)) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace FullGE3 FullGQ :=
      finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ FullGQ :=
      finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    (CutCapTopology.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj R
      hnontrivial).presentation
        ((Capping.ofBufferedFiniteCaps transitionEnd_pos hδ hδ1 f hf hdisj).coreInclusion
          (finiteStaticRetainedTubePoint hδ f hf hdisj R c hc hδ1 b x)) =
      Sum.inl (finiteStaticCapInclusion hδ f hf hdisj hs U g R c hc
        x₀ order d₀ d w b hD (((w b).toStaticCapWitness hD).retained x)) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace FullGE3 FullGQ :=
    finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ FullGQ :=
    finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  rw [finiteStaticCapInclusion_retained, Capping.ofBufferedFiniteCaps_coreInclusion]
  change (finiteCapSelectedDiffeomorph I Fact.out transitionEnd_pos hδ f hf hdisj R).symm
    (finiteCoreInclusion transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      ((bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj)
        ((bufferedCutCoreHomeomorph hδ hδ1 f hf hdisj).symm _))) = _
  rw [Homeomorph.apply_symm_apply]
  exact finiteCapSelectedDiffeomorph_symm_retained I Fact.out transitionEnd_pos hδ f hf hdisj R
    (finiteCoreInclusion transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
      (finiteStaticRetainedPoint hδ f hf hdisj R c hc b x).val)
    (finiteStaticRetainedPoint hδ f hf hdisj R c hc b x).property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_retained_presentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_retained_presentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_retained_presentation ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteStaticCapInclusion_retained_presentation

end DifferentialGeometry.PDE.RicciFlow.StandardCap
