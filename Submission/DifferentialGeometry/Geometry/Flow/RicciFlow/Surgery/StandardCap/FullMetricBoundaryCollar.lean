import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricModels
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RetainedCoreMaps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev BoundaryGE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.BoundaryGE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.BoundaryGE3 target :: scope.openDecls } }
private abbrev BoundaryGIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.BoundaryGIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.BoundaryGIC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceBoundaryGE3InsertionQuotient {B : ℝ} {hB : 0 < B} : ChartedSpace BoundaryGE3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceBoundaryGE3InsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceBoundaryGE3InsertionQuotient target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealBoundaryGE3 : NeZero (Module.finrank ℝ BoundaryGE3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealBoundaryGE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealBoundaryGE3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient target :: scope.openDecls } }
private abbrev BoundaryIR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.BoundaryIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.BoundaryIR target :: scope.openDecls } }
private abbrev BoundaryS2 := Metric.sphere (0 : BoundaryGE3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.BoundaryS2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.BoundaryS2 target :: scope.openDecls } }
section Correspondence
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ δ' : ℝ} {k k' : ℕ}

theorem preparedDatum_closed_collar (d : normalizedDatum g x₀ δ k) (b : Bool)
    (hrec : δ'⁻¹ + 1 ≤ δ⁻¹)
    (d' : normalizedDatum g (d.offsetPoint (cuttingSign_sq b)) δ' k')
    (hmap : d'.map = d.recenteringMap (cuttingSign_sq b) hrec) (hside : d'.retainedSide = _root_.Bool.true)
    (hfit : δ'⁻¹ ≤ cuttingCollarWidth δ) (q : BoundaryS2 × _root_.Set.Ico (0 : ℝ) δ'⁻¹) :
    d'.oriented.positiveRetainedMap q = d.map (cuttingCollarCylinderMap d.precision_pos b
      (q.1, ⟨q.2.val, q.2.property.1, q.2.property.2.trans_le hfit⟩)) := by
  rw [normalizedDatum.positiveRetainedMap_apply, normalizedDatum.oriented_map_of_retainedSide_true d' hside,
    hmap, normalizedDatum.recenteringMap_apply]
  apply congrArg d.map
  apply Subtype.ext
  rw [cuttingCollarCylinderMap_val]
  change (q.1, cuttingSign b * (1 + q.2.val)) = (q.1, cuttingSign b + cuttingSign b * q.2.val)
  exact Prod.ext rfl (by ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.preparedDatum_closed_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.preparedDatum_closed_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.preparedDatum_closed_collar ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.preparedDatum_closed_collar
end Correspondence
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph BoundaryGIC I ∞ (f i))
local notation "BoundaryGQ" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (R : Set (ConnectedComponents (cutCore f)))
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
variable (c : ℝ) (hc : 4 ≤ c)
local notation "BoundaryGRet" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "BoundaryGOld" => finiteRetainedInteriorOpens transitionEnd_pos hδ f hf hdisj R
local notation "BoundaryGB" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
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

theorem finiteFullWitnessMap_closed_collar (b : BoundaryGB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace BoundaryGE3 BoundaryGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R ∘ (finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le) =
      (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b) ∘ (w b).data.retainedInclusion := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace BoundaryGE3 BoundaryGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  dsimp only
  funext q
  apply Subtype.ext
  change finiteCoreInclusion transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
    (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b.val
      (q.1, ⟨q.2.val, q.2.property.1, q.2.property.2.trans_le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le⟩)) =
        ((finiteCapFullInsertionDiffeomorph I Fact.out transitionEnd_pos hδ f hf hdisj hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1).symm ((w b).data.retainedInclusion q)).val
  rw [(w b).properties.retainedInclusion_eq]
  exact (congrArg Subtype.val
    (finiteCapFullInsertionDiffeomorph_symm_collar I Fact.out transitionEnd_pos hδ f hf hdisj hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le
      (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1 q)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullWitnessMap_closed_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullWitnessMap_closed_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullWitnessMap_closed_collar ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullWitnessMap_closed_collar

include hOriginal hmap hside in
theorem retainedCoreDomainMap_closed_collar (b : BoundaryGB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace BoundaryGE3 BoundaryGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    retainedCoreDomainMap f R U hRet ∘ (finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le) = (d b).oriented.positiveRetainedMap := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace BoundaryGE3 BoundaryGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  dsimp only
  funext q
  apply Subtype.ext
  change f b.val.1 (cuttingCollarCylinderMap (hδ b.val.1) b.val.2
    (q.1, ⟨q.2.val, q.2.property.1, q.2.property.2.trans_le (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le⟩)) =
      ((d b).oriented.positiveRetainedMap q).val
  rw [hOriginal b.val.1]
  exact congrArg Subtype.val
    (preparedDatum_closed_collar (d₀ b.val.1) b.val.2 (hrec b) (d b) (hmap b) (hside b) (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le q).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.retainedCoreDomainMap_closed_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.retainedCoreDomainMap_closed_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.retainedCoreDomainMap_closed_collar ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.retainedCoreDomainMap_closed_collar

include w hOriginal hmap hside in
theorem finiteRetained_closed_collar_smooth (b : BoundaryGB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace BoundaryGE3 BoundaryGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ BoundaryGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (c * precision b.val.1)⁻¹) :=
      halfClosedIntervalChartedSpace (inv_pos.mpr (d b).precision_pos)
    ContMDiff BoundaryIR (𝓡 3) ∞ (finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R ∘ (finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le)) ∧
      ContMDiff BoundaryIR I ∞ (retainedCoreDomainMap f R U hRet ∘ (finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le)) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace BoundaryGE3 BoundaryGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ BoundaryGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (c * precision b.val.1)⁻¹) :=
    halfClosedIntervalChartedSpace (inv_pos.mpr (d b).precision_pos)
  dsimp only
  rw [finiteFullWitnessMap_closed_collar I hδ f hf hdisj hs U g R c hc x₀ order d₀ d w b, retainedCoreDomainMap_closed_collar I hδ f hf hdisj U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside b]
  exact ⟨(contMDiff_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b).comp
    (w b).properties.retained_embedding.contMDiff, (d b).oriented.positiveRetainedMap_smooth⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteRetained_closed_collar_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteRetained_closed_collar_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteRetained_closed_collar_smooth ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteRetained_closed_collar_smooth

theorem finiteFullPreparedMetric_closed_collar (b : BoundaryGB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace BoundaryGE3 BoundaryGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ BoundaryGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (c * precision b.val.1)⁻¹) :=
      halfClosedIntervalChartedSpace (inv_pos.mpr (d b).precision_pos)
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let Φ := finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R ∘ (finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le)
    let Ψ := retainedCoreDomainMap f R U hRet ∘ (finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le)
    ∀ (q : BoundaryS2 × _root_.Set.Ico (0 : ℝ) (c * precision b.val.1)⁻¹) (v z : TangentSpace BoundaryIR q),
      gRet.inner (Φ q) (mfderiv BoundaryIR (𝓡 3) Φ q v) (mfderiv BoundaryIR (𝓡 3) Φ q z) =
        g.inner (Ψ q) (mfderiv BoundaryIR I Ψ q v) (mfderiv BoundaryIR I Ψ q z) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace BoundaryGE3 BoundaryGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ BoundaryGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (c * precision b.val.1)⁻¹) :=
    halfClosedIntervalChartedSpace (inv_pos.mpr (d b).precision_pos)
  dsimp only
  rw [finiteFullWitnessMap_closed_collar I hδ f hf hdisj hs U g R c hc x₀ order d₀ d w b, retainedCoreDomainMap_closed_collar I hδ f hf hdisj U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside b]
  intro q v z
  exact (metric_inner_comp_of_isometry (w b).data.outMetric
    (finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w)
    (finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
    (contMDiff_finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b)
    (finiteFullPreparedMetric_witness_inner I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b)
    (w b).data.retainedInclusion (w b).properties.retained_embedding.contMDiff q v z).trans
      ((w b).properties.retained_metric q v z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_closed_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_closed_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_closed_collar ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_closed_collar
end DifferentialGeometry.PDE.RicciFlow.StandardCap
