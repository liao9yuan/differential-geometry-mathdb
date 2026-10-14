import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricRetainedCollar
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RetainedCoreInteriorDifferential

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
private abbrev FullCoreTensorGE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.FullCoreTensorGE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.FullCoreTensorGE3 target :: scope.openDecls } }
private abbrev FullCoreTensorGIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.FullCoreTensorGIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.FullCoreTensorGIC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceFullCoreTensorGE3InsertionQuotient {B : ℝ} {hB : 0 < B} : ChartedSpace FullCoreTensorGE3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceFullCoreTensorGE3InsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceFullCoreTensorGE3InsertionQuotient target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealFullCoreTensorGE3 : NeZero (Module.finrank ℝ FullCoreTensorGE3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealFullCoreTensorGE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealFullCoreTensorGE3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient target :: scope.openDecls } }
private abbrev FullCoreTensorIH := ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.FullCoreTensorIH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.FullCoreTensorIH target :: scope.openDecls } }
private abbrev FullCoreTensorIR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.FullCoreTensorIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.FullCoreTensorIR target :: scope.openDecls } }
private abbrev FullCoreTensorS2 := Metric.sphere (0 : FullCoreTensorGE3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.FullCoreTensorS2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.FullCoreTensorS2 target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph FullCoreTensorGIC I ∞ (f i))
local notation "FullCoreTensorGQ" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (R : Set (ConnectedComponents (cutCore f)))
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
variable (c : ℝ) (hc : 4 ≤ c)
local notation "FullCoreTensorGRet" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "FullCoreTensorGOld" => finiteRetainedInteriorOpens transitionEnd_pos hδ f hf hdisj R
local notation "FullCoreTensorGB" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
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

theorem finiteFullPreparedMetric_retainedCore_interior (p : retainedCore f R)
    (hp : p.val.val ∈ interior (cutCore f)) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace FullCoreTensorIH (retainedCore f R) := retainedCoreChartedSpace I Fact.out hδ f hf hdisj R
    let : ChartedSpace FullCoreTensorGE3 FullCoreTensorGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ FullCoreTensorGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let Φ := finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R
    let Ψ := retainedCoreDomainMap f R U hRet
    ∀ (v z : TangentSpace FullCoreTensorIR p),
      gRet.inner (Φ p) (mfderiv FullCoreTensorIR (𝓡 3) Φ p v) (mfderiv FullCoreTensorIR (𝓡 3) Φ p z) =
        g.inner (Ψ p) (mfderiv FullCoreTensorIR I Ψ p v) (mfderiv FullCoreTensorIR I Ψ p z) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace FullCoreTensorIH (retainedCore f R) := retainedCoreChartedSpace I Fact.out hδ f hf hdisj R
  let : ChartedSpace FullCoreTensorGE3 FullCoreTensorGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ FullCoreTensorGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let Φ := finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R
  let Ψ := retainedCoreDomainMap f R U hRet
  dsimp only
  intro v z
  have hd : mfderiv FullCoreTensorIR (𝓡 3) Φ p =
      (mfderiv I (𝓡 3) (finiteCoreInteriorMap transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj)
        (⟨p.val.val, hp⟩ : coreInteriorDomain f)).comp (mfderiv FullCoreTensorIR I Ψ p) :=
    finiteRetainedCoreInclusion_mfderiv_interior I Fact.out transitionEnd_pos hδ f hf hdisj hs R U hRet p hp
  change gRet.inner (Φ p) (mfderiv FullCoreTensorIR (𝓡 3) Φ p v) (mfderiv FullCoreTensorIR (𝓡 3) Φ p z) =
    g.inner (Ψ p) (mfderiv FullCoreTensorIR I Ψ p v) (mfderiv FullCoreTensorIR I Ψ p z)
  rw [hd]
  exact finiteFullPreparedMetric_original_inner I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    ⟨p.val.val, hp⟩ p.property (mfderiv FullCoreTensorIR I Ψ p v) (mfderiv FullCoreTensorIR I Ψ p z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_retainedCore_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_retainedCore_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_retainedCore_interior ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_retainedCore_interior

theorem finiteFullPreparedMetric_retainedCore_inner :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace FullCoreTensorIH (retainedCore f R) := retainedCoreChartedSpace I Fact.out hδ f hf hdisj R
    let : ChartedSpace FullCoreTensorGE3 FullCoreTensorGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ FullCoreTensorGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let Φ := finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R
    let Ψ := retainedCoreDomainMap f R U hRet
    ∀ (p : retainedCore f R) (v z : TangentSpace FullCoreTensorIR p),
      gRet.inner (Φ p) (mfderiv FullCoreTensorIR (𝓡 3) Φ p v) (mfderiv FullCoreTensorIR (𝓡 3) Φ p z) =
        g.inner (Ψ p) (mfderiv FullCoreTensorIR I Ψ p v) (mfderiv FullCoreTensorIR I Ψ p z) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace FullCoreTensorIH (retainedCore f R) := retainedCoreChartedSpace I Fact.out hδ f hf hdisj R
  let : ChartedSpace FullCoreTensorGE3 FullCoreTensorGQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ FullCoreTensorGQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let Φ := finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R
  let Ψ := retainedCoreDomainMap f R U hRet
  dsimp only
  intro p v z
  by_cases hp : p.val.val ∈ interior (cutCore f)
  · exact finiteFullPreparedMetric_retainedCore_interior I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w p hp v z
  · have hfront : p.val ∈ _root_.Set.range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) := by
      rw [range_cuttingSphereAttachment hδ f hf hdisj]
      exact ⟨subset_closure p.val.property, hp⟩
    obtain ⟨⟨b, y⟩, he⟩ := hfront
    have hb : cuttingSphereComponent hδ f hf hdisj b ∈ R :=
      (cuttingSphere_mem_retainedCore_iff hδ f hf hdisj R b y).mp (he.symm ▸ p.property)
    let b' : FullCoreTensorGB := ⟨b, hb⟩
    let hB := (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).1
    let q : FullCoreTensorS2 × _root_.Set.Ico (0 : ℝ) (c * precision b.1)⁻¹ := (y, ⟨0, le_rfl, hB⟩)
    let κ := finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b' (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).2.le
    have hq : κ q = p := Subtype.ext
      ((finiteRetainedCollarCoreMap_zero transitionEnd_pos hδ f hf hdisj R b'
        (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).2.le hB y).trans he)
    have h : ∀ (v' z' : TangentSpace FullCoreTensorIR (κ q)),
        gRet.inner (Φ (κ q)) (mfderiv FullCoreTensorIR (𝓡 3) Φ (κ q) v') (mfderiv FullCoreTensorIR (𝓡 3) Φ (κ q) z') =
          g.inner (Ψ (κ q)) (mfderiv FullCoreTensorIR I Ψ (κ q) v') (mfderiv FullCoreTensorIR I Ψ (κ q) z') :=
      finiteFullPreparedMetric_retainedCore_collar I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w b' q
    rw [hq] at h
    exact h v z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_retainedCore_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_retainedCore_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_retainedCore_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_retainedCore_inner
end DifferentialGeometry.PDE.RicciFlow.StandardCap
