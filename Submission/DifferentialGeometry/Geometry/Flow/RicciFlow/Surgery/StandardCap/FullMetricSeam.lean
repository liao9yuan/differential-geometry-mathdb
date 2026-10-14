import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FullMetricConclusions
import Submission.DifferentialGeometry.Geometry.Curvature.EmbeddingIsometry

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Metric
  DifferentialGeometry.Topology.ThreeManifold.Surgery DifferentialGeometry.Topology.Manifold.Attachment
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev SeamGE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.SeamGE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.SeamGE3 target :: scope.openDecls } }
private abbrev SeamGIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.SeamGIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.SeamGIC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceSeamGE3InsertionQuotient {B : ℝ} {hB : 0 < B} : ChartedSpace SeamGE3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceSeamGE3InsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instChartedSpaceSeamGE3InsertionQuotient target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient {B : ℝ} {hB : 0 < B} : IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopInsertionQuotient target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealSeamGE3 : NeZero (Module.finrank ℝ SeamGE3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealSeamGE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instNeZeroNatFinrankRealSeamGE3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient {B : ℝ} {hB : 0 < B} : T2Space (InsertionQuotient hB) :=
  radialCapAttachment_t2Space transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instT2SpaceInsertionQuotient target :: scope.openDecls } }
private abbrev SeamIH := ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.SeamIH
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.SeamIH target :: scope.openDecls } }
private abbrev SeamIR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.SeamIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.SeamIR target :: scope.openDecls } }
private abbrev SeamS2 := Metric.sphere (0 : SeamGE3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.SeamS2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.SeamS2 target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph SeamGIC I ∞ (f i))
local notation "SeamQ" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (R : Set (ConnectedComponents (cutCore f)))
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
variable (c : ℝ) (hc : 4 ≤ c)
local notation "SeamRet" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "SeamOld" => finiteRetainedInteriorOpens transitionEnd_pos hδ f hf hdisj R
local notation "SeamB" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
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

omit [SigmaCompactSpace M] in
theorem finiteFullPreparedMetric_restrict_retainedInterior :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace SeamGE3 SeamQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ SeamQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space SeamQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    (finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w).restrictOpenOfSubset inf_le_left =
      finiteOldMetric I Fact.out transitionEnd_pos hδ f hf hdisj hs U g R hRet := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace SeamGE3 SeamQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ SeamQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space SeamQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  apply SmoothRiemannianMetric.ext_inner
  intro q v z
  exact finiteGluedMetric_inner_old I hδ f hf hdisj hs U g R hRet
    (fun b => (c * precision b.1)⁻¹) (fun b => (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).1)
    x₀ order d₀ hOriginal hrec d hmap hside w
    (fun b => (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le)
    (fun _ => le_rfl) q v z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_restrict_retainedInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_restrict_retainedInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_restrict_retainedInterior ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_restrict_retainedInterior

theorem finiteFullPreparedMetric_curvature_retainedInterior :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace SeamGE3 SeamQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ SeamQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : T2Space SeamQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let Ψ := finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet
    ∀ q : SeamOld,
      metricScalarAt gRet (Opens.inclusion inf_le_left q) = metricScalarAt g (Ψ q) ∧
        leastCurvatureOperatorEigenvalueAt gRet (Opens.inclusion inf_le_left q)
            (metricAlgebraicCurvatureTensorAt gRet (Opens.inclusion inf_le_left q)) =
          leastCurvatureOperatorEigenvalueAt g (Ψ q) (metricAlgebraicCurvatureTensorAt g (Ψ q)) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace SeamGE3 SeamQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ SeamQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space SeamQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  let : SecondCountableTopology H := I.secondCountableTopology
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let F := finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet
  have hlocal := isLocalDiffeomorph_finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj I Fact.out hs U R hRet
  have hi : _root_.Topology.IsOpenEmbedding F :=
    .of_continuous_injective_isOpenMap hlocal.contMDiff.continuous
      (injective_finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet) hlocal.isOpenMap
  let : SecondCountableTopology SeamOld := hi.isEmbedding.secondCountableTopology
  let : LocallyCompactSpace SeamOld := ChartedSpace.locallyCompactSpace SeamGE3 SeamOld
  let : SigmaCompactSpace SeamOld := inferInstance
  let old := finiteOldMetric I Fact.out transitionEnd_pos hδ f hf hdisj hs U g R hRet
  let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
  let inc : SeamOld → SeamRet := Opens.inclusion inf_le_left
  have hi' : _root_.Function.Injective inc := fun _ _ he => Subtype.ext (congrArg (fun q : SeamRet => q.val) he)
  have hl : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ inc := by
    apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
      (contMDiff_inclusion (n := ∞) (show SeamOld ≤ SeamRet from inf_le_left)) _ rfl
    intro q
    rw [mfderiv_opens_incl]
    exact fun _ _ he => he
  have hm : ∀ (q : SeamOld) (v z : TangentSpace (𝓡 3) q),
      old.inner q v z = gRet.inner (inc q) (mfderiv (𝓡 3) (𝓡 3) inc q v) (mfderiv (𝓡 3) (𝓡 3) inc q z) := by
    intro q v z
    dsimp only [inc]
    rw [mfderiv_opens_incl]
    exact (finiteGluedMetric_inner_old I hδ f hf hdisj hs U g R hRet
      (fun b => (c * precision b.1)⁻¹) (fun b => (preparedFullCapWidth_bounds c (precision b.1) hc (hδ b.1)).1)
      x₀ order d₀ hOriginal hrec d hmap hside w
      (fun b => (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le)
      (fun _ => le_rfl) q v z).symm
  dsimp only
  intro q
  have hglobal := curvature_of_injective_local_isometry old gRet inc hl hi' hm q
  have horiginal := curvature_of_injective_local_isometry old g F hlocal
    (injective_finiteRetainedInteriorOriginalMap transitionEnd_pos hδ f hf hdisj U R hRet)
    (finiteOldMetric_inner I Fact.out transitionEnd_pos hδ f hf hdisj hs U g R hRet) q
  exact ⟨hglobal.1.symm.trans horiginal.1, hglobal.2.symm.trans horiginal.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_curvature_retainedInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_curvature_retainedInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_curvature_retainedInterior ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_curvature_retainedInterior

omit [SigmaCompactSpace M] in
theorem finiteFullPreparedMetric_collar_comparison (b : SeamB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace SeamGE3 SeamQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ SeamQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    let : ChartedSpace (EuclideanHalfSpace 1) (_root_.Set.Ico (0 : ℝ) (c * precision b.val.1)⁻¹) :=
      halfClosedIntervalChartedSpace (inv_pos.mpr (d b).precision_pos)
    let gRet := finiteFullPreparedMetric I hδ f hf hdisj hs U g R hRet c hc x₀ order d₀ hOriginal hrec d hmap hside w
    let Φ := finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R ∘ (finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le)
    let Ψ := retainedCoreDomainMap f R U hRet ∘ (finiteRetainedCollarCoreMap transitionEnd_pos hδ f hf hdisj R b (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le)
    (∀ (q : SeamS2 × _root_.Set.Ico (0 : ℝ) (c * precision b.val.1)⁻¹) (v : TangentSpace SeamIR q),
      gRet.inner (Φ q) (mfderiv SeamIR (𝓡 3) Φ q v) (mfderiv SeamIR (𝓡 3) Φ q v) ≤
        g.inner (Ψ q) (mfderiv SeamIR I Ψ q v) (mfderiv SeamIR I Ψ q v)) ∧
    (∀ (q : SeamS2 × _root_.Set.Ico (0 : ℝ) (c * precision b.val.1)⁻¹) (v : TangentSpace SeamIR q),
      g.inner (Ψ q) (mfderiv SeamIR I Ψ q v) (mfderiv SeamIR I Ψ q v) ≤
        gRet.inner (Φ q) (mfderiv SeamIR (𝓡 3) Φ q v) (mfderiv SeamIR (𝓡 3) Φ q v)) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace SeamGE3 SeamQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ SeamQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  dsimp only
  have h := finiteFullPreparedMetric_closed_collar I hδ f hf hdisj hs U g R hRet c hc
    x₀ order d₀ hOriginal hrec d hmap hside w b
  exact ⟨fun q v => (h q v v).le, fun q v => (h q v v).ge⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_collar_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_collar_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_collar_comparison ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteFullPreparedMetric_collar_comparison

end DifferentialGeometry.PDE.RicciFlow.StandardCap
