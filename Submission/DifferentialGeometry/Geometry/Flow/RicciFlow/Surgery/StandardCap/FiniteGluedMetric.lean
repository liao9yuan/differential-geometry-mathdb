import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.FinitePreparedMetricOverlap
import Submission.DifferentialGeometry.Geometry.Metric.FamilyGluing

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
private abbrev GluedE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.GluedE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.GluedE3 target :: scope.openDecls } }
private abbrev GluedIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.GluedIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.GluedIC target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ}
variable (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph GluedIC I ∞ (f i))
local notation "GluedQ" => FiniteCapQuotient transitionEnd_pos hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
variable (U : Opens M) (g : SmoothRiemannianMetric I U)
variable (R : Set (ConnectedComponents (cutCore f)))
variable (hRet : MapsTo (Subtype.val : cutCore f → M) (retainedCore f R) U)
variable (r : ι × Bool → ℝ) (hr : ∀ b, 0 < r b)
local notation "GluedRet" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "GluedOld" => finiteRetainedInteriorOpens transitionEnd_pos hδ f hf hdisj R
local notation "GluedB" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}
local notation "GluedPatch" b => finiteCapRestrictedNeighborhood transitionEnd_pos hδ f hf hdisj b (r b)

private def gluingDomain (i : Option GluedB) : _root_.TopologicalSpace.Opens GluedQ := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  exact match i with
  | none => GluedOld
  | some b => GluedPatch b.val

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.gluingDomain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.gluingDomain target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private theorem gluingDomain_subset_retained (i : Option GluedB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    gluingDomain I hδ f hf hdisj R r i ≤ GluedRet := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  cases i with
  | none => exact inf_le_left
  | some b => exact finiteCapRestrictedNeighborhood_subset_retained transitionEnd_pos hδ f hf hdisj R b.val b.property (r b.val)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.gluingDomain_subset_retained
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.gluingDomain_subset_retained target :: scope.openDecls } }

include hr in
omit [IsManifold I ∞ M] in
private theorem gluingDomain_cover :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    ∀ x : GluedRet, ∃ i : Option GluedB, x.val ∈ gluingDomain I hδ f hf hdisj R r i := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  dsimp only
  intro x
  have he := Set.ext_iff.mp (finiteCapRetained_restricted_cover transitionEnd_pos hδ f hf hdisj R r hr) x.val
  rcases he.mpr x.property with ho | hc
  · exact ⟨none, ho⟩
  · obtain ⟨b, hb⟩ := mem_iUnion.mp hc
    exact ⟨some b, hb⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.gluingDomain_cover
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.gluingDomain_cover target :: scope.openDecls } }

variable (x₀ : ι → U) (order : ι → ℕ)
variable (d₀ : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
variable (hOriginal : ∀ i, f i = neckAmbientMap U (d₀ i))
variable {δ' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℝ} {k' : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ}
variable (hrec : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (δ' b)⁻¹ + 1 ≤ (precision b.val.1)⁻¹)
variable (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g
  ((d₀ b.val.1).offsetPoint (cuttingSign_sq b.val.2)) (δ' b) (k' b))
variable (hmap : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).map = (d₀ b.val.1).recenteringMap (cuttingSign_sq b.val.2) (hrec b))
variable (hside : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, (d b).retainedSide = true)
variable {A D ε : ℝ} {hA : 0 < A} {m : ℕ}
variable (w : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, CanonicalStaticInsertionWitness (d b) A hA D m ε)
variable (hfit : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, r b.val ≤ cuttingCollarWidth (precision b.val.1))
variable (hstatic : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, r b.val ≤ (δ' b)⁻¹)

private def localMetrics :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    ∀ i : Option GluedB, SmoothRiemannianMetric (𝓡 3) (gluingDomain I hδ f hf hdisj R r i) := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  dsimp only
  intro i
  cases i with
  | none => exact finiteOldMetric I Fact.out transitionEnd_pos hδ f hf hdisj hs U g R hRet
  | some b => exact finiteCapWitnessMetric I Fact.out hδ f hf hdisj hs (d b) (w b) b.val (r b.val) (hfit b) (hstatic b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.localMetrics
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.localMetrics target :: scope.openDecls } }

include hOriginal hmap hside in
private theorem localMetrics_compatible :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    ∀ (i j : Option GluedB) (x : GluedQ)
      (hi : x ∈ gluingDomain I hδ f hf hdisj R r i)
      (hj : x ∈ gluingDomain I hδ f hf hdisj R r j) (v z : TangentSpace (𝓡 3) x),
      (localMetrics I hδ f hf hdisj hs U g R hRet r x₀ order d₀ d w hfit hstatic i).inner ⟨x, hi⟩ v z =
        (localMetrics I hδ f hf hdisj hs U g R hRet r x₀ order d₀ d w hfit hstatic j).inner ⟨x, hj⟩ v z := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  dsimp only
  intro i j x hi hj v z
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some b =>
      exact finitePreparedMetricOverlap_inner I Fact.out hδ f hf hdisj hs U g R hRet
        b.val b.property (r b.val) (hfit b) (d₀ b.val.1) (hOriginal b.val.1)
        (hrec b) (d b) (hmap b) (hside b) (w b) (hstatic b) ⟨x, hj⟩ hi.2 v z
  | some b =>
    cases j with
    | none =>
      exact (finitePreparedMetricOverlap_inner I Fact.out hδ f hf hdisj hs U g R hRet
        b.val b.property (r b.val) (hfit b) (d₀ b.val.1) (hOriginal b.val.1)
        (hrec b) (d b) (hmap b) (hside b) (w b) (hstatic b) ⟨x, hi⟩ hj.2 v z).symm
    | some c =>
      by_cases he : b = c
      · subst c
        rfl
      · have hbc : b.val ≠ c.val := fun he' => he (Subtype.ext he')
        exact (Set.disjoint_left.mp (pairwise_disjoint_finiteCapRestrictedNeighborhoods
          transitionEnd_pos hδ f hf hdisj r hbc) hi hj).elim

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.localMetrics_compatible
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.localMetrics_compatible target :: scope.openDecls } }

def finiteGluedMetric :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    SmoothRiemannianMetric (𝓡 3) GluedRet := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space GluedQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  exact glueMetricFamilyOn (gluingDomain I hδ f hf hdisj R r)
    (localMetrics I hδ f hf hdisj hs U g R hRet r x₀ order d₀ d w hfit hstatic)
    GluedRet (gluingDomain_subset_retained I hδ f hf hdisj R r)
    (gluingDomain_cover I hδ f hf hdisj R r hr)
    (localMetrics_compatible I hδ f hf hdisj hs U g R hRet r x₀ order d₀ hOriginal hrec d hmap hside w hfit hstatic)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteGluedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteGluedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteGluedMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteGluedMetric

theorem finiteGluedMetric_inner_old :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    ∀ (q : GluedOld) (v z : TangentSpace (𝓡 3) q),
      (finiteGluedMetric I hδ f hf hdisj hs U g R hRet r hr x₀ order d₀ hOriginal hrec d hmap hside w hfit hstatic).inner
        (Opens.inclusion inf_le_left q) v z =
          (finiteOldMetric I Fact.out transitionEnd_pos hδ f hf hdisj hs U g R hRet).inner q v z := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space GluedQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro q v z
  exact glueMetricFamilyOn_inner (gluingDomain I hδ f hf hdisj R r)
    (localMetrics I hδ f hf hdisj hs U g R hRet r x₀ order d₀ d w hfit hstatic)
    GluedRet (gluingDomain_subset_retained I hδ f hf hdisj R r)
    (gluingDomain_cover I hδ f hf hdisj R r hr)
    (localMetrics_compatible I hδ f hf hdisj hs U g R hRet r x₀ order d₀ hOriginal hrec d hmap hside w hfit hstatic) _root_.Option.none q v z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteGluedMetric_inner_old then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteGluedMetric_inner_old"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteGluedMetric_inner_old ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteGluedMetric_inner_old

theorem finiteGluedMetric_inner_cap (b : GluedB) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    ∀ (q : GluedPatch b.val) (v z : TangentSpace (𝓡 3) q),
      (finiteGluedMetric I hδ f hf hdisj hs U g R hRet r hr x₀ order d₀ hOriginal hrec d hmap hside w hfit hstatic).inner
        (Opens.inclusion (finiteCapRestrictedNeighborhood_subset_retained transitionEnd_pos
          hδ f hf hdisj R b.val b.property (r b.val)) q) v z =
            (finiteCapWitnessMetric I Fact.out hδ f hf hdisj hs (d b) (w b) b.val (r b.val) (hfit b) (hstatic b)).inner q v z := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  let : T2Space GluedQ := finiteCapQuotient_t2Space transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro q v z
  exact glueMetricFamilyOn_inner (gluingDomain I hδ f hf hdisj R r)
    (localMetrics I hδ f hf hdisj hs U g R hRet r x₀ order d₀ d w hfit hstatic)
    GluedRet (gluingDomain_subset_retained I hδ f hf hdisj R r)
    (gluingDomain_cover I hδ f hf hdisj R r hr)
    (localMetrics_compatible I hδ f hf hdisj hs U g R hRet r x₀ order d₀ hOriginal hrec d hmap hside w hfit hstatic) (_root_.Option.some b) q v z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteGluedMetric_inner_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteGluedMetric_inner_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteGluedMetric_inner_cap ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteGluedMetric_inner_cap

theorem finiteGluedMetric_original_inner (p : coreInteriorDomain f)
    (hp : (⟨p.val, interior_subset p.property⟩ : cutCore f) ∈ retainedCore f R)
    (v z : TangentSpace I p) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
    (finiteGluedMetric I hδ f hf hdisj hs U g R hRet r hr x₀ order d₀ hOriginal hrec d hmap hside w hfit hstatic).inner
      (Opens.inclusion inf_le_left (finiteRetainedInteriorImage transitionEnd_pos hδ f hf hdisj R p hp))
      (mfderiv I (𝓡 3) (finiteCoreInteriorMap transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) p v)
      (mfderiv I (𝓡 3) (finiteCoreInteriorMap transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) p z) =
        g.inner ⟨p.val, hRet hp⟩ v z := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace GluedE3 GluedQ := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ GluedQ := finiteCapQuotient_isManifold Fact.out transitionEnd_pos hδ f hf hdisj hs
  exact (finiteGluedMetric_inner_old I hδ f hf hdisj hs U g R hRet r hr x₀ order d₀ hOriginal hrec d hmap hside w hfit hstatic
    (finiteRetainedInteriorImage transitionEnd_pos hδ f hf hdisj R p hp)
    (mfderiv I (𝓡 3) (finiteCoreInteriorMap transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) p v)
    (mfderiv I (𝓡 3) (finiteCoreInteriorMap transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj) p z)).trans
      (finiteOldMetric_original_inner I Fact.out transitionEnd_pos hδ f hf hdisj hs U g R hRet p hp v z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteGluedMetric_original_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteGluedMetric_original_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteGluedMetric_original_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.finiteGluedMetric_original_inner

end DifferentialGeometry.PDE.RicciFlow.StandardCap
