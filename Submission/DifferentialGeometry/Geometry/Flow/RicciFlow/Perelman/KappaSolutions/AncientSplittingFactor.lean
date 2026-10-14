import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplitting.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TerminalScalar
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalProductScalar
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Contractible

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Topology
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientSplittingFactorTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorTopology
local instance ancientSplittingFactorCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorCharted
local instance ancientSplittingFactorSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorSmooth
local instance ancientSplittingFactorC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorC1
local instance ancientSplittingFactorT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorT2
local instance ancientSplittingFactorSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorSigma
local instance ancientSplittingFactorInhabited : Inhabited F.M := ⟨F.basepoint⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorInhabited then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorInhabited"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorInhabited ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorInhabited

local instance ancientSplittingFactorLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorLocallyPathConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorLocallyPathConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorLocallyPathConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorLocallyPathConnected

local instance ancientSplittingFactorSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorSemilocallySimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorSemilocallySimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorSemilocallySimplyConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientSplittingFactorSemilocallySimplyConnected

private theorem simplyConnectedSpace_of_simplyConnectedSpace_prod_real {X : Type*}
    [TopologicalSpace X] [SimplyConnectedSpace (X × ℝ)] : SimplyConnectedSpace X := by
  let eR : ContinuousMap.HomotopyEquiv ℝ Unit :=
    Classical.choice (ContractibleSpace.hequiv ℝ Unit)
  let e : ContinuousMap.HomotopyEquiv (X × ℝ) X :=
    ((ContinuousMap.HomotopyEquiv.refl X).prodCongr eR).trans
      (Homeomorph.prodUnique X Unit).toHomotopyEquiv
  exact e.simplyConnectedSpace_iff.mp ‹SimplyConnectedSpace (X × ℝ)›

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.simplyConnectedSpace_of_simplyConnectedSpace_prod_real
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.simplyConnectedSpace_of_simplyConnectedSpace_prod_real target :: scope.openDecls } }

theorem connectedSpace_and_simplyConnectedSpace_of_universalCover_product
    (G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval)
    (Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M)
    (hconnected : ConnectedSpace F.M) :
    ConnectedSpace G.M ∧ SimplyConnectedSpace G.M := by
  let _ : TopologicalSpace G.M := G.topology
  let _ : ConnectedSpace F.M := hconnected
  have hsc : SimplyConnectedSpace (G.M × ℝ) :=
    Phi.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance
  let _ : SimplyConnectedSpace (G.M × ℝ) := hsc
  have hscG : SimplyConnectedSpace G.M := simplyConnectedSpace_of_simplyConnectedSpace_prod_real
  let _ : SimplyConnectedSpace G.M := hscG
  exact ⟨inferInstance, hscG⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.connectedSpace_and_simplyConnectedSpace_of_universalCover_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.connectedSpace_and_simplyConnectedSpace_of_universalCover_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.connectedSpace_and_simplyConnectedSpace_of_universalCover_product ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.connectedSpace_and_simplyConnectedSpace_of_universalCover_product

theorem metricComplete_of_universalCover_product
    (G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval)
    (Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M)
    (hconnected : ConnectedSpace F.M) (t : ℝ)
    (hprod : ∀ (y : G.M) (s : ℝ) (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) (w, c)) =
        (G.S.family.metric t).inner y v w + a * c)
    (hcomplete : MetricComplete (I := I) (F.atTime t)) :
    MetricComplete (I := 𝓡 2) (G.atTime t) := by
  let _ : TopologicalSpace G.M := G.topology
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
  let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
  let _ : IsManifold (𝓡 2) 1 G.M :=
    IsManifold.of_le (I := 𝓡 2) (M := G.M) (n := ∞) (by decide)
  let _ : T2Space G.M := G.t2
  let _ : SigmaCompactSpace G.M := G.sigmaCompact
  let _ : T2Space (TangentBundle (𝓡 2) G.M) := G.t2TangentBundle
  let _ : ConnectedSpace F.M := hconnected
  let _ : SigmaCompactSpace (UniversalCover F.M) :=
    Phi.toHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace
  have hliftBase : RiemannianMetricComplete (I := I) (F.S.family.metric t) := ⟨hcomplete⟩
  have hlift : RiemannianMetricComplete (I := I)
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)) :=
    UniversalCover.liftedMetric_complete (I := I) (F.S.family.metric t) hliftBase
  have heq : Diffeomorph.pullbackMetricCross
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)) Phi =
      (G.S.family.metric t).prod (euclideanMetric (E := ℝ)) := by
    apply SmoothRiemannianMetric.ext_inner
    intro z u v
    obtain ⟨y, s⟩ := z
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.prod_inner]
    change (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) u)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) v) =
      (G.S.family.metric t).inner y u.1 v.1 + _root_.Inner.inner ℝ (u.2 : ℝ) (v.2 : ℝ)
    rw [RCLike.inner_apply, conj_trivial, mul_comm]
    exact hprod y s u.1 v.1 (u.2 : ℝ) (v.2 : ℝ)
  have hc : RiemannianMetricComplete
      ((G.S.family.metric t).prod (euclideanMetric (E := ℝ))) := by
    rw [← heq]
    exact DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_pullbackMetricCross
      (J := I) hlift Phi
  have hfac : RiemannianMetricComplete (I := 𝓡 2) (G.S.family.metric t) :=
    (RiemannianMetricComplete.prod_iff.mp hc).1
  dsimp only [MetricComplete, PointedFlowData.atTime]
  exact hfac.complete

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricComplete_of_universalCover_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricComplete_of_universalCover_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricComplete_of_universalCover_product ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.metricComplete_of_universalCover_product

theorem ancient_fixed_universal_cover_product_of_negative_time_metric_product
    (G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval)
    (Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M)
    (hconnected : ConnectedSpace F.M)
    (hcompleteF : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hscalarG : ∀ t : ℝ, t < 0 → ∀ y : G.M, 0 < G.S.scalar t y)
    (hscalar0 : ∀ y : G.M, 0 < G.S.scalar 0 y)
    (hprod : ∀ t : ℝ, t < 0 → ∀ (y : G.M) (s : ℝ)
      (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (fun z : G.M × ℝ => Phi z) (y, s) (w, c)) =
        (G.S.family.metric t).inner y v w + a * c) :
    let _ : ConnectedSpace F.M := hconnected
    ∃ G' : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval,
      let _ : TopologicalSpace G'.M := G'.topology
      let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G'.M := G'.charted
      let _ : IsManifold (𝓡 2) ∞ G'.M := G'.smooth
      let _ : IsManifold (𝓡 2) 1 G'.M :=
        IsManifold.of_le (I := 𝓡 2) (M := G'.M) (n := ∞) (by decide)
      let _ : T2Space G'.M := G'.t2
      let _ : SigmaCompactSpace G'.M := G'.sigmaCompact
      ConnectedSpace G'.M ∧ SimplyConnectedSpace G'.M ∧
        (∀ t : ℝ, t ≤ 0 → MetricComplete (I := 𝓡 2) (G'.atTime t)) ∧
        (∀ t : ℝ, t ≤ 0 → ∀ y : G'.M, 0 < G'.S.scalar t y) ∧
        ∃ Phi' : (G'.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M,
          ∀ (t : ℝ), t ≤ 0 → ∀ (y : G'.M) (s : ℝ)
            (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
            (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi' (y, s))
                (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi' (y, s) (v, a))
                (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi' (y, s) (w, c)) =
              (G'.S.family.metric t).inner y v w + a * c := by
  have hpack :=
    connectedSpace_and_simplyConnectedSpace_of_universalCover_product F G Phi hconnected
  have hcompleteG : ∀ t : ℝ, t < 0 → MetricComplete (I := 𝓡 2) (G.atTime t) :=
    fun t ht => metricComplete_of_universalCover_product F G Phi hconnected t (hprod t ht)
      (hcompleteF t ht.le)
  exact ancient_fixed_universal_cover_product_of_negative_splitting
    F G Phi hconnected hcompleteF hpack.1 hpack.2 hcompleteG hscalarG hprod hscalar0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_fixed_universal_cover_product_of_negative_time_metric_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_fixed_universal_cover_product_of_negative_time_metric_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_fixed_universal_cover_product_of_negative_time_metric_product ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_fixed_universal_cover_product_of_negative_time_metric_product

theorem splitSurface_scalar_pos_at_zero_of_negative_product
    (hdim : Module.finrank ℝ E = 3)
    (G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval)
    (Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hcurvature : ∀ t : ℝ, t ≤ 0 → PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (hbounded : ∀ a b : ℝ, a < b → b ≤ 0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        F.rmNormSq (I := I) t x ≤ C)
    (hscalar : ∀ t : ℝ, t < 0 → ∀ y : G.M, 0 < G.S.scalar t y)
    (hproduct : ∀ t : ℝ, t < 0 → ∀ (y : G.M) (s : ℝ)
      (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
      (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (v, a))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (w, c)) =
        (G.S.family.metric t).inner y v w + a * c) :
    ∀ y : G.M, 0 < G.S.scalar 0 y := by
  let _ : T2Space (TangentBundle I F.M) := F.t2TangentBundle
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let _ : TopologicalSpace G.M := G.topology
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
  let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
  let _ : T2Space G.M := G.t2
  have hcomplete' : ∀ t ∈ ancientTimeInterval.regular,
      RiemannianMetricComplete (I := I) (F.S.base.metric t) := by
    intro t ht
    exact ⟨hcomplete t (le_of_lt (by simpa using ht))⟩
  have hbounded' : ∀ a b : ℝ, Set.Icc a b ⊆ ancientTimeInterval.regular →
      ∃ C : ℝ, ∀ t ∈ Set.Icc a b, ∀ x : F.M,
        DifferentialGeometry.Tensor0SBundle.normSq0S (I := I)
          (F.S.base.metric t) x 4 (F.S.base.rm04 t x) ≤ C := by
    intro a b hab
    by_cases hle : a ≤ b
    · have hb : b < 0 := by simpa using hab (Set.mem_Icc.mpr ⟨hle, le_rfl⟩)
      obtain ⟨C, _, hC⟩ := hbounded (a - 1) b (by linarith) hb.le
      refine ⟨C, ?_⟩
      intro t ht x
      exact hC t ⟨by linarith [ht.1], ht.2⟩ x
    · exact ⟨0, fun t ht => False.elim (hle (ht.1.trans ht.2))⟩
  have hcone : ∀ t ∈ ancientTimeInterval.regular, ∀ x : F.M,
      metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    intro t ht x
    exact pointedFlow_metricAlgebraicCurvatureTensorAt_mem_nonnegativeCone F hcurvature t
      (le_of_lt (by simpa using ht)) x
  have hprod0 := universalCover_product_inner_at_zero_of_negative_times F G Phi hproduct
  intro y
  have hle := hamilton_ancient_scalar_le_terminal F.S F.isSolution hcomplete' hbounded'
    hcone (t := (-1 : ℝ)) (b := 0) (by norm_num) (by simp)
    (by intro t ht; simpa using ht) (UniversalCover.proj (Phi (y, 0)))
  have hm := universalCover_product_scalar_eq (F.S.family.metric (-1))
    (G.S.family.metric (-1)) Phi (hproduct (-1) (by norm_num)) y 0
  have hz := universalCover_product_scalar_eq (F.S.family.metric 0)
    (G.S.family.metric 0) Phi hprod0 y 0
  change F.S.scalar (-1) (UniversalCover.proj (Phi (y, 0))) = G.S.scalar (-1) y at hm
  change F.S.scalar 0 (UniversalCover.proj (Phi (y, 0))) = G.S.scalar 0 y at hz
  rw [hm, hz] at hle
  exact (hscalar (-1) (by norm_num) y).trans_le hle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_scalar_pos_at_zero_of_negative_product then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_scalar_pos_at_zero_of_negative_product"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_scalar_pos_at_zero_of_negative_product ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_scalar_pos_at_zero_of_negative_product

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
