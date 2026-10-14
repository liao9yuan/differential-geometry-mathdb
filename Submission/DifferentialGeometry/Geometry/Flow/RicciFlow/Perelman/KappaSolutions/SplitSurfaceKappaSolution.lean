import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SplitSurfaceAncientGeometry
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalCoverSplitNoncollapse

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Topology
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
  (G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval)

local instance splitSurfaceKappaBaseTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseTopology
local instance splitSurfaceKappaBaseCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseCharted
local instance splitSurfaceKappaBaseSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseSmooth
local instance splitSurfaceKappaBaseC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseC1
local instance splitSurfaceKappaBaseT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseT2
local instance splitSurfaceKappaBaseSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseSigma
local instance splitSurfaceKappaBaseInhabited : Inhabited F.M := ⟨F.basepoint⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseInhabited then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseInhabited"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseInhabited ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseInhabited
local instance splitSurfaceKappaBaseLocallyPathConnected : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseLocallyPathConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseLocallyPathConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseLocallyPathConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseLocallyPathConnected
local instance splitSurfaceKappaBaseSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseSemilocallySimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseSemilocallySimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseSemilocallySimplyConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseSemilocallySimplyConnected
local instance splitSurfaceKappaBaseMeasurable : MeasurableSpace F.M := borel F.M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseMeasurable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseMeasurable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseMeasurable ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseMeasurable
local instance splitSurfaceKappaBaseBorel : BorelSpace F.M := ⟨rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseBorel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseBorel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseBorel ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaBaseBorel

local instance splitSurfaceKappaSurfaceTopology : TopologicalSpace G.M := G.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceTopology
local instance splitSurfaceKappaSurfaceCharted :
    ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceCharted
local instance splitSurfaceKappaSurfaceSmooth : IsManifold (𝓡 2) ∞ G.M := G.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceSmooth
local instance splitSurfaceKappaSurfaceC1 : IsManifold (𝓡 2) 1 G.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceC1
local instance splitSurfaceKappaSurfaceT2 : T2Space G.M := G.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceT2
local instance splitSurfaceKappaSurfaceSigma : SigmaCompactSpace G.M := G.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceSigma
local instance splitSurfaceKappaSurfaceMeasurable : MeasurableSpace G.M := borel G.M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceMeasurable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceMeasurable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceMeasurable ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceMeasurable
local instance splitSurfaceKappaSurfaceBorel : BorelSpace G.M := ⟨rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceBorel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceBorel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceBorel ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurfaceKappaSurfaceBorel

variable (Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M)
  (hproduct : ∀ t : ℝ, t ≤ 0 → ∀ (y : G.M) (s : ℝ)
    (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
    (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (v, a))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (w, c)) =
      (G.S.family.metric t).inner y v w + a * c)

include hproduct

theorem splitSurface_noncollapsed_all_scales {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3) :
    PointedFlowNoncollapsedAllScales (I := 𝓡 2) G (kappa / 2) := by
  let _ : ConnectedSpace F.M := hF.connected
  intro time B hRm
  refine ⟨div_pos hF.kappa_pos (by norm_num), ?_⟩
  have hbase : ∀ (p : F.M) (rho : ℝ), 0 < rho →
      (∀ z ∈ riemannianBallOf (I := I) (F.S.family.metric (time : ℝ)) p rho,
        rho ^ 4 * normSq0S (I := I) (F.S.family.metric (time : ℝ)) z 4
          (metricRm04At (I := I) (F.S.family.metric (time : ℝ)) z) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal rho ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure (I := I) (M := F.M) (F.S.family.metric (time : ℝ))
          (riemannianBallOf (I := I) (F.S.family.metric (time : ℝ)) p rho) := by
    intro p rho hrho hcurvature
    let B0 : FlowMetricBall (I := I) (M := F.M) F.S time := ⟨p, rho, hrho⟩
    have hB0 : B0.IsSpatiallyRmControlled := by
      intro z hz
      simpa only [B0, FlowMetricBall.rmNormSq, SolutionFamily.rm04,
        metricRm04_apply, SolutionOn.family] using hcurvature z hz
    have hvolume := (hF.noncollapsed time B0 hB0).2
    change ENNReal.ofReal kappa * ENNReal.ofReal rho ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure (I := I) (M := F.M) (F.S.family.metric (time : ℝ))
        (riemannianBallOf (I := I) (F.S.family.metric (time : ℝ)) p rho) at hvolume
    exact hvolume
  have hsurface :
      ∀ z ∈ riemannianBallOf (I := 𝓡 2) (G.S.family.metric (time : ℝ))
        B.center B.radius,
      B.radius ^ 4 * normSq0S (I := 𝓡 2) (G.S.family.metric (time : ℝ)) z 4
        (metricRm04At (I := 𝓡 2) (G.S.family.metric (time : ℝ)) z) ≤ 1 := by
    intro z hz
    simpa only [FlowMetricBall.rmNormSq, SolutionFamily.rm04,
      metricRm04_apply, SolutionOn.family] using hRm z hz
  have ht : (time : ℝ) ≤ 0 := by simpa using time.property
  have hvolume := universalCover_split_surface_tensor_half_noncollapsed
    (F.S.family.metric (time : ℝ)) hdim (G.S.family.metric (time : ℝ))
    Phi (hproduct (time : ℝ) ht) kappa hF.kappa_pos.le hbase
    B.center B.radius B.radius_pos hsurface
  change ENNReal.ofReal (kappa / 2) * ENNReal.ofReal B.radius ^
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) ≤
    riemannianVolumeMeasure (I := 𝓡 2) (M := G.M) (G.S.family.metric (time : ℝ))
      (riemannianBallOf (I := 𝓡 2) (G.S.family.metric (time : ℝ)) B.center B.radius)
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using hvolume

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_noncollapsed_all_scales then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_noncollapsed_all_scales"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_noncollapsed_all_scales ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_noncollapsed_all_scales

theorem splitSurface_toIsAncientKappaSolution {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hconnectedG : ConnectedSpace G.M)
    (hcompleteG : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := 𝓡 2) (G.atTime t))
    (hpositiveG : ∀ t : ℝ, t ≤ 0 → ∀ y : G.M, 0 < G.S.scalar t y) :
    IsAncientKappaSolution (I := 𝓡 2) (kappa / 2) G := by
  obtain ⟨C, _, hsign, hscalar, _, hnotFlat⟩ :=
    splitSurface_ancient_geometry F G Phi hproduct hF hdim hpositiveG
  exact
    { kappa_pos := div_pos hF.kappa_pos (by norm_num)
      carrier_eq := rfl
      regular_eq := rfl
      connected := hconnectedG
      complete := fun t ht => hcompleteG t (by simpa using ht)
      nonnegativeCurvatureOperator := fun t ht => hsign t (by simpa using ht)
      globalScalarBound := ⟨C, hscalar⟩
      noncollapsed := splitSurface_noncollapsed_all_scales F G Phi hproduct hF hdim
      notFlat := hnotFlat }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_toIsAncientKappaSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_toIsAncientKappaSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_toIsAncientKappaSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.splitSurface_toIsAncientKappaSolution

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
