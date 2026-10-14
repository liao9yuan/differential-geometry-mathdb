import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Compact
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.CanonicalMetricCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

local instance globalizedMetricLimitTopology : TopologicalSpace L.M := L.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitTopology
local instance globalizedMetricLimitCharted : ChartedSpace H L.M := L.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitCharted
local instance globalizedMetricLimitSmooth : IsManifold I ∞ L.M := L.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitSmooth
local instance globalizedMetricLimitT2 : T2Space L.M := L.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitT2
local instance globalizedMetricLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricLimitSigma

local instance globalizedMetricApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxTopology
local instance globalizedMetricApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxCharted
local instance globalizedMetricApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxSmooth
local instance globalizedMetricApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxT2
local instance globalizedMetricApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricApproxSigma

local instance globalizedMetricSourceTopology (k : ℕ) :
    TopologicalSpace (MetricSourceDomain (I := I) Phi k) := metricSourceDomainTopology Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceTopology
local instance globalizedMetricSourceCharted (k : ℕ) :
    ChartedSpace H (MetricSourceDomain (I := I) Phi k) := metricSourceDomainChartedSpace Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceCharted
local instance globalizedMetricSourceSmooth (k : ℕ) :
    IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := metric_source_domain_smooth Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceSmooth
local instance globalizedMetricSourceT2 (k : ℕ) :
    T2Space (MetricSourceDomain (I := I) Phi k) := metric_source_domain_t2 Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceT2
local instance globalizedMetricSourceSigma (k : ℕ) :
    SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
  metric_source_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_source Phi k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricSourceSigma

local instance globalizedMetricTargetTopology (k : ℕ) :
    TopologicalSpace (MetricTargetDomain (I := I) Phi k) := metricTargetDomainTopology Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricTargetTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricTargetTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricTargetTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricTargetTopology
local instance globalizedMetricTargetCharted (k : ℕ) :
    ChartedSpace H (MetricTargetDomain (I := I) Phi k) := metricTargetDomainChartedSpace Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricTargetCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricTargetCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricTargetCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricTargetCharted
local instance globalizedMetricTargetSmooth (k : ℕ) :
    IsManifold I ∞ (MetricTargetDomain (I := I) Phi k) := metric_target_domain_smooth Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricTargetSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricTargetSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricTargetSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricTargetSmooth
local instance globalizedMetricTargetT2 (k : ℕ) :
    T2Space (MetricTargetDomain (I := I) Phi k) := metric_target_domain_t2 Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricTargetT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricTargetT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricTargetT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetricTargetT2

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem canonicalSource_pullback_eq_global_restrict (k : ℕ)
    (e : Diffeomorph I I L.M (X.obj (subseq k)).M (∞ : WithTop ℕ∞))
    (he : ∀ x : L.M, e x = Phi.map k x) :
    (canonicalSourceData Phi k).pullbackMetric =
      (Diffeomorph.pullbackMetric (I := I) (X.obj (subseq k)).metric e).restrictOpen
        (I := I) (metricSourceOpenSubset Phi k) := by
  change Diffeomorph.pullbackMetric (I := I)
      ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
      (metricSourceTargetDiffeomorph Phi k) =
    (Diffeomorph.pullbackMetric (I := I) (X.obj (subseq k)).metric e).restrictOpen
      (I := I) (metricSourceOpenSubset Phi k)
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  change
    (Diffeomorph.pullbackMetric (I := I)
      ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
      (metricSourceTargetDiffeomorph Phi k)).inner x v w =
      (Diffeomorph.pullbackMetric (I := I) (X.obj (subseq k)).metric e).inner
        (x : L.M) v w
  with_unfolding_all
    erw [Diffeomorph.pullbackMetric_inner, Diffeomorph.pullbackMetric_inner]
    change (X.obj (subseq k)).metric.inner
        ((metricSourceTargetDiffeomorph Phi k x : MetricTargetDomain (I := I) Phi k) :
          (X.obj (subseq k)).M)
        (mfderiv I I (metricSourceTargetDiffeomorph Phi k) x v)
        (mfderiv I I (metricSourceTargetDiffeomorph Phi k) x w) =
      (X.obj (subseq k)).metric.inner (e (x : L.M))
        (mfderiv I I e (x : L.M) v) (mfderiv I I e (x : L.M) w)
    simp only [metric_source_target_diffeomorph_mfderiv]
    have hef : (e : L.M → (X.obj (subseq k)).M) = Phi.map k := funext he
    rw [hef]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalSource_pullback_eq_global_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalSource_pullback_eq_global_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalSource_pullback_eq_global_restrict ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalSource_pullback_eq_global_restrict

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] in
private theorem globalizedMetric_sourceCompact_image (k : ℕ) (K : Set L.M)
    (hKsource : K ⊆ Phi.source k) :
    (Subtype.val : MetricSourceDomain (I := I) Phi k → L.M) ''
      metricSourceCompactSet (I := I) Phi k K = K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hKsource hx⟩, hx, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetric_sourceCompact_image
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.globalizedMetric_sourceCompact_image target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem canonicalSource_sup_eq_global_pullback (k : ℕ)
    (e : Diffeomorph I I L.M (X.obj (subseq k)).M (∞ : WithTop ℕ∞))
    (he : ∀ x : L.M, e x = Phi.map k x)
    (K : Set L.M) (p : ℕ) (hKsource : K ⊆ Phi.source k) :
    (canonicalSourceData Phi k).derivNormSupOn (I := I) K p =
      metricDerivNormSupOn (I := I) K p
        (Diffeomorph.pullbackMetric (I := I) (X.obj (subseq k)).metric e)
        L.metric L.metric := by
  change metricDerivNormSupOn (I := I) (metricSourceCompactSet (I := I) Phi k K) p
      (Diffeomorph.pullbackMetric (I := I)
        ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
        (metricSourceTargetDiffeomorph Phi k))
      (L.metric.restrictOpen (I := I) (metricSourceOpenSubset Phi k))
      (L.metric.restrictOpen (I := I) (metricSourceOpenSubset Phi k)) = _
  have hpb : Diffeomorph.pullbackMetric (I := I)
      ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
      (metricSourceTargetDiffeomorph Phi k) =
      (Diffeomorph.pullbackMetric (I := I) (X.obj (subseq k)).metric e).restrictOpen
        (I := I) (metricSourceOpenSubset Phi k) :=
    canonicalSource_pullback_eq_global_restrict Phi k e he
  rw [hpb,
    metricDerivNormSupOn_restrictOpen,
    globalizedMetric_sourceCompact_image Phi k K hKsource]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalSource_sup_eq_global_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalSource_sup_eq_global_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalSource_sup_eq_global_pullback ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalSource_sup_eq_global_pullback

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem compactLimit_global_pullback_metric_convergence
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k : ℕ, C.domain k = canonicalSourceData Phi k)
    (hcompact : CompactSpace L.M)
    (hconnected : ∀ k : ℕ, ConnectedSpace (X.obj (subseq k)).M) :
    ∃ k0 : ℕ,
      ∃ e : ∀ k : ℕ,
        Diffeomorph I I L.M (X.obj (subseq (k0 + k))).M (∞ : WithTop ℕ∞),
        (∀ k : ℕ, Phi.source (k0 + k) = Set.univ ∧
          Phi.target (k0 + k) = Set.univ ∧
          (∀ x : L.M, e k x = Phi.map (k0 + k) x) ∧
          (∀ y, (e k).symm y = (Phi.partialDiffeomorph (k0 + k)).symm y) ∧
          e k L.basepoint = (X.obj (subseq (k0 + k))).basepoint ∧
          CompactSpace (X.obj (subseq (k0 + k))).M) ∧
        MetricCInfConvergenceOnCompacts (I := I)
          (fun k => Diffeomorph.pullbackMetric (I := I)
            (X.obj (subseq (k0 + k))).metric (e k)) L.metric L.metric := by
  classical
  obtain ⟨k0, hk0⟩ := compactLimit_eventually_globalizes Phi hcompact hconnected
  have hex (k : ℕ) :
      ∃ e : Diffeomorph I I L.M (X.obj (subseq (k0 + k))).M (∞ : WithTop ℕ∞),
        (∀ x : L.M, e x = Phi.map (k0 + k) x) ∧
        (∀ y, e.symm y = (Phi.partialDiffeomorph (k0 + k)).symm y) ∧
        e L.basepoint = (X.obj (subseq (k0 + k))).basepoint ∧
        CompactSpace (X.obj (subseq (k0 + k))).M :=
    (hk0 (k0 + k) (by omega)).2.2
  choose e he hinverse hbase hcompactApprox using hex
  refine ⟨k0, e, ?_, ?_⟩
  · intro k
    exact ⟨(hk0 (k0 + k) (by omega)).1, (hk0 (k0 + k) (by omega)).2.1,
      he k, hinverse k, hbase k, hcompactApprox k⟩
  · intro K hK p eps heps
    obtain ⟨k1, hk1⟩ := C.converges K hK p eps heps
    refine ⟨k1, fun k hk => ?_⟩
    have hc := hk1 (k0 + k) (by omega)
    have hs : (canonicalSourceData Phi (k0 + k)).derivNormSupOn (I := I) K p < eps := by
      rw [← hcanonical (k0 + k)]
      exact hc.2
    rw [canonicalSource_sup_eq_global_pullback Phi (k0 + k) (e k) (he k) K p hc.1] at hs
    exact hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.compactLimit_global_pullback_metric_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.compactLimit_global_pullback_metric_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.compactLimit_global_pullback_metric_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.compactLimit_global_pullback_metric_convergence

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
