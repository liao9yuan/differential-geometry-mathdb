import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MetricRicciDifference
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Topology _root_.Submission.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

local instance pointedRicciManifoldOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] : IsManifold I 1 P :=
  IsManifold.of_le (I := I) (M := P) (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciManifoldOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciManifoldOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciManifoldOne ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciManifoldOne

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

local instance pointedRicciLimitTopology : TopologicalSpace L.M := L.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitTopology
local instance pointedRicciLimitCharted : ChartedSpace H L.M := L.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitCharted
local instance pointedRicciLimitSmooth : IsManifold I ∞ L.M := L.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitSmooth
local instance pointedRicciLimitT2 : T2Space L.M := L.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitT2
local instance pointedRicciLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciLimitSigma

local instance pointedRicciApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxTopology
local instance pointedRicciApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxCharted
local instance pointedRicciApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxSmooth
local instance pointedRicciApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxT2
local instance pointedRicciApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciApproxSigma

local instance pointedRicciSourceTopology (k : ℕ) :
    TopologicalSpace (MetricSourceDomain (I := I) Phi k) := metricSourceDomainTopology Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceTopology
local instance pointedRicciSourceCharted (k : ℕ) :
    ChartedSpace H (MetricSourceDomain (I := I) Phi k) := metricSourceDomainChartedSpace Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceCharted
local instance pointedRicciSourceSmooth (k : ℕ) :
    IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := metric_source_domain_smooth Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceSmooth
local instance pointedRicciSourceT2 (k : ℕ) :
    T2Space (MetricSourceDomain (I := I) Phi k) := metric_source_domain_t2 Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceT2
local instance pointedRicciSourceSigma (k : ℕ) :
    SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
  metric_source_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_source Phi k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciSourceSigma

local instance pointedRicciTargetTopology (k : ℕ) :
    TopologicalSpace (MetricTargetDomain (I := I) Phi k) := metricTargetDomainTopology Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetTopology
local instance pointedRicciTargetCharted (k : ℕ) :
    ChartedSpace H (MetricTargetDomain (I := I) Phi k) := metricTargetDomainChartedSpace Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetCharted
local instance pointedRicciTargetSmooth (k : ℕ) :
    IsManifold I ∞ (MetricTargetDomain (I := I) Phi k) := metric_target_domain_smooth Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetSmooth
local instance pointedRicciTargetT2 (k : ℕ) :
    T2Space (MetricTargetDomain (I := I) Phi k) := metric_target_domain_t2 Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetT2
local instance pointedRicciTargetSigma (k : ℕ) :
    SigmaCompactSpace (MetricTargetDomain (I := I) Phi k) :=
  metric_target_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_target Phi k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicciTargetSigma

variable {Phi}

omit [CompleteSpace E] in
private theorem canonicalRicci_restrict (k : ℕ)
    (x : MetricSourceDomain (I := I) Phi k) (v : TangentSpace I x) :
    ricciTensor (I := I) (L.metric.restrictOpen (I := I) (metricSourceOpenSubset Phi k)) x v v =
      ricciTensor (I := I) L.metric (x : L.M) v v := by
  have h := DifferentialGeometry.CheegerGromovCompactness.ricciTensor_restrictOpen L.metric (metricSourceOpenSubset Phi k) x v v
  erw [mfderiv_subtype_val_apply] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalRicci_restrict
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalRicci_restrict target :: scope.openDecls } }

private theorem canonicalRicci_pullback (k : ℕ)
    (x : MetricSourceDomain (I := I) Phi k) (v : TangentSpace I x) :
    ricciTensor (I := I)
        (Diffeomorph.pullbackMetric (I := I)
          ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
          (metricSourceTargetDiffeomorph Phi k)) x v v =
      ricciTensor (I := I) (X.obj (subseq k)).metric (Phi.map k (x : L.M))
        (mfderiv I I (Phi.map k) (x : L.M) v)
        (mfderiv I I (Phi.map k) (x : L.M) v) := by
  rw [DifferentialGeometry.CheegerGromovCompactness.ricciTensor_pullback]
  erw [DifferentialGeometry.CheegerGromovCompactness.ricciTensor_restrictOpen (X.obj (subseq k)).metric
    (metricTargetOpenSubset Phi k) (metricSourceTargetDiffeomorph Phi k x)
    (mfderiv I I (metricSourceTargetDiffeomorph Phi k) x v)
    (mfderiv I I (metricSourceTargetDiffeomorph Phi k) x v)]
  erw [mfderiv_subtype_val_apply, metric_source_target_diffeomorph_apply,
    metric_source_target_diffeomorph_mfderiv (I := I) Phi k x v]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalRicci_pullback
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.canonicalRicci_pullback target :: scope.openDecls } }

theorem pointedRicci_tendsto_of_canonical_metric_convergence
    (hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Phi
        (CanonicalMetricCompactness.canonicalSourceData Phi) K 2)
    (x : L.M) (v : TangentSpace I x) :
    Tendsto (fun k => ricciTensor (I := I) (X.obj (subseq k)).metric (Phi.map k x)
      (mfderiv I I (Phi.map k) x v) (mfderiv I I (Phi.map k) x v))
      atTop (𝓝 (ricciTensor (I := I) L.metric x v v)) := by
  let n : ℝ := Module.finrank ℝ E
  let A : ℝ := n * 432 * L.metric.inner x v v
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hv : 0 ≤ L.metric.inner x v v :=
    DifferentialGeometry.metric_inner_self_nonneg L.metric x v
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  apply Metric.tendsto_atTop.mpr
  intro epsilon hepsilon
  let delta : ℝ := _root_.Min.min 1 (_root_.Min.min (1 / (2 * (n + 1))) (epsilon / (A + 1)))
  have hd0 : 0 < delta := by dsimp only [delta]; positivity
  have hd1 : delta ≤ 1 := min_le_left _ _
  have hdn : n * delta ≤ 1 / 2 := by
    have ht : delta ≤ 1 / (2 * (n + 1)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hm := (le_div_iff₀ (by positivity : 0 < 2 * (n + 1))).mp ht
    nlinarith [hd0.le]
  have hdA : A * delta < epsilon := by
    have ht : delta ≤ epsilon / (A + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hm := (le_div_iff₀ (by positivity : 0 < A + 1)).mp ht
    nlinarith
  obtain ⟨k0, hk0⟩ := hconv {x} isCompact_singleton delta hd0
  refine ⟨k0, fun k hk => ?_⟩
  obtain ⟨hsource, hsup⟩ := hk0 k hk
  let xu : MetricSourceDomain (I := I) Phi k := ⟨x, hsource (Set.mem_singleton x)⟩
  let gU := L.metric.restrictOpen (I := I) (metricSourceOpenSubset Phi k)
  let hU := Diffeomorph.pullbackMetric (I := I)
    ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
    (metricSourceTargetDiffeomorph Phi k)
  have hcompact : IsCompact (metricSourceCompactSet (I := I) Phi k {x}) :=
    metric_source_compact_set_is_compact (I := I) Phi k isCompact_singleton hsource
  change metricDerivNormSupOn (I := I)
    (metricSourceCompactSet (I := I) Phi k {x}) 2 hU gU gU < delta at hsup
  have hjet (a : ℕ) (ha : a ≤ 2) : metricDerivNorm (I := I) a hU gU gU xu ≤ delta := by
    have ht := derivNorm_le_sup (I := I) hcompact ha
      hU gU gU (x := xu) (Set.mem_singleton x)
    exact ht.trans hsup.le
  have hb := metricRicci_difference_le_relative_two_jets gU hU xu hd0.le hd1 hdn hjet v
  have hlim : ricciTensor (I := I) gU xu v v = ricciTensor (I := I) L.metric x v v :=
    canonicalRicci_restrict (Phi := Phi) k xu v
  have hpull : ricciTensor (I := I) hU xu v v =
      ricciTensor (I := I) (X.obj (subseq k)).metric (Phi.map k x)
        (mfderiv I I (Phi.map k) x v) (mfderiv I I (Phi.map k) x v) :=
    canonicalRicci_pullback (Phi := Phi) k xu v
  rw [hpull, hlim] at hb
  have hcoeff : (Module.finrank ℝ E : ℝ) * (432 * delta) * gU.inner xu v v =
      A * delta := by
    change n * (432 * delta) * L.metric.inner x v v =
      (n * 432 * L.metric.inner x v v) * delta
    ring
  rw [hcoeff] at hb
  rw [Real.dist_eq]
  exact hb.trans_lt hdA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicci_tendsto_of_canonical_metric_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicci_tendsto_of_canonical_metric_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicci_tendsto_of_canonical_metric_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicci_tendsto_of_canonical_metric_convergence

theorem pointedRicci_tendsto_of_metricCG_canonical_domains
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (x : L.M) (v : TangentSpace I x) :
    Tendsto (fun k => ricciTensor (I := I) (X.obj (subseq k)).metric (Phi.map k x)
      (mfderiv I I (Phi.map k) x v) (mfderiv I I (Phi.map k) x v))
      atTop (𝓝 (ricciTensor (I := I) L.metric x v v)) := by
  apply pointedRicci_tendsto_of_canonical_metric_convergence
  intro K hK
  have ht := C.converges K hK 2
  have hD : C.domain = CanonicalMetricCompactness.canonicalSourceData Phi := funext hcanonical
  rw [hD] at ht
  exact ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicci_tendsto_of_metricCG_canonical_domains then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicci_tendsto_of_metricCG_canonical_domains"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicci_tendsto_of_metricCG_canonical_domains ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedRicci_tendsto_of_metricCG_canonical_domains

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
