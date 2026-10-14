import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Inner

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

local instance pointedQuadraticManifoldOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] : IsManifold I 1 P :=
  IsManifold.of_le (I := I) (M := P) (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticManifoldOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticManifoldOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticManifoldOne ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticManifoldOne

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

local instance pointedQuadraticLimitTopology : TopologicalSpace L.M := L.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitTopology ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitTopology
local instance pointedQuadraticLimitCharted : ChartedSpace H L.M := L.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitCharted ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitCharted
local instance pointedQuadraticLimitSmooth : IsManifold I ∞ L.M := L.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitSmooth ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitSmooth
local instance pointedQuadraticLimitT2 : T2Space L.M := L.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitT2 ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitT2
local instance pointedQuadraticLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitSigma ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticLimitSigma

local instance pointedQuadraticApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxTopology ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxTopology
local instance pointedQuadraticApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxCharted ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxCharted
local instance pointedQuadraticApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxSmooth ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxSmooth
local instance pointedQuadraticApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxT2 ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxT2
local instance pointedQuadraticApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxSigma ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticApproxSigma

local instance pointedQuadraticSourceTopology (k : ℕ) :
    TopologicalSpace (MetricSourceDomain (I := I) Phi k) := metricSourceDomainTopology Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceTopology ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceTopology
local instance pointedQuadraticSourceCharted (k : ℕ) :
    ChartedSpace H (MetricSourceDomain (I := I) Phi k) := metricSourceDomainChartedSpace Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceCharted ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceCharted
local instance pointedQuadraticSourceSmooth (k : ℕ) :
    IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := metric_source_domain_smooth Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceSmooth ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceSmooth
local instance pointedQuadraticSourceT2 (k : ℕ) :
    T2Space (MetricSourceDomain (I := I) Phi k) := metric_source_domain_t2 Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceT2 ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceT2
local instance pointedQuadraticSourceSigma (k : ℕ) :
    SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
  metric_source_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_source Phi k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceSigma ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticSourceSigma

local instance pointedQuadraticTargetTopology (k : ℕ) :
    TopologicalSpace (MetricTargetDomain (I := I) Phi k) := metricTargetDomainTopology Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetTopology ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetTopology
local instance pointedQuadraticTargetCharted (k : ℕ) :
    ChartedSpace H (MetricTargetDomain (I := I) Phi k) := metricTargetDomainChartedSpace Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetCharted ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetCharted
local instance pointedQuadraticTargetSmooth (k : ℕ) :
    IsManifold I ∞ (MetricTargetDomain (I := I) Phi k) := metric_target_domain_smooth Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetSmooth ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetSmooth
local instance pointedQuadraticTargetT2 (k : ℕ) :
    T2Space (MetricTargetDomain (I := I) Phi k) := metric_target_domain_t2 Phi k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetT2 ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetT2
local instance pointedQuadraticTargetSigma (k : ℕ) :
    SigmaCompactSpace (MetricTargetDomain (I := I) Phi k) :=
  metric_target_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_target Phi k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetSigma ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedQuadraticTargetSigma

variable {Phi}

omit [I.Boundaryless] in
theorem pointed_metric_eventually_quadratic_bounds
    {K : Set L.M} (hK : IsCompact K)
    (hconv : metricSourceConvergesOn (I := I) Phi
      (CanonicalMetricCompactness.canonicalSourceData Phi) K 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ k in _root_.Filter.atTop, K ⊆ Phi.source k ∧ ∀ x ∈ K, ∀ v : TangentSpace I x,
      (1 - epsilon) * L.metric.inner x v v ≤
        (X.obj (subseq k)).metric.inner (Phi.map k x)
          (mfderiv I I (Phi.map k) x v) (mfderiv I I (Phi.map k) x v) ∧
      (X.obj (subseq k)).metric.inner (Phi.map k x)
          (mfderiv I I (Phi.map k) x v) (mfderiv I I (Phi.map k) x v) ≤
        (1 + epsilon) * L.metric.inner x v v := by
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := Nat.cast_nonneg _
  obtain ⟨k0, hk0⟩ := hconv (epsilon / (n + 1)) (by positivity)
  filter_upwards [_root_.Filter.eventually_ge_atTop k0] with k hk
  obtain ⟨hsource, hsup⟩ := hk0 k hk
  refine ⟨hsource, fun x hx v => ?_⟩
  let xu : MetricSourceDomain (I := I) Phi k := ⟨x, hsource hx⟩
  let gU := L.metric.restrictOpen (I := I) (metricSourceOpenSubset Phi k)
  let hU := Diffeomorph.pullbackMetric (I := I)
    ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
    (metricSourceTargetDiffeomorph Phi k)
  have hcompact : IsCompact (metricSourceCompactSet (I := I) Phi k K) :=
    metric_source_compact_set_is_compact (I := I) Phi k hK hsource
  change metricDerivNormSupOn (I := I)
    (metricSourceCompactSet (I := I) Phi k K) 0 hU gU gU < _ at hsup
  have hpoint := (derivNorm_le_sup (I := I) hcompact (le_refl 0)
    hU gU gU (x := xu) hx).trans_lt hsup
  have hbound := metricQuadFormDiff_le_metricDerivNorm (I := I) hU gU gU xu v
  have hpull : hU.inner xu v v = (X.obj (subseq k)).metric.inner (Phi.map k x)
      (mfderiv I I (Phi.map k) x v) (mfderiv I I (Phi.map k) x v) := by
    dsimp only [hU]
    erw [Diffeomorph.pullbackMetric_inner]
    change (X.obj (subseq k)).metric.inner _ _ _ = _
    erw [metric_source_target_diffeomorph_mfderiv]
    rfl
  change |hU.inner xu v v - L.metric.inner x v v| ≤
    n * metricDerivNorm (I := I) 0 hU gU gU xu * L.metric.inner x v v at hbound
  rw [hpull] at hbound
  have hnn : 0 ≤ L.metric.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (L.metric.pos x v hv).le
  have hsmall : n * metricDerivNorm (I := I) 0 hU gU gU xu ≤ epsilon := by
    calc
      _ ≤ n * (epsilon / (n + 1)) := mul_le_mul_of_nonneg_left hpoint.le hn
      _ ≤ epsilon := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < n + 1)]
        nlinarith
  have hb := hbound.trans (mul_le_mul_of_nonneg_right hsmall hnn)
  have hbs := abs_le.mp hb
  exact ⟨by nlinarith [hbs.1], by nlinarith [hbs.2]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointed_metric_eventually_quadratic_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointed_metric_eventually_quadratic_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointed_metric_eventually_quadratic_bounds ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointed_metric_eventually_quadratic_bounds

end DifferentialGeometry.CheegerGromovCompactness
end
