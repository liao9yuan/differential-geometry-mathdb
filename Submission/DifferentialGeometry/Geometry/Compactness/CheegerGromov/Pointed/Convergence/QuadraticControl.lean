import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Defs
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.MetricSource
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {subseq : ℕ → ℕ} {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}

local instance pointedControlTopology : TopologicalSpace L.M := L.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlTopology
local instance pointedControlCharted : ChartedSpace H L.M := L.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlCharted
local instance pointedControlSmooth : IsManifold I ∞ L.M := L.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlSmooth
local instance pointedControlT2 : T2Space L.M := L.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlT2
local instance pointedControlSigmaCompact : SigmaCompactSpace L.M := L.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlSigmaCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlSigmaCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlSigmaCompact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedControlSigmaCompact

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_pointed_quadratic_control
    (C : MetricConvergenceData (I := I) Φ)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (K : Set L.M) (hK : IsCompact K) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → K ⊆ Φ.source k ∧
      (let _ : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := (C.domain k).topology
       let _ : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := (C.domain k).charted
       let _ : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := (C.domain k).smooth
       ∀ x : MetricSourceDomain (I := I) Φ k, (x : L.M) ∈ K →
         ∀ v : TangentSpace I x,
           |(C.domain k).pullbackMetric.inner x v v - (C.domain k).limitMetric.inner x v v| ≤
             epsilon * (C.domain k).limitMetric.inner x v v) := by
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := by dsimp only [n]; positivity
  have htol : 0 < epsilon / (n + 1) := div_pos hepsilon (by linarith)
  obtain ⟨k0, hk0⟩ := C.converges K hK 0 (epsilon / (n + 1)) htol
  refine ⟨k0, fun k hk => ?_⟩
  obtain ⟨hsource, hsup⟩ := hk0 k hk
  refine ⟨hsource, ?_⟩
  let _ : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := (C.domain k).topology
  let _ : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := (C.domain k).charted
  let _ : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := (C.domain k).smooth
  let _ : T2Space (MetricSourceDomain (I := I) Φ k) := (C.domain k).t2
  let _ : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := (C.domain k).sigmaCompact
  dsimp only
  intro x hx v
  have hcompact : IsCompact (metricSourceCompactSet (I := I) Φ k K) :=
    (C.domain k).compact_preimage K hK hsource
  have hpoint := derivNorm_le_sup (I := I) hcompact (a := 0) (p := 0) le_rfl
    (C.domain k).pullbackMetric (C.domain k).limitMetric (C.domain k).referenceMetric
    (x := x) hx
  have hsmall : metricDerivNorm (I := I) 0 (C.domain k).pullbackMetric
      (C.domain k).limitMetric (C.domain k).referenceMetric x ≤ epsilon / (n + 1) :=
    hpoint.trans hsup.le
  rw [hreference k] at hsmall
  have hcoef : n * metricDerivNorm (I := I) 0 (C.domain k).pullbackMetric
      (C.domain k).limitMetric (C.domain k).limitMetric x ≤ epsilon := by
    calc
      _ ≤ n * (epsilon / (n + 1)) := mul_le_mul_of_nonneg_left hsmall hn
      _ ≤ epsilon := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by linarith : 0 < n + 1)).2
        nlinarith [hepsilon.le]
  have hquad := metricQuadFormDiff_le_metricDerivNorm (I := I)
    (C.domain k).pullbackMetric (C.domain k).limitMetric (C.domain k).limitMetric x v
  have hnonneg : 0 ≤ (C.domain k).limitMetric.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ((C.domain k).limitMetric.pos x v hv).le
  exact hquad.trans (mul_le_mul_of_nonneg_right hcoef hnonneg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_quadratic_control then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_quadratic_control"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_quadratic_control ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_quadratic_control

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_pointed_ambient_quadratic_control
    (C : MetricConvergenceData (I := I) Φ)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (K : Set L.M) (hK : IsCompact K) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → K ⊆ Φ.source k ∧
      (let _ : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := (C.domain k).topology
       let _ : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := (C.domain k).charted
       let _ : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := (C.domain k).smooth
       let _ : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
       let _ : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
       let _ : IsManifold I ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth
       ∀ x : MetricSourceDomain (I := I) Φ k, (x : L.M) ∈ K →
         ∀ v : TangentSpace I x,
           |(X.obj (subseq k)).metric.inner (Φ.map k (x : L.M))
               (mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k =>
                 Φ.map k (y : L.M)) x v)
               (mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k =>
                 Φ.map k (y : L.M)) x v) -
             L.metric.inner (x : L.M)
               (mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x v)
               (mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x v)| ≤
             epsilon * L.metric.inner (x : L.M)
               (mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x v)
               (mfderiv I I (fun y : MetricSourceDomain (I := I) Φ k => (y : L.M)) x v)) := by
  obtain ⟨k0, hk0⟩ := exists_pointed_quadratic_control C hreference K hK epsilon hepsilon
  refine ⟨k0, fun k hk => ⟨(hk0 k hk).1, ?_⟩⟩
  let _ : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := (C.domain k).topology
  let _ : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := (C.domain k).charted
  let _ : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := (C.domain k).smooth
  let _ : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
  let _ : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
  let _ : IsManifold I ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth
  let _ : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
  let _ : SigmaCompactSpace (X.obj (subseq k)).M := (X.obj (subseq k)).sigmaCompact
  dsimp only
  intro x hx v
  have h := (hk0 k hk).2 x hx v
  simpa only [(C.domain k).pullback_inner, (C.domain k).limit_inner] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_ambient_quadratic_control then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_ambient_quadratic_control"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_ambient_quadratic_control ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_ambient_quadratic_control

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
