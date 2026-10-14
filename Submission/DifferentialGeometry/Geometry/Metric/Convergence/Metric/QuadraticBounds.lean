import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem MetricCPConvergenceOn.eventually_quadratic_bounds
    {gSeq : ℕ → SmoothRiemannianMetric I M} {gInf gRef : SmoothRiemannianMetric I M}
    {K : Set M} (hconv : MetricCPConvergenceOn K 0 gSeq gInf gRef)
    (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in _root_.Filter.atTop, ∀ x ∈ K, ∀ v : TangentSpace I x,
      (1 - ε) * gInf.inner x v v ≤ (gSeq k).inner x v v ∧
      (gSeq k).inner x v v ≤ (1 + ε) * gInf.inner x v v := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := Nat.cast_nonneg _
  obtain ⟨C, hC, hcompare⟩ := equivOn_compact hK gInf gRef
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hnC : 0 ≤ n * C := mul_nonneg hn hC0
  obtain ⟨k₀, hk₀⟩ := hconv (ε / (n * C + 1)) (by positivity)
  filter_upwards [_root_.Filter.eventually_ge_atTop k₀] with k hk
  intro x hx v
  have hpoint := (derivNorm_le_sup hK (le_refl 0) (gSeq k) gInf gRef hx).trans_lt
    (hk₀ k hk)
  have hbound := metricQuadFormDiff_le_metricDerivNorm (gSeq k) gInf gRef x v
  change |(gSeq k).inner x v v - gInf.inner x v v| ≤
    n * metricDerivNorm 0 (gSeq k) gInf gRef x * gRef.inner x v v at hbound
  have hnn : 0 ≤ gInf.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (gInf.pos x v hv).le
  have hsmall : n * C * metricDerivNorm 0 (gSeq k) gInf gRef x ≤ ε := by
    calc
      _ ≤ n * C * (ε / (n * C + 1)) := mul_le_mul_of_nonneg_left hpoint.le hnC
      _ ≤ ε := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < n * C + 1)]
        nlinarith
  have hnorm0 : 0 ≤ metricDerivNorm 0 (gSeq k) gInf gRef x := Real.sqrt_nonneg _
  have hb : |(gSeq k).inner x v v - gInf.inner x v v| ≤ ε * gInf.inner x v v :=
    hbound.trans (calc
      _ ≤ n * metricDerivNorm 0 (gSeq k) gInf gRef x * (C * gInf.inner x v v) :=
        mul_le_mul_of_nonneg_left (hcompare x hx v).2 (mul_nonneg hn hnorm0)
      _ = (n * C * metricDerivNorm 0 (gSeq k) gInf gRef x) * gInf.inner x v v := by ring
      _ ≤ ε * gInf.inner x v v := mul_le_mul_of_nonneg_right hsmall hnn)
  have habs := abs_le.mp hb
  exact ⟨by nlinarith [habs.1], by nlinarith [habs.2]⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCPConvergenceOn
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCPConvergenceOn.eventually_quadratic_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCPConvergenceOn.eventually_quadratic_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCPConvergenceOn.eventually_quadratic_bounds ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCPConvergenceOn.eventually_quadratic_bounds

theorem MetricCInfConvergenceOnCompacts.eventually_quadratic_bounds
    {gSeq : ℕ → SmoothRiemannianMetric I M} {gInf gRef : SmoothRiemannianMetric I M}
    (hconv : MetricCInfConvergenceOnCompacts gSeq gInf gRef)
    {K : Set M} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in _root_.Filter.atTop, ∀ x ∈ K, ∀ v : TangentSpace I x,
      (1 - ε) * gInf.inner x v v ≤ (gSeq k).inner x v v ∧
      (gSeq k).inner x v v ≤ (1 + ε) * gInf.inner x v v :=
  (hconv K hK 0).eventually_quadratic_bounds hK hε

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.eventually_quadratic_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.eventually_quadratic_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.eventually_quadratic_bounds ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.eventually_quadratic_bounds

end DifferentialGeometry.CheegerGromovCompactness
