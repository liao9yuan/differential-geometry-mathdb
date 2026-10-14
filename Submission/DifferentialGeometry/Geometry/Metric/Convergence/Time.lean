import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.CheegerGromovCompactness
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem metric_cp_convergence_at_tendsto_time
    (K : Set M) (p : ℕ) (J : Set ℝ)
    (g : ℕ → ℝ → SmoothRiemannianMetric I M)
    (G : ℝ → SmoothRiemannianMetric I M) (R : SmoothRiemannianMetric I M)
    (time : ℕ → ℝ) {s L : ℝ}
    (htime : ∀ n, time n ∈ J) (hlim : _root_.Filter.Tendsto time _root_.Filter.atTop (𝓝 s))
    (hconv : ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ n ≥ N,
      ∀ t ∈ J, ∀ j ≤ p, ∀ x ∈ K, metricDerivNorm j (g n t) (G t) R x < epsilon)
    (hcontinuous : ∀ t ∈ J, ∀ j ≤ p, ∀ x ∈ K,
      metricDerivNorm j (G t) (G s) R x ≤ L * |t - s|) :
    MetricCPConvergenceOn K p (fun n => g n (time n)) (G s) R := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hconv (epsilon / 3) (by positivity)
  have hzero : _root_.Filter.Tendsto (fun n => L * |time n - s|) _root_.Filter.atTop (𝓝 0) := by
    simpa using (hlim.sub_const s).abs.const_mul L
  obtain ⟨N', hN'⟩ := eventually_atTop.mp
    (hzero.eventually (Iio_mem_nhds (show (0 : ℝ) < epsilon / 3 by positivity)))
  refine ⟨max N N', fun n hn => ?_⟩
  apply lt_of_le_of_lt
    (metricDerivNormSupOn_le_of_forall K p (g n (time n)) (G s) R
      (2 * epsilon / 3) (by positivity) ?_) (by linarith)
  intro j hj x hx
  have hg := hN n ((le_max_left _ _).trans hn) (time n) (htime n) j hj x hx
  have hG := (hcontinuous (time n) (htime n) j hj x hx).trans_lt
    (hN' n ((le_max_right _ _).trans hn))
  have htri := metricDerivNorm_triangle j (g n (time n)) (G (time n)) (G s) R x
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metric_cp_convergence_at_tendsto_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metric_cp_convergence_at_tendsto_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metric_cp_convergence_at_tendsto_time ``Submission.DifferentialGeometry.CheegerGromovCompactness.metric_cp_convergence_at_tendsto_time

end DifferentialGeometry.CheegerGromovCompactness
