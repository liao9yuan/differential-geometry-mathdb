import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import Mathlib.Topology.Compactness.LocallyCompact
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Comparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
universe u uE uH
namespace DifferentialGeometry
namespace CheegerGromovCompactness
open scoped _root_.Manifold _root_.ContDiff
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M]

theorem MetricCPConvergenceOn.eventually_pairwise_metric_deriv_norm
    (G : Nat → SmoothRiemannianMetric I M)
    (gInf : SmoothRiemannianMetric I M)
    {K L : Set M} (hL : IsCompact L) (hKL : K ⊆ interior L)
    (p : Nat) (hconv : MetricCPConvergenceOn (I := I) L p G gInf gInf)
    {eps : Real} (heps : 0 < eps) :
    ∃ N : Nat, ∀ m : Nat, N ≤ m → ∀ l : Nat, N ≤ l →
      ∀ a : Nat, a ≤ p → ∀ x : M, x ∈ K →
        metricDerivNorm (I := I) a (G m) (G l) (G l) x < eps := by
  let : CompleteSpace E := FiniteDimensional.complete Real E
  obtain ⟨δ, hδpos, hδlt, hδdim, hδbudget⟩ :=
    exists_metric_reference_change_delta (E := E) p (show 0 < eps / 2 by positivity)
  obtain ⟨N, hN⟩ := hconv δ hδpos
  have hsmall : ∀ j : Nat, N ≤ j → ∀ y ∈ interior L, ∀ q : Nat, q ≤ p →
      metricDerivNorm (I := I) q (G j) gInf gInf y ≤ δ := by
    intro j hj y hy q hq
    exact ((derivNorm_le_sup (I := I) hL hq (G j) gInf gInf
      (interior_subset hy)).trans_lt (hN j hj)).le
  refine ⟨N, fun m hm l hl a ha x hx => ?_⟩
  have hchange := metric_deriv_norm_reference_change_le (I := I) isOpen_interior
    (G m) (G l) gInf p hδpos.le hδlt.le hδdim hδbudget
    (hsmall m hm) (hsmall l hl) x (hKL hx) a ha
  exact hchange.trans_lt (half_lt_self heps)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCPConvergenceOn
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCPConvergenceOn.eventually_pairwise_metric_deriv_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCPConvergenceOn.eventually_pairwise_metric_deriv_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCPConvergenceOn.eventually_pairwise_metric_deriv_norm ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCPConvergenceOn.eventually_pairwise_metric_deriv_norm

theorem MetricCInfConvergenceOnCompacts.eventually_pairwise_metric_deriv_norm
    (G : Nat → SmoothRiemannianMetric I M)
    (gInf : SmoothRiemannianMetric I M)
    (hconv : MetricCInfConvergenceOnCompacts (I := I) G gInf gInf)
    {K : Set M} (hK : IsCompact K) (p : Nat) {eps : Real} (heps : 0 < eps) :
    ∃ N : Nat, ∀ m : Nat, N ≤ m → ∀ l : Nat, N ≤ l →
      ∀ a : Nat, a ≤ p → ∀ x : M, x ∈ K →
        metricDerivNorm (I := I) a (G m) (G l) (G l) x < eps := by
  let : CompleteSpace E := FiniteDimensional.complete Real E
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨L, hL, hKL, _⟩ := exists_compact_between hK isOpen_univ (Set.subset_univ K)
  exact MetricCPConvergenceOn.eventually_pairwise_metric_deriv_norm G gInf hL hKL p
    (hconv L hL p) heps

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.eventually_pairwise_metric_deriv_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.eventually_pairwise_metric_deriv_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.eventually_pairwise_metric_deriv_norm ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCInfConvergenceOnCompacts.eventually_pairwise_metric_deriv_norm

end CheegerGromovCompactness
end DifferentialGeometry
