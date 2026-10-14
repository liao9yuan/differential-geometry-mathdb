import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.CovariantContinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.CovariantDerivative.Terminal

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_metric_covariant_derivative_bounds_from_terminal_values_of_local_solutions
    {c b : ℝ} (hcb : c < b) (gRef : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    (N : ℕ) (B : ℝ) (hB : 1 ≤ B) (K : ℝ) (hK : 0 ≤ K)
    (A : ℕ → ℝ) (hA : ∀ q, 0 ≤ A q) :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧
      ∀ (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M)
        (D : RealTimeInterval) (S : ℕ → SolutionOn (I := I) (M := U) D),
      (∀ i, IsSolutionOn (S i)) →
      (∀ i t, (S i).family.metric t = (gSeq i t).restrictOpen U) →
      (_root_.Set.Icc c b ⊆ D.carrier) → (_root_.Set.Ico c b ⊆ D.regular) →
      (∀ i, ∀ t ∈ _root_.Set.Icc c b, MetricUniformEquivalentOn U gRef (gSeq i t) B) →
      MovingShiBoundOn U c b gSeq N K →
      (∀ q, 1 ≤ q → q ≤ N → ∀ i, ∀ x ∈ U,
        metricCovDerivNorm q (gSeq i b) gRef x ≤ A q) →
      ∀ q, 1 ≤ q → q ≤ N → ∀ i, ∀ t ∈ _root_.Set.Icc c b, ∀ x ∈ U,
        metricCovDerivNorm q (gSeq i t) gRef x ≤ C q := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨C, hC, hbound⟩ :=
    exists_metric_covariant_derivative_bounds_from_terminal_values_of_evolution
      (c := c) (b := b) gRef U U.isOpen N B hB K hK A hA
  refine ⟨C, hC, ?_⟩
  intro gSeq D S hS hmet hslab hreg hequiv hShi hinit
  apply hbound gSeq hequiv hShi hinit
  · intro q _ _ i x hx
    have hc := solution_metricCovDerivNorm_continuousOn_closed_interval
      (S i) (hS i) hcb hslab hreg (gRef.restrictOpen U) q ⟨x, hx⟩
    have heq : (fun t => metricCovDerivNorm q ((S i).base.metric t)
        (gRef.restrictOpen U) ⟨x, hx⟩) =
        (fun t => metricCovDerivNorm q (gSeq i t) gRef x) := by
      funext t
      change metricCovDerivNorm q ((S i).family.metric t)
        (gRef.restrictOpen U) ⟨x, hx⟩ = _
      rw [hmet i t, covNorm_restrictOpen]
    rwa [heq] at hc
  · intro q _ _ i x hx t ht v
    exact Perelman.KappaSolutions.metricCovDeriv_hasDerivAt_of_local_solution
      (gSeq i) gRef U (S i) (hS i) (hmet i) q
      (hreg (_root_.Set.Ioo_subset_Ico_self ht)) ⟨x, hx⟩ v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_metric_covariant_derivative_bounds_from_terminal_values_of_local_solutions then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_metric_covariant_derivative_bounds_from_terminal_values_of_local_solutions"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_metric_covariant_derivative_bounds_from_terminal_values_of_local_solutions ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_metric_covariant_derivative_bounds_from_terminal_values_of_local_solutions

end DifferentialGeometry.PDE.RicciFlow
