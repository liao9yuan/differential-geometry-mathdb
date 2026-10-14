import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.OpenTimeJetExtension
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessComparisonConstruction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [BoundarylessManifold I N]
  {M : ℕ → Type*} [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace ThreeSpace (M n)]
  [∀ n, IsManifold I3 ∞ (M n)]

theorem eventually_metricComparisonOn_of_local_flow_convergence
    (U : TopologicalSpace.Opens N) {D : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := U) D) (hS : ∀ n, IsSolutionOn (S n))
    (G : SolutionOn (I := I) (M := N) D) (hG : IsSolutionOn G)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = _root_.Set.Icc a b) (hregular : _root_.Set.Ioo a b ⊆ D.regular)
    (R : SmoothRiemannianMetric I U)
    (hconv : ∀ K : Set U, IsCompact K → ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc c b,
        metricDerivNormSupOn K r ((S n).base.metric t)
          ((G.base.metric t).restrictOpen U) R < epsilon)
    (g : ∀ n, ℝ → SmoothRiemannianMetric I3 (M n)) (F : ∀ n, N → M n)
    (hpair : ∀ n t, ∀ x : U, ∀ v w : TangentSpace I x,
      ((S n).base.metric t).inner x v w =
        (g n t).inner (F n x) (mfderiv I I3 (F n) (x : N) v) (mfderiv I I3 (F n) (x : N) w))
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (hJsub : J ⊆ _root_.Set.Icc c b)
    {K : Set N} (hK : IsCompact K) (hKU : K ⊆ U)
    (order : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n in _root_.Filter.atTop, Nonempty (MetricComparisonOn G.base.metric (g n) (F n)
      K J order epsilon) := by
  obtain ⟨B, C, hBzero, hCzero, hB, hC, hbound⟩ :=
    exists_metric_time_jets_extension_on_compact U S hS G hG hac hcb hcarrier hregular
      R hconv hK hKU
  have hclose : ∀ᶠ n in _root_.Filter.atTop, ∀ p q : Fin (order + 1), ∀ t ∈ _root_.Set.Icc c b, ∀ x ∈ K,
      tensor02CovDerivNormWith (p : ℕ) (B n (q : ℕ) t - C (q : ℕ) t)
        (G.base.metric t) (G.base.metric t) x ≤ epsilon := by
    rw [Filter.eventually_all]
    intro p
    rw [Filter.eventually_all]
    intro q
    exact eventually_atTop.mpr (hbound p q epsilon hepsilon)
  filter_upwards [hclose] with n hn
  refine ⟨metricComparisonOnOfGenuineTimeTowers G.base.metric (g n) (F n) K J
    hJ order epsilon (B n) C ?_ ?_ ?_ ?_ ?_⟩
  · intro t x hx v
    exact (hBzero n t x hx v).trans (hpair n t ⟨x, hKU hx⟩ (v 0) (v 1))
  · intro t x v
    rw [hCzero, metricTensorField_apply]
  · intro q t ht x _hx
    exact (hB n q t (hJsub ht) x).mono hJsub
  · intro q t ht x _hx
    exact (hC q t (hJsub ht) x).mono hJsub
  · intro p q hpq t ht x hx
    exact hn ⟨p, by omega⟩ ⟨q, by omega⟩ t (hJsub ht) x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metricComparisonOn_of_local_flow_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metricComparisonOn_of_local_flow_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metricComparisonOn_of_local_flow_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.eventually_metricComparisonOn_of_local_flow_convergence
end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
