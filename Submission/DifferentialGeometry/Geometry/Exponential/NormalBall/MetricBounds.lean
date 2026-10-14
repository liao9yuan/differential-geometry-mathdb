import Submission.DifferentialGeometry.Geometry.Exponential.NormalBall.Identity
import Submission.DifferentialGeometry.Geometry.Exponential.NormalBall.Chart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

theorem exists_metricBounds_of_metricEquivOn
    (g : SmoothRiemannianMetric I M) {p : M} (c : NormalBallChart (I := I) p)
    {r r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀r : r₀ < r) (hr : r ≤ c.radius)
    (hell : c.MetricEquivOn g (Metric.ball (0 : E) r)) :
    ∃ b : c.MetricBounds g, b.radius = r₀ := by
  have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (c.metric g) (Metric.ball (0 : E) r) :=
    (c.metric_cont_diff_on g Metric.isOpen_ball c.smooth_to).mono
      (Metric.ball_subset_ball hr)
  have hderiv : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ Metric.closedBall (0 : E) r₀, ‖iteratedFDeriv ℝ q (c.metric g) z‖ ≤ C := by
    intro q
    have hcontOpen : ContinuousOn (iteratedFDeriv ℝ q (c.metric g)) (Metric.ball (0 : E) r) :=
      ContinuousOn.continuousOn_iteratedFDeriv hsmooth Metric.isOpen_ball (by exact_mod_cast le_top)
    have hcont : ContinuousOn (iteratedFDeriv ℝ q (c.metric g)) (Metric.closedBall (0 : E) r₀) :=
      hcontOpen.mono (Metric.closedBall_subset_ball hr₀r)
    obtain ⟨C, hC⟩ := (_root_.ProperSpace.isCompact_closedBall (0 : E) r₀).exists_bound_of_continuousOn hcont
    exact ⟨max C 0, le_max_right _ _, fun z hz => (hC z hz).trans (le_max_left _ _)⟩
  choose C hC hderiv using hderiv
  let b : c.MetricBounds g :=
    { C := C
      C_nonneg := hC
      radius := r₀
      radius_pos := hr₀
      equiv := fun z hz => hell z (Metric.ball_subset_ball hr₀r.le hz)
      deriv := fun q z hz => hderiv q z (Metric.ball_subset_closedBall hz) }
  exact ⟨b, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.exists_metricBounds_of_metricEquivOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.exists_metricBounds_of_metricEquivOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.exists_metricBounds_of_metricEquivOn ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.exists_metricBounds_of_metricEquivOn

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

end

noncomputable section
open _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

theorem exists_metricBounds_identity_of_inner_bounds [FiniteDimensional ℝ E]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    {rChart r r₀ : ℝ} (hrChart : 0 < rChart) (hr₀ : 0 < r₀)
    (hr₀r : r₀ < r) (hr : r ≤ rChart)
    (hbound : ∀ z ∈ Metric.ball (0 : E) r, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ g.inner z v v ∧ g.inner z v v ≤ 2 * ‖v‖ ^ 2) :
    ∃ b : (identity (E := E) hrChart).MetricBounds g, b.radius = r₀ := by
  apply exists_metricBounds_of_metricEquivOn g (identity hrChart) hr₀ hr₀r hr
  intro z hz v
  have hh := hbound z hz v
  rw [metric_identity]
  exact hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.exists_metricBounds_identity_of_inner_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.exists_metricBounds_identity_of_inner_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.exists_metricBounds_identity_of_inner_bounds ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.exists_metricBounds_identity_of_inner_bounds


end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

end
