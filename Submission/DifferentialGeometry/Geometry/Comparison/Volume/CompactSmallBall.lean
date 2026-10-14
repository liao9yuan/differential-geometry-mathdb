import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Family.SmallBall
import Submission.DifferentialGeometry.Geometry.Metric.Family.Stationary
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

theorem exists_uniform_small_ball_volume_lower_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ κ : ℝ, 0 < ρ ∧ 0 < κ ∧ ∀ p : M, ∀ r : ℝ, 0 < r → r ≤ ρ →
      ENNReal.ofReal κ * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure (I := I) (M := M) g (riemannianBallOf g p r) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let D := RealTimeInterval.closedOpen 0 1 (by norm_num : (0 : ℝ) < 1)
  have hfamily : MetricFamilySmoothOn D (fun _ : ℝ => g) :=
    metricFamilySmoothOn_stationary g D
  obtain ⟨τ, κ, hτ, hτ1, hκ, hbound⟩ :=
    family_vol_low (I := I) (by norm_num : (0 : ℝ) < 1) (fun _ : ℝ => g)
      hfamily (rho := 1)
  refine ⟨Real.sqrt τ, κ, Real.sqrt_pos.mpr hτ, hκ, ?_⟩
  intro p r hr hrρ
  have hr1 : r ≤ 1 := hrρ.trans (Real.sqrt_le_one.mpr hτ1.le)
  have hrτ : r ^ 2 ≤ τ := (Real.le_sqrt hr.le hτ.le).mp hrρ
  exact hbound ⟨τ, hτ.le, hτ1⟩ le_rfl p hr hr1 hrτ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.exists_uniform_small_ball_volume_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.exists_uniform_small_ball_volume_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.exists_uniform_small_ball_volume_lower_bound ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.exists_uniform_small_ball_volume_lower_bound

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
