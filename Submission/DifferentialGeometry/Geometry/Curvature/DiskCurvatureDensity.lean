import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.NonconstantCoefficient
import Submission.DifferentialGeometry.Analysis.Integration.Measure.SmoothDensity
import Submission.DifferentialGeometry.Geometry.Curvature.DiskRegularizer

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]




theorem SmoothDiskExtension.exists_curvature_density
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : C(closedDisk, M)} {U : ℂ → M}
    (hu : SmoothDiskExtension (E := E) u U)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U z)
    (hnon : ¬ ∃ c : M, ∀ z : closedDisk, u z = c) :
    ∃ κ : ℂ → ℝ, ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧
      tsupport κ ⊆ Metric.ball (0 : ℂ) 1 ∩
        (diskMapConformalCoefficient g U) ⁻¹' _root_.Set.Ioi 0 ∧
      (∀ z, 0 ≤ κ z) ∧ (∫ z, κ z) = 2 * Real.pi := by
  obtain ⟨z, hz, hpos⟩ := hu.exists_pos_coefficient g hconf hnon
  obtain ⟨_, N, hN, hDN, hU⟩ := hu
  have hc := ((contDiffOn_diskMapConformalCoefficient g hN hU).mono
    (Metric.ball_subset_closedBall.trans hDN)).continuousOn
  exact exists_smooth_nonneg_density
    (hc.isOpen_inter_preimage Metric.isOpen_ball isOpen_Ioi) ⟨z, hz, hpos⟩
    (mul_pos (by norm_num) Real.pi_pos)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.exists_curvature_density then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.exists_curvature_density"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.exists_curvature_density ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.exists_curvature_density




theorem SmoothDiskExtension.exists_curvature_regularizer
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : C(closedDisk, M)} {U : ℂ → M}
    (hu : SmoothDiskExtension (E := E) u U)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U z)
    (hnon : ¬ ∃ c : M, ∀ z : closedDisk, u z = c) :
    ∃ κ F : ℂ → ℝ, ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧
      tsupport κ ⊆ Metric.ball (0 : ℂ) 1 ∩
        (diskMapConformalCoefficient g U) ⁻¹' _root_.Set.Ioi 0 ∧
      (∀ z, 0 ≤ κ z) ∧ (∫ z, κ z) = 2 * Real.pi ∧ ContDiff ℝ ∞ F ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, F =ᶠ[𝓝 z] diskRegularizerPotential κ) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, -Laplacian.laplacian F z = κ z) ∧
      (∀ z : ℂ, ‖z‖ = 1 → fderiv ℝ F z z = -1) := by
  obtain ⟨κ, hκ, hc, hs, hn, hmass⟩ := hu.exists_curvature_density g hconf hnon
  obtain ⟨F, hF, heq, hK, hk⟩ := exists_diskRegularizer_metric hc hκ
    (hs.trans _root_.Set.inter_subset_left) hmass
  refine ⟨κ, F, hκ, hc, hs, hn, hmass, hF, heq, ?_, ?_⟩
  · intro z hz
    simpa only [planeGaussianCurvature_mul_areaDensity hF] using hK z hz
  · intro z hz
    have h := hk z hz
    rw [conformalCircleGeodesicCurvature_eq hF hz] at h
    have h' := (mul_eq_zero.mp h).resolve_left (Real.exp_ne_zero _)
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.exists_curvature_regularizer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.exists_curvature_regularizer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.exists_curvature_regularizer ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.exists_curvature_regularizer

end DifferentialGeometry.Geometry
