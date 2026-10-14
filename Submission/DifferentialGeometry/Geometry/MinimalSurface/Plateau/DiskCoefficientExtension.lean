import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricCoefficient
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.Ball
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]





theorem SmoothDiskExtension.exists_nonneg_coefficient_extension
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : C(closedDisk, M)} {U : ℂ → M}
    (hu : SmoothDiskExtension (E := E) u U) :
    ∃ A : ℂ → ℝ, ContDiff ℝ ∞ A ∧ HasCompactSupport A ∧ (∀ z, 0 ≤ A z) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        A =ᶠ[𝓝 z] diskMapConformalCoefficient g U := by
  obtain ⟨_, N, hN, hDN, hU⟩ := hu
  obtain ⟨δ, hδ, hδN⟩ := (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) 1).exists_cthickening_subset_open hN hDN
  rw [cthickening_closedBall hδ.le (by norm_num : (0 : ℝ) ≤ 1)] at hδN
  have hball : Metric.ball (0 : ℂ) (δ + 1) ⊆ N := Metric.ball_subset_closedBall.trans hδN
  exact exists_contDiff_nonneg_compactSupport_eq_near_closedBall (by norm_num)
    (by linarith : (1 : ℝ) < δ + 1)
    ((contDiffOn_diskMapConformalCoefficient g hN hU).mono hball)
    (fun z _ => diskMapConformalCoefficient_nonneg g U z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.exists_nonneg_coefficient_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.exists_nonneg_coefficient_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.exists_nonneg_coefficient_extension ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.exists_nonneg_coefficient_extension

end DifferentialGeometry.Geometry
