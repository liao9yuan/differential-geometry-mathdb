import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricCoefficient
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import Submission.DifferentialGeometry.Geometry.Metric.ZeroDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]





theorem SmoothDiskExtension.exists_pos_coefficient
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : C(closedDisk, M)} {U : ℂ → M}
    (hu : SmoothDiskExtension (E := E) u U)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U z)
    (hnon : ¬ ∃ c : M, ∀ z : closedDisk, u z = c) :
    ∃ z ∈ Metric.ball (0 : ℂ) 1, 0 < diskMapConformalCoefficient g U z := by
  by_contra hpos
  push Not at hpos
  obtain ⟨heq, N, hN, hDN, hU⟩ := hu
  have hder : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z = 0 := by
    intro z hz
    exact (hconf z hz).coefficient_eq_zero_iff.mp
      (le_antisymm (hpos z hz) (diskMapConformalCoefficient_nonneg g U z))
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hconst : _root_.Set.EqOn U (fun _ => U 0) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    exact eq_of_mfderiv_eq_zero_on_convex g hN (hU.of_le (by simp))
      (Metric.ball_subset_closedBall.trans hDN) (convex_ball (0 : ℂ) 1) hder hz h0
  have hclosed : _root_.Set.EqOn U (fun _ => U 0) (Metric.closedBall (0 : ℂ) 1) :=
    hconst.of_subset_closure (hU.continuousOn.mono hDN) continuousOn_const
      Metric.ball_subset_closedBall (by rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)])
  apply hnon
  exact ⟨U 0, fun z => (heq z).symm.trans (hclosed z.property)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.SmoothDiskExtension.exists_pos_coefficient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.SmoothDiskExtension.exists_pos_coefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.SmoothDiskExtension.exists_pos_coefficient ``Submission.DifferentialGeometry.Geometry.SmoothDiskExtension.exists_pos_coefficient

end DifferentialGeometry.Geometry
