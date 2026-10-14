import Submission.DifferentialGeometry.Geometry.Measure.Area.RegionCongruence
import Submission.DifferentialGeometry.Geometry.Measure.Area.Reparametrization
import Submission.DifferentialGeometry.Topology.LoopSpace.AttachAnnulus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Submission.DifferentialGeometry _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]



theorem riemannianArea_half_disk_dilation (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : ℂ → M} {K : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (K : ℝ≥0∞) * _root_.EDist.edist z w) :
    riemannianArea g (fun z => u ((2 : ℝ) • z)) (_root_.Metric.closedBall (0 : ℂ) (1 / 2)) =
      riemannianArea g u (_root_.Metric.closedBall (0 : ℂ) 1) := by
  let φ : ℂ →L[ℝ] ℂ := (2 : ℝ) • ContinuousLinearMap.id ℝ ℂ
  let ψ : ℂ →L[ℝ] ℂ := (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℂ
  have hinv (z : ℂ) : ψ (φ z) = z := by simp [φ, ψ]
  have himage : φ '' _root_.Metric.closedBall (0 : ℂ) (1 / 2) = _root_.Metric.closedBall (0 : ℂ) 1 := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      simp only [_root_.Metric.mem_closedBall, dist_zero_right] at hz ⊢
      change ‖(2 : ℝ) • z‖ ≤ 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    · intro z hz
      refine ⟨ψ z, ?_, ?_⟩
      · simp only [_root_.Metric.mem_closedBall, dist_zero_right] at hz ⊢
        change ‖(1 / 2 : ℝ) • z‖ ≤ 1 / 2
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        linarith
      · simp [φ, ψ]
  have h := riemannianArea_precomp g (s := _root_.Metric.closedBall (0 : ℂ) (1 / 2)) hu
    φ.lipschitz ψ.lipschitz measurableSet_closedBall
    (fun z _ => hinv z)
  rw [himage] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianArea_half_disk_dilation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianArea_half_disk_dilation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianArea_half_disk_dilation ``Submission.DifferentialGeometry.Geometry.riemannianArea_half_disk_dilation


theorem attachDiskAnnulus_inner_area (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : ℂ → M} {K : ℝ≥0}
    (hu : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (K : ℝ≥0∞) * _root_.EDist.edist z w)
    (H : ℝ × loopCircle → M) :
    riemannianArea g (attachDiskAnnulus u H) (_root_.Metric.closedBall (0 : ℂ) (1 / 2)) =
      riemannianArea g u (_root_.Metric.closedBall (0 : ℂ) 1) := by
  calc
    _ = riemannianArea g (fun z => u ((2 : ℝ) • z)) (_root_.Metric.closedBall (0 : ℂ) (1 / 2)) :=
      riemannianArea_congr_on_closedBall g (fun z hz => attachDiskAnnulus_inner u H
        (by simpa only [_root_.Metric.mem_closedBall, dist_zero_right] using hz))
    _ = _ := riemannianArea_half_disk_dilation g hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.attachDiskAnnulus_inner_area then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.attachDiskAnnulus_inner_area"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.attachDiskAnnulus_inner_area ``Submission.DifferentialGeometry.Geometry.attachDiskAnnulus_inner_area

end DifferentialGeometry.Geometry
