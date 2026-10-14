import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Bochner.Set

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Topology _root_.ENNReal _root_.NNReal _root_.ContDiff

namespace DifferentialGeometry.Analysis

theorem integral_ball_add_collar
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) {r R : ℝ} (hrR : r ≤ R)
    (hi : _root_.MeasureTheory.IntegrableOn f (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R)) :
    (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r, f x) +
      (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R \ Metric.closedBall 0 r, f x) =
      ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R, f x := by
  have hnull := measure_eq_zero_iff_ae_notMem.mp
    (Measure.addHaar_sphere _root_.MeasureTheory.MeasureSpace.volume (0 : EuclideanSpace ℝ (Fin 2)) r)
  have heq : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R \ Metric.closedBall 0 r =ᵐ[_root_.MeasureTheory.MeasureSpace.volume]
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R \ Metric.ball 0 r := by
    filter_upwards [hnull] with x hx
    apply propext
    have hn : _root_.Dist.dist x (0 : EuclideanSpace ℝ (Fin 2)) ≠ r := hx
    change (_root_.Dist.dist x (0 : EuclideanSpace ℝ (Fin 2)) < R ∧ ¬ _root_.Dist.dist x 0 ≤ r) ↔
      (_root_.Dist.dist x (0 : EuclideanSpace ℝ (Fin 2)) < R ∧ ¬ _root_.Dist.dist x 0 < r)
    exact and_congr_right fun _ =>
      ⟨fun h => (lt_of_not_ge h).le |> not_lt.mpr,
        fun h => not_le.mpr (lt_of_le_of_ne (not_lt.mp h) hn.symm)⟩
  have heqi := _root_.MeasureTheory.setIntegral_congr_set (f := f) heq
  have hsplit := _root_.MeasureTheory.setIntegral_sdiff Metric.isOpen_ball.measurableSet hi (Metric.ball_subset_ball hrR)
  have h := eq_sub_iff_add_eq.mp (heqi.trans hsplit)
  convert h using 1
  exact add_comm _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_ball_add_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_ball_add_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_ball_add_collar ``Submission.DifferentialGeometry.Analysis.integral_ball_add_collar

end DifferentialGeometry.Analysis

end
