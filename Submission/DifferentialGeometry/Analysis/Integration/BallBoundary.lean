import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Restrict

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Metric

namespace MeasureTheory
open _root_.MeasureTheory

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} {c : X} {r : ℝ}

open _root_.MeasureTheory in
theorem ae_mem_ball_of_measure_sphere_eq_zero (h : μ (_root_.Metric.sphere c r) = 0) :
    ∀ᵐ x ∂μ.restrict (_root_.Metric.closedBall c r), x ∈ _root_.Metric.ball c r := by
  have hzero : ∀ᵐ x ∂μ, x ∉ _root_.Metric.sphere c r := by
    rw [_root_.MeasureTheory.ae_iff]
    convert h using 1
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, _root_.Classical.not_not]
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_closedBall, _root_.MeasureTheory.ae_restrict_of_ae hzero] with x hx hxn
  exact lt_of_le_of_ne hx hxn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.ae_mem_ball_of_measure_sphere_eq_zero then
    throwError "Refusing to shadow existing declaration MeasureTheory.ae_mem_ball_of_measure_sphere_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.ae_mem_ball_of_measure_sphere_eq_zero ``Submission.MeasureTheory.ae_mem_ball_of_measure_sphere_eq_zero

end MeasureTheory
