import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission







noncomputable section

open _root_.MeasureTheory _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Convolution

namespace DifferentialGeometry.Analysis

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]



theorem contDiffOn_planeIntegral_of_compact_support {n : ℕ∞}
    {f : P → ℂ → ℝ} {S : Set P} {K : Set ℂ} (hS : IsOpen S) (hK : IsCompact K)
    (hzero : ∀ p, ∀ w, p ∈ S → w ∉ K → f p w = 0)
    (hf : ContDiffOn ℝ n (fun q : P × ℂ => f q.1 q.2) (S ×ˢ _root_.Set.univ)) :
    ContDiffOn ℝ n (fun p => ∫ w : ℂ, f p w) S := by
  have h := _root_.MeasureTheory.contDiffOn_convolution_left_with_param_comp (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℂ))
    (ContinuousLinearMap.mul ℝ ℝ) (v := fun _ : P => (0 : ℂ)) contDiffOn_const
    hS hK hzero (f := fun _ : ℂ => (1 : ℝ)) continuous_const.locallyIntegrable hf
  simpa only [_root_.MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply', mul_one] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiffOn_planeIntegral_of_compact_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiffOn_planeIntegral_of_compact_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiffOn_planeIntegral_of_compact_support ``Submission.DifferentialGeometry.Analysis.contDiffOn_planeIntegral_of_compact_support

end DifferentialGeometry.Analysis
