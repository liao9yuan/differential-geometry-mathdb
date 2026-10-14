import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.Convolution _root_.Pointwise _root_.Topology

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [MeasurableSpace E] [BorelSpace E] {mu : Measure E}
  [SFinite mu] [mu.IsAddLeftInvariant] [mu.IsNegInvariant]

open _root_.HasCompactSupport in
theorem HasCompactSupport.fderiv_convolution_left_apply
    {phi f : E → Real} (hsupp : HasCompactSupport phi)
    (hphi : ContDiff Real 1 phi) (hf : _root_.MeasureTheory.LocallyIntegrable f mu) (x v : E) :
    fderiv Real (phi ⋆[ContinuousLinearMap.mul Real Real, mu] f) x v =
      ((fun y ↦ fderiv Real phi y v) ⋆[ContinuousLinearMap.mul Real Real, mu] f) x := by
  have hd := (hsupp.hasFDerivAt_convolution_left
    (ContinuousLinearMap.mul Real Real) hphi hf x).fderiv
  rw [hd]
  have hI := (hsupp.fderiv Real).convolutionExists_left
    ((ContinuousLinearMap.mul Real Real).precompL E)
    (hphi.continuous_fderiv one_ne_zero) hf x
  simp only [MeasureTheory.convolution_def]
  rw [ContinuousLinearMap.integral_apply hI]
  rfl

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.HasCompactSupport
  let env ← Lean.getEnv
  if env.contains `HasCompactSupport.fderiv_convolution_left_apply then
    throwError "Refusing to shadow existing declaration HasCompactSupport.fderiv_convolution_left_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `HasCompactSupport.fderiv_convolution_left_apply ``Submission.HasCompactSupport.fderiv_convolution_left_apply

end NormedSpace

end
