import Submission.DifferentialGeometry.Analysis.Calculus.Multilinear

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Analysis.Calculus

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem cml_deriv_zero {n : ℕ}
    {A : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F}
    {A' : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F}
    {V : Fin n → ℝ → E} {V' : Fin n → E} {s : ℝ}
    (hA : HasDerivAt A A' s) (hV : ∀ i, HasDerivAt (V i) (V' i) s)
    (hzero : A s = 0) :
    HasDerivAt (fun r => A r (fun i => V i r))
      (A' (fun i => V i s)) s := by
  simpa only [hzero, zero_apply, Finset.sum_const_zero, add_zero] using
    hA.continuousMultilinearMap_apply hV

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.cml_deriv_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.cml_deriv_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.cml_deriv_zero ``Submission.DifferentialGeometry.Analysis.Calculus.cml_deriv_zero

end DifferentialGeometry.Analysis.Calculus
