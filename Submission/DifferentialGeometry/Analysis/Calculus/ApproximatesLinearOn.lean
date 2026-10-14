import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.ApproximatesLinearOn in
theorem ApproximatesLinearOn.fderiv_sub_le
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {A : E →L[𝕜] F} {s : Set E} {c : NNReal} {x : E}
    (hf : ApproximatesLinearOn f A s c) (hs : s ∈ nhds x)
    (hfd : DifferentiableAt 𝕜 f x) :
    ‖fderiv 𝕜 f x - A‖ ≤ (c : Real) := by
  have hres : HasFDerivAt (f - (A : E → F))
      (fderiv 𝕜 f x - A) x := by
    simpa only [Pi.sub_apply] using hfd.hasFDerivAt.sub A.hasFDerivAt
  exact hres.le_of_lipschitzOn hs hf.lipschitzOnWith

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ApproximatesLinearOn
  let env ← Lean.getEnv
  if env.contains `ApproximatesLinearOn.fderiv_sub_le then
    throwError "Refusing to shadow existing declaration ApproximatesLinearOn.fderiv_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `ApproximatesLinearOn.fderiv_sub_le ``Submission.ApproximatesLinearOn.fderiv_sub_le
