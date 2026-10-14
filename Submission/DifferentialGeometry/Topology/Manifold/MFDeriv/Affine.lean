import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold
namespace DifferentialGeometry.Manifold
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}


theorem mfderiv_const_sub_real {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (b : ℝ) :
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y => b - f y) x) =
      -(show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x) := by
  change (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) ((fun _ : M => b) - f) x) = _
  erw [mfderiv_sub mdifferentiableAt_const hf,mfderiv_const,zero_sub]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.mfderiv_const_sub_real then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.mfderiv_const_sub_real"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.mfderiv_const_sub_real ``Submission.DifferentialGeometry.Manifold.mfderiv_const_sub_real

end DifferentialGeometry.Manifold
