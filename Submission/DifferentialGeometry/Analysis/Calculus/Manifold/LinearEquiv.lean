import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Equiv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Manifold
open scoped _root_.Manifold

namespace ContinuousLinearEquiv
open _root_.ContinuousLinearEquiv

open _root_.ContinuousLinearEquiv in
theorem comp_right_mfderiv
    {V W E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    (L : V ≃L[ℝ] W) (u : W → M) (x : V) :
    mfderiv 𝓘(ℝ, V) I (u ∘ L) x =
      (mfderiv 𝓘(ℝ, W) I u (L x)).comp L.toContinuousLinearMap := by
  have hL : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, W) L x := L.differentiableAt.mdifferentiableAt
  by_cases hu : MDifferentiableAt 𝓘(ℝ, W) I u (L x)
  · rw [mfderiv_comp x hu hL, mfderiv_eq_fderiv, L.hasFDerivAt.fderiv]
    rfl
  · have hc : ¬ MDifferentiableAt 𝓘(ℝ, V) I (u ∘ L) x := by
      intro h
      have hi : MDifferentiableAt 𝓘(ℝ, W) 𝓘(ℝ, V) L.symm (L x) :=
        L.symm.differentiableAt.mdifferentiableAt
      have h' : MDifferentiableAt 𝓘(ℝ, V) I (u ∘ L) (L.symm (L x)) :=
        (L.symm_apply_apply x).symm ▸ h
      have heq : ((u ∘ L) ∘ L.symm) = u := by
        funext y
        simp only [Function.comp_apply, L.apply_symm_apply]
      exact hu (heq ▸ h'.comp (L x) hi)
    rw [mfderiv_zero_of_not_mdifferentiableAt hc, mfderiv_zero_of_not_mdifferentiableAt hu]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearEquiv.comp_right_mfderiv then
    throwError "Refusing to shadow existing declaration ContinuousLinearEquiv.comp_right_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearEquiv.comp_right_mfderiv ``Submission.ContinuousLinearEquiv.comp_right_mfderiv

end ContinuousLinearEquiv

end
