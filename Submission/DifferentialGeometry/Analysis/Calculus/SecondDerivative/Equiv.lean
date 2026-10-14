import Mathlib.Analysis.Calculus.FDeriv.Equiv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.ContinuousLinearEquiv in
theorem ContinuousLinearEquiv.comp_right_fderiv_fderiv
    {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (e : E ≃L[𝕜] F) (f : F → G) (x v w : E) :
    fderiv 𝕜 (fderiv 𝕜 (f ∘ e)) x v w =
      fderiv 𝕜 (fderiv 𝕜 f) (e x) (e v) (e w) := by
  let A := e.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 G)
  have hd : fderiv 𝕜 (f ∘ e) = A ∘ ((fderiv 𝕜 f) ∘ e) := by
    funext y
    rw [e.comp_right_fderiv]
    rfl
  rw [hd, A.comp_fderiv, e.comp_right_fderiv]
  simp [A]

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContinuousLinearEquiv
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearEquiv.comp_right_fderiv_fderiv then
    throwError "Refusing to shadow existing declaration ContinuousLinearEquiv.comp_right_fderiv_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearEquiv.comp_right_fderiv_fderiv ``Submission.ContinuousLinearEquiv.comp_right_fderiv_fderiv
