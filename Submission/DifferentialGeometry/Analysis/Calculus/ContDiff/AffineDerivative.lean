import Mathlib.Analysis.Calculus.ContDiff.Operations

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


namespace DifferentialGeometry.Analysis.Calculus

open scoped _root_.ContDiff

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem contDiffOn_succ_of_fderiv_eq_add_clm_apply
    {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : DifferentiableOn 𝕜 f U)
    {A : E → E →L[𝕜] F} {Γ : E → F →L[𝕜] E →L[𝕜] F}
    (heq : Set.EqOn (fderiv 𝕜 f) (fun x => A x + Γ x (f x)) U)
    (n : ℕ) (hA : ContDiffOn 𝕜 n A U) (hΓ : ContDiffOn 𝕜 n Γ U) :
    ContDiffOn 𝕜 (n + 1) f U := by
  revert hA hΓ
  induction n with
  | zero =>
    intro hA hΓ
    have hfzero : ContDiffOn 𝕜 0 f U := contDiffOn_zero.mpr hf.continuousOn
    have hdf : ContDiffOn 𝕜 0 (fderiv 𝕜 f) U :=
      (hA.add (hΓ.clm_apply hfzero)).congr heq
    exact (contDiffOn_succ_iff_fderiv_of_isOpen hU).mpr ⟨hf, by simp, hdf⟩
  | succ n ih =>
    intro hA hΓ
    have hfprev : ContDiffOn 𝕜 (n + 1) f U :=
      ih (hA.of_le (by exact_mod_cast Nat.le_succ n))
        (hΓ.of_le (by exact_mod_cast Nat.le_succ n))
    have hdf : ContDiffOn 𝕜 (n + 1) (fderiv 𝕜 f) U :=
      (hA.add (hΓ.clm_apply hfprev)).congr heq
    exact (contDiffOn_succ_iff_fderiv_of_isOpen hU).mpr ⟨hf, by simp, hdf⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.contDiffOn_succ_of_fderiv_eq_add_clm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.contDiffOn_succ_of_fderiv_eq_add_clm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.contDiffOn_succ_of_fderiv_eq_add_clm_apply ``Submission.DifferentialGeometry.Analysis.Calculus.contDiffOn_succ_of_fderiv_eq_add_clm_apply

theorem contDiffOn_of_fderiv_eq_add_clm_apply
    {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : DifferentiableOn 𝕜 f U)
    {A : E → E →L[𝕜] F} {Γ : E → F →L[𝕜] E →L[𝕜] F}
    (heq : Set.EqOn (fderiv 𝕜 f) (fun x => A x + Γ x (f x)) U)
    (hA : ContDiffOn 𝕜 ∞ A U) (hΓ : ContDiffOn 𝕜 ∞ Γ U) :
    ContDiffOn 𝕜 ∞ f U := by
  apply contDiffOn_infty.mpr
  intro n
  cases n with
  | zero => exact contDiffOn_zero.mpr hf.continuousOn
  | succ n =>
    exact contDiffOn_succ_of_fderiv_eq_add_clm_apply hU hf heq n
      (contDiffOn_infty.mp hA n) (contDiffOn_infty.mp hΓ n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.contDiffOn_of_fderiv_eq_add_clm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.contDiffOn_of_fderiv_eq_add_clm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.contDiffOn_of_fderiv_eq_add_clm_apply ``Submission.DifferentialGeometry.Analysis.Calculus.contDiffOn_of_fderiv_eq_add_clm_apply

end DifferentialGeometry.Analysis.Calculus
