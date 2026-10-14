import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Tactic.NormNum

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.HasCompactSupport in
theorem HasCompactSupport.comp_prodMk_right
    {T E A : Type*} [TopologicalSpace T] [TopologicalSpace E] [Zero A]
    {φ : T × E → A} (hφ : HasCompactSupport φ) (t : T) :
    HasCompactSupport (fun x => φ (t, x)) := by
  apply (hφ.isCompact.image continuous_snd).of_isClosed_subset (isClosed_tsupport _)
  intro x hx
  exact ⟨(t, x), tsupport_comp_subset_preimage φ
    (continuous_const.prodMk continuous_id) hx, rfl⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.HasCompactSupport
  let env ← Lean.getEnv
  if env.contains `HasCompactSupport.comp_prodMk_right then
    throwError "Refusing to shadow existing declaration HasCompactSupport.comp_prodMk_right"
  Lean.modifyEnv fun env => Lean.addAlias env `HasCompactSupport.comp_prodMk_right ``Submission.HasCompactSupport.comp_prodMk_right

open _root_.DifferentiableAt in
theorem DifferentiableAt.fderiv_prodMk_right_apply
    {𝕜 T E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup T] [NormedSpace 𝕜 T]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {φ : T × E → F} {t : T} {x : E} (hφ : DifferentiableAt 𝕜 φ (t, x)) (v : E) :
    fderiv 𝕜 (fun y => φ (t, y)) x v = fderiv 𝕜 φ (t, x) (0, v) := by
  have heq := (hφ.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv
  exact congrArg (fun L => L v) heq

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentiableAt
  let env ← Lean.getEnv
  if env.contains `DifferentiableAt.fderiv_prodMk_right_apply then
    throwError "Refusing to shadow existing declaration DifferentiableAt.fderiv_prodMk_right_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentiableAt.fderiv_prodMk_right_apply ``Submission.DifferentiableAt.fderiv_prodMk_right_apply

open _root_.ContDiff in
theorem ContDiff.fderiv_fderiv_prodMk_right_apply
    {𝕜 T E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup T] [NormedSpace 𝕜 T]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {φ : T × E → F} (hφ : ContDiff 𝕜 2 φ) (t : T) (x v : E) :
    fderiv 𝕜 (fun y => fderiv 𝕜 (fun z => φ (t, z)) y v) x v =
      fderiv 𝕜 (fun p => fderiv 𝕜 φ p (0, v)) (t, x) (0, v) := by
  have hfirst : ∀ y, fderiv 𝕜 (fun z => φ (t, z)) y v =
      fderiv 𝕜 φ (t, y) (0, v) := fun y =>
    (hφ.differentiable (by norm_num) (t, y)).fderiv_prodMk_right_apply v
  simp only [hfirst]
  have hD : ContDiff 𝕜 1 (fun p => fderiv 𝕜 φ p (0, v)) :=
    (hφ.fderiv_right (by norm_num)).clm_apply contDiff_const
  exact (hD.differentiable one_ne_zero (t, x)).fderiv_prodMk_right_apply v

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContDiff
  let env ← Lean.getEnv
  if env.contains `ContDiff.fderiv_fderiv_prodMk_right_apply then
    throwError "Refusing to shadow existing declaration ContDiff.fderiv_fderiv_prodMk_right_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiff.fderiv_fderiv_prodMk_right_apply ``Submission.ContDiff.fderiv_fderiv_prodMk_right_apply
