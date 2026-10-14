import Mathlib.Analysis.Calculus.ContDiff.Convolution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.MeasureTheory
open scoped _root_.Convolution

variable {𝕜 E A B F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {μ : Measure E} [SFinite μ] [μ.IsAddLeftInvariant]

open _root_.MeasureTheory in
theorem MeasureTheory.fderiv_convolution_right_apply
    (L : A →L[𝕜] B →L[𝕜] F) {k : E → A} {f : E → B}
    (hk : _root_.MeasureTheory.LocallyIntegrable k μ) (hc : HasCompactSupport f)
    (hf : ContDiff 𝕜 1 f) (x v : E) :
    fderiv 𝕜 (k ⋆[L, μ] f) x v =
      (k ⋆[L, μ] (fun y => fderiv 𝕜 f y v)) x := by
  rw [(hc.hasFDerivAt_convolution_right L hk hf x).fderiv]
  exact _root_.MeasureTheory.convolution_precompR_apply L hk (hc.fderiv 𝕜)
    (hf.continuous_fderiv (by norm_num)) x v

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MeasureTheory
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.fderiv_convolution_right_apply then
    throwError "Refusing to shadow existing declaration MeasureTheory.fderiv_convolution_right_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.fderiv_convolution_right_apply ``Submission.MeasureTheory.fderiv_convolution_right_apply

open _root_.MeasureTheory in
theorem MeasureTheory.fderiv_convolution_left_apply [μ.IsNegInvariant]
    (L : A →L[𝕜] B →L[𝕜] F) {k : E → A} {f : E → B}
    (hc : HasCompactSupport k) (hk : ContDiff 𝕜 1 k) (hf : _root_.MeasureTheory.LocallyIntegrable f μ) (x v : E) :
    fderiv 𝕜 (k ⋆[L, μ] f) x v =
      ((fun y => fderiv 𝕜 k y v) ⋆[L, μ] f) x := by
  simp +singlePass only [← _root_.MeasureTheory.convolution_flip]
  exact fderiv_convolution_right_apply L.flip hf hc hk x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.fderiv_convolution_left_apply then
    throwError "Refusing to shadow existing declaration MeasureTheory.fderiv_convolution_left_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.fderiv_convolution_left_apply ``Submission.MeasureTheory.fderiv_convolution_left_apply

open _root_.MeasureTheory in
theorem MeasureTheory.fderiv_fderiv_convolution_right_apply
    (L : A →L[𝕜] B →L[𝕜] F) {k : E → A} {f : E → B}
    (hk : _root_.MeasureTheory.LocallyIntegrable k μ) (hc : HasCompactSupport f)
    (hf : ContDiff 𝕜 2 f) (x v w : E) :
    fderiv 𝕜 (fderiv 𝕜 (k ⋆[L, μ] f)) x v w =
      (k ⋆[L, μ] (fun y => fderiv 𝕜 (fderiv 𝕜 f) y v w)) x := by
  have hconv : ContDiff 𝕜 2 (k ⋆[L, μ] f) := hc.contDiff_convolution_right L hk hf
  have hdiff := (hconv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heq : (fun y => fderiv 𝕜 (k ⋆[L, μ] f) y w) =
      k ⋆[L, μ] (fun y => fderiv 𝕜 f y w) := by
    funext y
    exact fderiv_convolution_right_apply L hk hc (hf.of_le (by norm_num)) y w
  have hpartial : ContDiff 𝕜 1 (fun y => fderiv 𝕜 f y w) :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hderiv (y : E) : fderiv 𝕜 (fun z => fderiv 𝕜 f z w) y v =
      fderiv 𝕜 (fderiv 𝕜 f) y v w := by
    rw [fderiv_clm_apply ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) y)
      (differentiableAt_const w)]
    simp
  have hv : fderiv 𝕜 (fun y => fderiv 𝕜 (k ⋆[L, μ] f) y w) x v =
      fderiv 𝕜 (fderiv 𝕜 (k ⋆[L, μ] f)) x v w := by
    rw [fderiv_clm_apply (hdiff x) (differentiableAt_const w)]
    simp
  rw [← hv, heq, fderiv_convolution_right_apply L hk (hc.fderiv_apply 𝕜 w) hpartial]
  simp_rw [hderiv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.fderiv_fderiv_convolution_right_apply then
    throwError "Refusing to shadow existing declaration MeasureTheory.fderiv_fderiv_convolution_right_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.fderiv_fderiv_convolution_right_apply ``Submission.MeasureTheory.fderiv_fderiv_convolution_right_apply

open _root_.MeasureTheory in
theorem MeasureTheory.fderiv_fderiv_convolution_left_apply [μ.IsNegInvariant]
    (L : A →L[𝕜] B →L[𝕜] F) {k : E → A} {f : E → B}
    (hc : HasCompactSupport k) (hk : ContDiff 𝕜 2 k) (hf : _root_.MeasureTheory.LocallyIntegrable f μ) (x v w : E) :
    fderiv 𝕜 (fderiv 𝕜 (k ⋆[L, μ] f)) x v w =
      ((fun y => fderiv 𝕜 (fderiv 𝕜 k) y v w) ⋆[L, μ] f) x := by
  simp +singlePass only [← _root_.MeasureTheory.convolution_flip]
  exact fderiv_fderiv_convolution_right_apply L.flip hf hc hk x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.fderiv_fderiv_convolution_left_apply then
    throwError "Refusing to shadow existing declaration MeasureTheory.fderiv_fderiv_convolution_left_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.fderiv_fderiv_convolution_left_apply ``Submission.MeasureTheory.fderiv_fderiv_convolution_left_apply
