import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.GreenIdentity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Filter _root_.InnerProductSpace
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis

private theorem scalar_comp_partial {f : ℂ → ℝ} {φ : ℝ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hφ : DifferentiableAt ℝ φ (f z)) (v : ℂ) :
    fderiv ℝ (φ ∘ f) z v = deriv φ (f z) * fderiv ℝ f z v := by
  rw [(hφ.hasDerivAt.comp_hasFDerivAt z hf.hasFDerivAt).fderiv]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.scalar_comp_partial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.scalar_comp_partial target :: scope.openDecls } }

private theorem scalar_comp_second_partial {f : ℂ → ℝ} {φ : ℝ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hφ : ContDiffAt ℝ 2 φ (f z)) (v w : ℂ) :
    fderiv ℝ (fun q => fderiv ℝ (φ ∘ f) q v) z w =
      deriv (deriv φ) (f z) * fderiv ℝ f z w * fderiv ℝ f z v +
        deriv φ (f z) * fderiv ℝ (fun q => fderiv ℝ f q v) z w := by
  have hfd := hf.differentiableAt (by norm_num)
  have hnear : (fun q => fderiv ℝ (φ ∘ f) q v) =ᶠ[𝓝 z]
      (fun q => deriv φ (f q) * fderiv ℝ f q v) := by
    filter_upwards [hf.eventually (by norm_num),
      hfd.continuousAt (hφ.eventually (by norm_num))] with q hq hφq
    change ContDiffAt ℝ 2 φ (f q) at hφq
    exact scalar_comp_partial (hq.differentiableAt (by norm_num))
      (hφq.differentiableAt (by norm_num)) v
  have hφd : DifferentiableAt ℝ (deriv φ) (f z) :=
    (hφ.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hpart : DifferentiableAt ℝ (fun q => fderiv ℝ f q v) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  rw [hnear.fderiv_eq]
  erw [fderiv_fun_mul (hφd.comp z hfd) hpart]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [scalar_comp_partial hfd hφd w]
  dsimp only [Function.comp_apply]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.scalar_comp_second_partial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.scalar_comp_second_partial target :: scope.openDecls } }



theorem laplacian_comp_scalar {f : ℂ → ℝ} {φ : ℝ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hφ : ContDiffAt ℝ 2 φ (f z)) :
    Laplacian.laplacian (φ ∘ f) z =
      deriv φ (f z) * Laplacian.laplacian f z +
        deriv (deriv φ) (f z) * ((fderiv ℝ f z 1) ^ 2 + (fderiv ℝ f z Complex.I) ^ 2) := by
  rw [← complexDivergence_gradient (hφ.comp z hf)]
  unfold complexDivergence
  rw [scalar_comp_second_partial hf hφ, scalar_comp_second_partial hf hφ]
  have hΔ := complexDivergence_gradient hf
  unfold complexDivergence at hΔ
  rw [← hΔ]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.laplacian_comp_scalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.laplacian_comp_scalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.laplacian_comp_scalar ``Submission.DifferentialGeometry.Analysis.laplacian_comp_scalar



theorem laplacian_log {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) (hz : f z ≠ 0) :
    Laplacian.laplacian (fun q => Real.log (f q)) z =
      Laplacian.laplacian f z / f z -
        ((fderiv ℝ f z 1) ^ 2 + (fderiv ℝ f z Complex.I) ^ 2) / (f z) ^ 2 := by
  have h := laplacian_comp_scalar hf (Real.contDiffAt_log.mpr hz)
  rw [Real.deriv_log] at h
  have hd : deriv Real.log = fun r : ℝ => r⁻¹ := by
    funext r
    exact Real.deriv_log r
  rw [hd, deriv_inv] at h
  change Laplacian.laplacian (fun q => Real.log (f q)) z = _ at h
  rw [h]
  simp only [div_eq_mul_inv]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.laplacian_log then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.laplacian_log"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.laplacian_log ``Submission.DifferentialGeometry.Analysis.laplacian_log


theorem laplacian_exp {f : ℂ → ℝ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) :
    Laplacian.laplacian (fun q => Real.exp (f q)) z =
      Real.exp (f z) * (Laplacian.laplacian f z +
        (fderiv ℝ f z 1) ^ 2 + (fderiv ℝ f z Complex.I) ^ 2) := by
  have h := laplacian_comp_scalar hf Real.contDiff_exp.contDiffAt
  simp only [Real.deriv_exp] at h
  change Laplacian.laplacian (fun q => Real.exp (f q)) z = _ at h
  rw [h]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.laplacian_exp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.laplacian_exp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.laplacian_exp ``Submission.DifferentialGeometry.Analysis.laplacian_exp

end DifferentialGeometry.Analysis
