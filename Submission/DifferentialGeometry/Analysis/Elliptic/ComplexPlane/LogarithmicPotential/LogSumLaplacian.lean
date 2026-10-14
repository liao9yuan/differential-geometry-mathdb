import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LaplacianCalculus
import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Gradient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.InnerProductSpace
open scoped _root_.ContDiff

namespace DifferentialGeometry.Analysis

private theorem partial_log {f : ℂ → ℝ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hz : f z ≠ 0) (v : ℂ) :
    fderiv ℝ (fun q => Real.log (f q)) z v = fderiv ℝ f z v / f z := by
  rw [(hf.hasFDerivAt.log hz).fderiv]
  simp only [_root_.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.partial_log
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.partial_log target :: scope.openDecls } }




theorem laplacian_log_add {a b : ℂ → ℝ} {z : ℂ}
    (ha : ContDiffAt ℝ 2 a z) (hb : ContDiffAt ℝ 2 b z)
    (hapos : 0 < a z) (hbpos : 0 < b z) :
    Laplacian.laplacian (fun q => Real.log (a q + b q)) z =
      a z / (a z + b z) * Laplacian.laplacian (fun q => Real.log (a q)) z +
      b z / (a z + b z) * Laplacian.laplacian (fun q => Real.log (b q)) z +
      (a z * b z / (a z + b z) ^ 2) *
        ‖gradient (fun q => Real.log (a q)) z - gradient (fun q => Real.log (b q)) z‖ ^ 2 := by
  have ha0 := hapos.ne'
  have hb0 := hbpos.ne'
  have hab0 := (add_pos hapos hbpos).ne'
  rw [laplacian_log (ha.add hb) hab0, laplacian_log ha ha0, laplacian_log hb hb0,
    norm_gradient_sub_complex_sq]
  erw [ha.laplacian_add hb, fderiv_fun_add (ha.differentiableAt (by norm_num))
    (hb.differentiableAt (by norm_num))]
  simp only [_root_.add_apply, partial_log (ha.differentiableAt (by norm_num)) ha0,
    partial_log (hb.differentiableAt (by norm_num)) hb0]
  field_simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.laplacian_log_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.laplacian_log_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.laplacian_log_add ``Submission.DifferentialGeometry.Analysis.laplacian_log_add




theorem neg_half_laplacian_log_add_le {a b : ℂ → ℝ} {z : ℂ}
    (ha : ContDiffAt ℝ 2 a z) (hb : ContDiffAt ℝ 2 b z)
    (hapos : 0 < a z) (hbpos : 0 < b z) :
    -(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (a q + b q)) z ≤
      a z / (a z + b z) * (-(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (a q)) z) +
      b z / (a z + b z) * (-(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (b q)) z) := by
  rw [laplacian_log_add ha hb hapos hbpos]
  have hn : 0 ≤ (a z * b z / (a z + b z) ^ 2) *
      ‖gradient (fun q => Real.log (a q)) z - gradient (fun q => Real.log (b q)) z‖ ^ 2 := by
    positivity
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.neg_half_laplacian_log_add_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.neg_half_laplacian_log_add_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.neg_half_laplacian_log_add_le ``Submission.DifferentialGeometry.Analysis.neg_half_laplacian_log_add_le

end DifferentialGeometry.Analysis
