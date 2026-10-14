import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LogarithmicPotential.LogSumLaplacian
import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LaplacianMinimum

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.InnerProductSpace _root_.Submission.InnerProductSpace _root_.Filter
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis



theorem neg_half_laplacian_log_add_at_zero {a b : ℂ → ℝ} {z : ℂ}
    (ha : ContDiffAt ℝ 2 a z) (hb : ContDiffAt ℝ 2 b z)
    (han : ∀ᶠ q in 𝓝 z, 0 ≤ a q) (ha0 : a z = 0) (hbpos : 0 < b z) :
    -(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (a q + b q)) z =
      -(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (b q)) z -
        Laplacian.laplacian a z / (2 * b z) := by
  have hd := (differential_laplacian_at_nonnegative_zero ha han ha0).1
  have hab0 : a z + b z ≠ 0 := by simpa only [ha0, zero_add] using hbpos.ne'
  rw [laplacian_log (ha.add hb) hab0, laplacian_log hb hbpos.ne']
  erw [ha.laplacian_add hb, fderiv_fun_add (ha.differentiableAt (by norm_num))
    (hb.differentiableAt (by norm_num))]
  simp only [ha0, zero_add, hd]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.neg_half_laplacian_log_add_at_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.neg_half_laplacian_log_add_at_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.neg_half_laplacian_log_add_at_zero ``Submission.DifferentialGeometry.Analysis.neg_half_laplacian_log_add_at_zero



theorem neg_half_laplacian_log_add_le_at_zero {a b : ℂ → ℝ} {z : ℂ}
    (ha : ContDiffAt ℝ 2 a z) (hb : ContDiffAt ℝ 2 b z)
    (han : ∀ᶠ q in 𝓝 z, 0 ≤ a q) (ha0 : a z = 0) (hbpos : 0 < b z) :
    -(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (a q + b q)) z ≤
      -(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (b q)) z := by
  rw [neg_half_laplacian_log_add_at_zero ha hb han ha0 hbpos]
  exact sub_le_self _ (div_nonneg
    (differential_laplacian_at_nonnegative_zero ha han ha0).2 (by positivity))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.neg_half_laplacian_log_add_le_at_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.neg_half_laplacian_log_add_le_at_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.neg_half_laplacian_log_add_le_at_zero ``Submission.DifferentialGeometry.Analysis.neg_half_laplacian_log_add_le_at_zero




theorem neg_half_laplacian_log_add_le_nonnegative {a b : ℂ → ℝ} {z : ℂ}
    (ha : ContDiffAt ℝ 2 a z) (hb : ContDiffAt ℝ 2 b z)
    (han : ∀ᶠ q in 𝓝 z, 0 ≤ a q) (hbpos : 0 < b z) :
    -(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (a q + b q)) z ≤
      (if a z = 0 then 0 else a z / (a z + b z) *
        (-(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (a q)) z)) +
      b z / (a z + b z) *
        (-(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (b q)) z) := by
  by_cases ha0 : a z = 0
  · simpa [ha0, hbpos.ne'] using
      neg_half_laplacian_log_add_le_at_zero ha hb han ha0 hbpos
  · rw [if_neg ha0]
    exact neg_half_laplacian_log_add_le ha hb
      (lt_of_le_of_ne han.self_of_nhds (Ne.symm ha0)) hbpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.neg_half_laplacian_log_add_le_nonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.neg_half_laplacian_log_add_le_nonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.neg_half_laplacian_log_add_le_nonnegative ``Submission.DifferentialGeometry.Analysis.neg_half_laplacian_log_add_le_nonnegative

end DifferentialGeometry.Analysis
