import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LogarithmicPotential.LogSumAtZeros

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.InnerProductSpace _root_.Submission.InnerProductSpace _root_.Filter
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis


def regularizedConformalCoefficient (a f : ℂ → ℝ) (ε : ℝ) (z : ℂ) : ℝ :=
  a z + ε ^ 2 * Real.exp (2 * f z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.regularizedConformalCoefficient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.regularizedConformalCoefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.regularizedConformalCoefficient ``Submission.DifferentialGeometry.Analysis.regularizedConformalCoefficient


def regularizedConformalWeight (a f : ℂ → ℝ) (ε : ℝ) (z : ℂ) : ℝ :=
  a z / regularizedConformalCoefficient a f ε z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.regularizedConformalWeight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.regularizedConformalWeight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.regularizedConformalWeight ``Submission.DifferentialGeometry.Analysis.regularizedConformalWeight


def regularizedConformalLogFactor (a f : ℂ → ℝ) (ε : ℝ) (z : ℂ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (regularizedConformalCoefficient a f ε z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.regularizedConformalLogFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.regularizedConformalLogFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.regularizedConformalLogFactor ``Submission.DifferentialGeometry.Analysis.regularizedConformalLogFactor

theorem regularizedConformalCoefficient_pos {a f : ℂ → ℝ} {ε : ℝ} {z : ℂ}
    (ha : 0 ≤ a z) (hε : ε ≠ 0) : 0 < regularizedConformalCoefficient a f ε z :=
  add_pos_of_nonneg_of_pos ha (mul_pos (sq_pos_of_ne_zero hε) (Real.exp_pos _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.regularizedConformalCoefficient_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.regularizedConformalCoefficient_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.regularizedConformalCoefficient_pos ``Submission.DifferentialGeometry.Analysis.regularizedConformalCoefficient_pos

theorem regularizedConformalWeight_mem_Icc {a f : ℂ → ℝ} {ε : ℝ} {z : ℂ}
    (ha : 0 ≤ a z) (hε : ε ≠ 0) : regularizedConformalWeight a f ε z ∈ Set.Icc 0 1 := by
  have hp := regularizedConformalCoefficient_pos (f := f) ha hε
  refine ⟨div_nonneg ha hp.le, (div_le_one hp).mpr ?_⟩
  change a z ≤ a z + ε ^ 2 * Real.exp (2 * f z)
  exact le_add_of_nonneg_right (by positivity)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.regularizedConformalWeight_mem_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.regularizedConformalWeight_mem_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.regularizedConformalWeight_mem_Icc ``Submission.DifferentialGeometry.Analysis.regularizedConformalWeight_mem_Icc



theorem contDiff_regularizedConformalLogFactor {a f : ℂ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (han : ∀ z, 0 ≤ a z)
    {ε : ℝ} (hε : ε ≠ 0) : ContDiff ℝ ∞ (regularizedConformalLogFactor a f ε) := by
  apply contDiff_const.mul
  exact (ha.add (contDiff_const.mul ((contDiff_const.mul hf).exp))).log
    (fun z => (regularizedConformalCoefficient_pos (f := f) (han z) hε).ne')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiff_regularizedConformalLogFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiff_regularizedConformalLogFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiff_regularizedConformalLogFactor ``Submission.DifferentialGeometry.Analysis.contDiff_regularizedConformalLogFactor



theorem exp_two_regularizedConformalLogFactor {a f : ℂ → ℝ} {z : ℂ}
    (ha : 0 ≤ a z) {ε : ℝ} (hε : ε ≠ 0) :
    Real.exp (2 * regularizedConformalLogFactor a f ε z) =
      regularizedConformalCoefficient a f ε z := by
  unfold regularizedConformalLogFactor
  rw [show 2 * ((1 / 2 : ℝ) * Real.log (regularizedConformalCoefficient a f ε z)) =
      Real.log (regularizedConformalCoefficient a f ε z) by ring]
  exact Real.exp_log (regularizedConformalCoefficient_pos ha hε)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exp_two_regularizedConformalLogFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exp_two_regularizedConformalLogFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exp_two_regularizedConformalLogFactor ``Submission.DifferentialGeometry.Analysis.exp_two_regularizedConformalLogFactor



theorem laplacian_regularizedConformalLogFactor {a f : ℂ → ℝ} {z : ℂ}
    (ha : ContDiffAt ℝ 2 a z) (hf : ContDiffAt ℝ 2 f z) (han : 0 ≤ a z)
    {ε : ℝ} (hε : ε ≠ 0) :
    Laplacian.laplacian (regularizedConformalLogFactor a f ε) z =
      (1 / 2 : ℝ) * Laplacian.laplacian
        (fun q => Real.log (regularizedConformalCoefficient a f ε q)) z := by
  have hc : ContDiffAt ℝ 2 (regularizedConformalCoefficient a f ε) z :=
    ha.add (contDiffAt_const.mul ((contDiffAt_const.mul hf).exp))
  have hl := hc.log (regularizedConformalCoefficient_pos (f := f) han hε).ne'
  change Laplacian.laplacian ((1 / 2 : ℝ) •
    (fun q => Real.log (regularizedConformalCoefficient a f ε q))) z = _
  exact _root_.InnerProductSpace.laplacian_smul (1 / 2 : ℝ) hl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.laplacian_regularizedConformalLogFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.laplacian_regularizedConformalLogFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.laplacian_regularizedConformalLogFactor ``Submission.DifferentialGeometry.Analysis.laplacian_regularizedConformalLogFactor


theorem neg_half_laplacian_log_const_mul_exp {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 f z) {c : ℝ} (hc : c ≠ 0) :
    -(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (c * Real.exp (2 * f q))) z =
      -Laplacian.laplacian f z := by
  have he : (fun q => Real.log (c * Real.exp (2 * f q))) =
      (fun q => Real.log c + 2 * f q) := by
    funext q
    rw [Real.log_mul hc (Real.exp_ne_zero _), Real.log_exp]
  rw [he]
  change -(1 / 2 : ℝ) * Laplacian.laplacian
    ((fun _ : ℂ => Real.log c) + (2 : ℝ) • f) z = _
  erw [contDiffAt_const.laplacian_add (hf.const_smul (2 : ℝ)), _root_.InnerProductSpace.laplacian_const,
    _root_.InnerProductSpace.laplacian_smul (2 : ℝ) hf]
  change -(1 / 2 : ℝ) * (0 + 2 * Laplacian.laplacian f z) = _
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.neg_half_laplacian_log_const_mul_exp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.neg_half_laplacian_log_const_mul_exp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.neg_half_laplacian_log_const_mul_exp ``Submission.DifferentialGeometry.Analysis.neg_half_laplacian_log_const_mul_exp



theorem regularizedConformal_curvature_at_zero {a f : ℂ → ℝ} {z : ℂ}
    (ha : ContDiffAt ℝ 2 a z) (hf : ContDiffAt ℝ 2 f z)
    (han : ∀ᶠ q in 𝓝 z, 0 ≤ a q) (ha0 : a z = 0) {ε : ℝ} (hε : ε ≠ 0) :
    -(1 / 2 : ℝ) * Laplacian.laplacian
        (fun q => Real.log (regularizedConformalCoefficient a f ε q)) z =
      -Laplacian.laplacian f z - Laplacian.laplacian a z / (2 * ε ^ 2 * Real.exp (2 * f z)) := by
  have hb : ContDiffAt ℝ 2 (fun q => ε ^ 2 * Real.exp (2 * f q)) z :=
    contDiffAt_const.mul ((contDiffAt_const.mul hf).exp)
  simp only [regularizedConformalCoefficient]
  rw [neg_half_laplacian_log_add_at_zero ha hb han ha0 (by positivity),
    neg_half_laplacian_log_const_mul_exp hf (pow_ne_zero 2 hε)]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.regularizedConformal_curvature_at_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.regularizedConformal_curvature_at_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.regularizedConformal_curvature_at_zero ``Submission.DifferentialGeometry.Analysis.regularizedConformal_curvature_at_zero



theorem regularizedConformal_curvature_le {a f : ℂ → ℝ} {z : ℂ}
    (ha : ContDiffAt ℝ 2 a z) (hf : ContDiffAt ℝ 2 f z)
    (han : ∀ᶠ q in 𝓝 z, 0 ≤ a q) {ε : ℝ} (hε : ε ≠ 0) :
    -(1 / 2 : ℝ) * Laplacian.laplacian
        (fun q => Real.log (regularizedConformalCoefficient a f ε q)) z ≤
      (if a z = 0 then 0 else regularizedConformalWeight a f ε z *
        (-(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (a q)) z)) +
      (1 - regularizedConformalWeight a f ε z) * (-Laplacian.laplacian f z) := by
  have hb : ContDiffAt ℝ 2 (fun q => ε ^ 2 * Real.exp (2 * f q)) z :=
    contDiffAt_const.mul ((contDiffAt_const.mul hf).exp)
  have h := neg_half_laplacian_log_add_le_nonnegative ha hb han
    (by positivity : 0 < ε ^ 2 * Real.exp (2 * f z))
  rw [neg_half_laplacian_log_const_mul_exp hf (pow_ne_zero 2 hε)] at h
  have hw : ε ^ 2 * Real.exp (2 * f z) / (a z + ε ^ 2 * Real.exp (2 * f z)) =
      1 - regularizedConformalWeight a f ε z := by
    have hp := (regularizedConformalCoefficient_pos (f := f) han.self_of_nhds hε).ne'
    dsimp [regularizedConformalWeight, regularizedConformalCoefficient] at hp ⊢
    field_simp
    ring
  rw [hw] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.regularizedConformal_curvature_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.regularizedConformal_curvature_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.regularizedConformal_curvature_le ``Submission.DifferentialGeometry.Analysis.regularizedConformal_curvature_le

end DifferentialGeometry.Analysis
