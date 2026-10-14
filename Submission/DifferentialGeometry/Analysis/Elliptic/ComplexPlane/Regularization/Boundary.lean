import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Regularization.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Filter
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis


theorem fderiv_regularizedConformalCoefficient {a f : ℂ → ℝ} {z : ℂ}
    (ha : DifferentiableAt ℝ a z) (hf : DifferentiableAt ℝ f z) (ε : ℝ) (v : ℂ) :
    fderiv ℝ (regularizedConformalCoefficient a f ε) z v =
      fderiv ℝ a z v + 2 * ε ^ 2 * Real.exp (2 * f z) * fderiv ℝ f z v := by
  have h := (ha.hasFDerivAt.add
    (((hf.hasFDerivAt.const_mul 2).exp).const_mul (ε ^ 2))).fderiv
  change fderiv ℝ (regularizedConformalCoefficient a f ε) z = _ at h
  rw [h]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.fderiv_regularizedConformalCoefficient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.fderiv_regularizedConformalCoefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.fderiv_regularizedConformalCoefficient ``Submission.DifferentialGeometry.Analysis.fderiv_regularizedConformalCoefficient





theorem regularizedConformal_boundary_density {a f : ℂ → ℝ} {z v : ℂ}
    (ha : DifferentiableAt ℝ a z) (hf : DifferentiableAt ℝ f z)
    (han : ∀ᶠ q in 𝓝 z, 0 ≤ a q) (hfν : fderiv ℝ f z v = -1)
    {ε : ℝ} (hε : ε ≠ 0) :
    1 + (1 / 2 : ℝ) * fderiv ℝ
        (fun q => Real.log (regularizedConformalCoefficient a f ε q)) z v =
      regularizedConformalWeight a f ε z *
        (1 + (1 / 2 : ℝ) * fderiv ℝ (fun q => Real.log (a q)) z v) := by
  have hp := (regularizedConformalCoefficient_pos (f := f) han.self_of_nhds hε).ne'
  have hdiff : DifferentiableAt ℝ (regularizedConformalCoefficient a f ε) z :=
    ha.add ((hf.const_mul 2).exp.const_mul (ε ^ 2))
  rw [fderiv.log hdiff hp]
  simp only [_root_.smul_apply, smul_eq_mul]
  rw [fderiv_regularizedConformalCoefficient ha hf, hfν]
  by_cases ha0 : a z = 0
  · have hm : IsLocalMin a z := by
      change ∀ᶠ q in 𝓝 z, a z ≤ a q
      simpa only [ha0] using han
    rw [hm.fderiv_eq_zero]
    dsimp [regularizedConformalWeight, regularizedConformalCoefficient] at hp ⊢
    simp only [ha0, zero_add, zero_div, _root_.MulZeroClass.zero_mul, _root_.zero_apply]
    field_simp
    ring
  · rw [fderiv.log ha ha0]
    simp only [_root_.smul_apply, smul_eq_mul]
    dsimp [regularizedConformalWeight, regularizedConformalCoefficient] at hp ⊢
    field_simp
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.regularizedConformal_boundary_density then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.regularizedConformal_boundary_density"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.regularizedConformal_boundary_density ``Submission.DifferentialGeometry.Analysis.regularizedConformal_boundary_density

end DifferentialGeometry.Analysis
