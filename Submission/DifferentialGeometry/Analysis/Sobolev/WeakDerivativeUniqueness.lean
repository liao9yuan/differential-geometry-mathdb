import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.LpSpace.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev

theorem ae_eq_of_integral_contDiff_mul_eq_on
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : _root_.MeasureTheory.Measure E} {S : Set E} (hS : IsOpen S) (hμS : ∀ᵐ x ∂μ, x ∈ S)
    {f g : E → ℝ} (hf : _root_.MeasureTheory.LocallyIntegrable f μ) (hg : _root_.MeasureTheory.LocallyIntegrable g μ)
    (hfg : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ S → (∫ x, f x * φ x ∂μ) = ∫ x, g x * φ x ∂μ) :
    f =ᵐ[μ] g := by
  have hz : ∀ᵐ x ∂μ, x ∈ S → (f - g) x = 0 := by
    apply hS.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hf.sub hg).locallyIntegrableOn S)
    intro φ hφ hφc hφs
    have hi := hf.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
    have hj := hg.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
    simp only [smul_eq_mul] at hi hj
    simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
    simp_rw [mul_comm (φ _)]
    rw [_root_.MeasureTheory.integral_sub hi hj, hfg φ hφ hφc hφs, sub_self]
  filter_upwards [hz, hμS] with x hx hxs
  exact sub_eq_zero.mp (hx hxs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.ae_eq_of_integral_contDiff_mul_eq_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.ae_eq_of_integral_contDiff_mul_eq_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.ae_eq_of_integral_contDiff_mul_eq_on ``Submission.DifferentialGeometry.Analysis.Sobolev.ae_eq_of_integral_contDiff_mul_eq_on

theorem lp_eq_of_integral_contDiff_mul_eq_on
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : _root_.MeasureTheory.Measure E} [_root_.MeasureTheory.IsLocallyFiniteMeasure μ] {S : Set E}
    (hS : IsOpen S) (hμS : ∀ᵐ x ∂μ, x ∈ S)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f g : _root_.MeasureTheory.Lp ℝ p μ}
    (hfg : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ S → (∫ x, f x * φ x ∂μ) = ∫ x, g x * φ x ∂μ) : f = g := by
  apply Lp.ext
  exact ae_eq_of_integral_contDiff_mul_eq_on hS hμS
    ((Lp.memLp f).locallyIntegrable hp) ((Lp.memLp g).locallyIntegrable hp) hfg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.lp_eq_of_integral_contDiff_mul_eq_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.lp_eq_of_integral_contDiff_mul_eq_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.lp_eq_of_integral_contDiff_mul_eq_on ``Submission.DifferentialGeometry.Analysis.Sobolev.lp_eq_of_integral_contDiff_mul_eq_on

theorem lp_eq_of_weak_deriv_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : _root_.MeasureTheory.Measure E} [_root_.MeasureTheory.IsLocallyFiniteMeasure μ] {S : Set E}
    (hS : IsOpen S) (hμS : ∀ᵐ x ∂μ, x ∈ S)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {U : E → ℝ} {R R' : _root_.MeasureTheory.Lp ℝ p μ} (v : E)
    (hR : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ S → (∫ x, U x * fderiv ℝ φ x v ∂μ) = -∫ x, R x * φ x ∂μ)
    (hR' : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ S → (∫ x, U x * fderiv ℝ φ x v ∂μ) = -∫ x, R' x * φ x ∂μ) :
    R = R' := by
  apply lp_eq_of_integral_contDiff_mul_eq_on hS hμS hp
  intro φ hφ hφc hφs
  exact neg_injective ((hR φ hφ hφc hφs).symm.trans (hR' φ hφ hφc hφs))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.lp_eq_of_weak_deriv_integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.lp_eq_of_weak_deriv_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.lp_eq_of_weak_deriv_integral ``Submission.DifferentialGeometry.Analysis.Sobolev.lp_eq_of_weak_deriv_integral

end DifferentialGeometry.Analysis.Sobolev
