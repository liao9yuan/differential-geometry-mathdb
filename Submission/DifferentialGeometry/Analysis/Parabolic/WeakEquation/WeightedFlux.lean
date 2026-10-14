import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.MeasureTheory
open scoped _root_.BigOperators

namespace DifferentialGeometry.Analysis.Parabolic

theorem integral_weighted_flux_eq_of_residual_eq_zero
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] {μ : _root_.MeasureTheory.Measure α}
    {u w timeDerivative : α → ℝ} {A : α → ι → ι → ℝ}
    {du df testGradient : ι → α → ℝ}
    (hgradient : ∀ᵐ p ∂μ, ∀ i, du i p = -u p * df i p)
    (htime : _root_.MeasureTheory.Integrable (fun p => w p * u p * timeDerivative p) μ)
    (hflux : ∀ j, _root_.MeasureTheory.Integrable
      (fun p => (∑ i, w p * A p i j * du i p) * testGradient j p) μ)
    (hresidual : (∫ p, w p * u p *
      (timeDerivative p + ∑ j, ∑ i, A p i j * df i p * testGradient j p) ∂μ) = 0) :
    (∫ p, w p * u p * timeDerivative p ∂μ) =
      ∑ j, ∫ p, (∑ i, w p * A p i j * du i p) * testGradient j p ∂μ := by
  have hsum : _root_.MeasureTheory.Integrable
      (fun p => ∑ j, (∑ i, w p * A p i j * du i p) * testGradient j p) μ :=
    _root_.MeasureTheory.integrable_finsetSum Finset.univ fun j _ => hflux j
  have hconvert :
      (fun p => w p * u p *
        (timeDerivative p + ∑ j, ∑ i, A p i j * df i p * testGradient j p)) =ᵐ[μ]
      fun p => w p * u p * timeDerivative p -
        ∑ j, (∑ i, w p * A p i j * du i p) * testGradient j p := by
    filter_upwards [hgradient] with p hp
    have hsum_eq :
        (∑ j, (∑ i, w p * A p i j * du i p) * testGradient j p) =
          -(w p * u p * (∑ j, ∑ i, A p i j * df i p * testGradient j p)) := by
      simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [hp i]
      ring
    rw [hsum_eq]
    ring
  have hzero :
      (∫ p, w p * u p * timeDerivative p -
        ∑ j, (∑ i, w p * A p i j * du i p) * testGradient j p ∂μ) = 0 :=
    (_root_.MeasureTheory.integral_congr_ae hconvert).symm.trans hresidual
  rw [_root_.MeasureTheory.integral_sub htime hsum,
    _root_.MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hflux j)] at hzero
  exact sub_eq_zero.mp hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.integral_weighted_flux_eq_of_residual_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.integral_weighted_flux_eq_of_residual_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.integral_weighted_flux_eq_of_residual_eq_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.integral_weighted_flux_eq_of_residual_eq_zero

end DifferentialGeometry.Analysis.Parabolic
