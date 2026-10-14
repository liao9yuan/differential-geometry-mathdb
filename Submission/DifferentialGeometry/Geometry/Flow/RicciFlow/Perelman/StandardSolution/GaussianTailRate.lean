import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.OriginalVolumeSplit
import Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.Convolution.Lp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean
open scoped _root_.ENNReal _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow

def reducedSourceGaussianTailRate (n : ℕ) : ℝ :=
  100 * (1 + ∫ y : EuclideanSpace ℝ (Fin n),
    ‖y‖ ^ 2 * (((Real.pi : ℝ) ^ ((n : ℝ) / 2))⁻¹ * Real.exp (-‖y‖ ^ 2)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reducedSourceGaussianTailRate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reducedSourceGaussianTailRate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reducedSourceGaussianTailRate ``Submission.DifferentialGeometry.PDE.RicciFlow.reducedSourceGaussianTailRate

theorem reducedSourceGaussianTailRate_pos (n : ℕ) :
    0 < reducedSourceGaussianTailRate n := by
  have hmoment : 0 ≤ ∫ y : EuclideanSpace ℝ (Fin n),
      ‖y‖ ^ 2 * (((Real.pi : ℝ) ^ ((n : ℝ) / 2))⁻¹ * Real.exp (-‖y‖ ^ 2)) :=
    _root_.MeasureTheory.integral_nonneg (fun y ↦ mul_nonneg (sq_nonneg ‖y‖)
      (mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg Real.pi_pos.le _))
        (Real.exp_pos _).le))
  unfold reducedSourceGaussianTailRate
  linarith only [hmoment]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reducedSourceGaussianTailRate_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reducedSourceGaussianTailRate_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reducedSourceGaussianTailRate_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.reducedSourceGaussianTailRate_pos

private theorem reducedSourceGaussian_secondMoment_integrable (n : ℕ) [NeZero n] :
    _root_.MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin n) ↦
      ‖y‖ ^ 2 * (((Real.pi : ℝ) ^ ((n : ℝ) / 2))⁻¹ * Real.exp (-‖y‖ ^ 2))) := by
  have h := gaussMoment_int (V := EuclideanSpace ℝ (Fin n)) 2 (a := 1) zero_lt_one
  apply (h.const_mul (((Real.pi : ℝ) ^ ((n : ℝ) / 2))⁻¹)).congr
  filter_upwards [] with y
  simp only [neg_one_mul]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.reducedSourceGaussian_secondMoment_integrable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.reducedSourceGaussian_secondMoment_integrable target :: scope.openDecls } }

theorem reducedSourceGaussianTail_le_rate_mul (n : ℕ) [NeZero n]
    (eps : ℝ) (heps : 0 < eps) :
    reducedSourceGaussianTail n (1 / (10 * Real.sqrt eps)) ≤
      ENNReal.ofReal (reducedSourceGaussianTailRate n * eps) := by
  let V := EuclideanSpace ℝ (Fin n)
  let d : V → ℝ := fun y ↦
    ((Real.pi : ℝ) ^ ((n : ℝ) / 2))⁻¹ * Real.exp (-‖y‖ ^ 2)
  let f : V → ℝ := fun y ↦ ‖y‖ ^ 2 * d y
  let A : Set V := {y | 1 / (10 * Real.sqrt eps) < ‖y‖}
  have hd : ∀ y : V, 0 ≤ d y := fun y ↦
    mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg Real.pi_pos.le _))
      (Real.exp_pos _).le
  have hf : ∀ y : V, 0 ≤ f y := fun y ↦ mul_nonneg (sq_nonneg ‖y‖) (hd y)
  have hfint : _root_.MeasureTheory.Integrable f := reducedSourceGaussian_secondMoment_integrable n
  have hscaled : _root_.MeasureTheory.Integrable (fun y : V ↦ (100 * eps) * f y) :=
    hfint.const_mul (100 * eps)
  have hA : MeasurableSet A :=
    measurableSet_lt measurable_const continuous_norm.measurable
  have hpoint : ∀ y ∈ A, d y ≤ (100 * eps) * f y := by
    intro y hy
    have hden : 0 < 10 * Real.sqrt eps := by positivity
    have hprod : 1 < ‖y‖ * (10 * Real.sqrt eps) := (div_lt_iff₀ hden).mp hy
    have hunit : 1 ≤ 100 * eps * ‖y‖ ^ 2 := by
      calc
        1 ≤ (‖y‖ * (10 * Real.sqrt eps)) ^ 2 := by
          simpa only [one_pow] using
            (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
              (mul_nonneg (norm_nonneg y) hden.le)).mpr hprod.le
        _ = 100 * eps * ‖y‖ ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt heps.le]
          ring
    calc
      d y = 1 * d y := (one_mul _).symm
      _ ≤ (100 * eps * ‖y‖ ^ 2) * d y := mul_le_mul_of_nonneg_right hunit (hd y)
      _ = (100 * eps) * f y := by dsimp only [f]; ring
  have htail : reducedSourceGaussianTail n (1 / (10 * Real.sqrt eps)) ≤
      ENNReal.ofReal ((100 * eps) * ∫ y : V, f y) := by
    calc
      reducedSourceGaussianTail n (1 / (10 * Real.sqrt eps)) =
          ∫⁻ y : V in A, ENNReal.ofReal (d y) := rfl
      _ ≤ ∫⁻ y : V in A, ENNReal.ofReal ((100 * eps) * f y) :=
        _root_.MeasureTheory.setLIntegral_mono' hA (fun y hy ↦ ENNReal.ofReal_le_ofReal (hpoint y hy))
      _ ≤ ∫⁻ y : V, ENNReal.ofReal ((100 * eps) * f y) := by
        simpa using _root_.MeasureTheory.lintegral_mono_set (_root_.Set.subset_univ A)
      _ = ENNReal.ofReal (∫ y : V, (100 * eps) * f y) :=
        (_root_.MeasureTheory.ofReal_integral_eq_lintegral_ofReal hscaled
          (_root_.MeasureTheory.ae_of_all _ (fun y ↦ mul_nonneg (by positivity) (hf y)))).symm
      _ = ENNReal.ofReal ((100 * eps) * ∫ y : V, f y) := by
        rw [_root_.MeasureTheory.integral_const_mul]
  apply htail.trans
  apply ENNReal.ofReal_le_ofReal
  change (100 * eps) * (∫ y : V, f y) ≤
    (100 * (1 + ∫ y : V, f y)) * eps
  nlinarith only [heps]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.reducedSourceGaussianTail_le_rate_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.reducedSourceGaussianTail_le_rate_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.reducedSourceGaussianTail_le_rate_mul ``Submission.DifferentialGeometry.PDE.RicciFlow.reducedSourceGaussianTail_le_rate_mul

end DifferentialGeometry.PDE.RicciFlow

end
