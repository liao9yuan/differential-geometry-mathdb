import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Calculus.ContDiff.Operations

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Filter
open scoped _root_.Topology _root_.Convolution _root_.ContDiff

namespace DifferentialGeometry.Analysis



theorem abs_log_le_self_add_inv {r : ℝ} (hr : 0 ≤ r) : |Real.log r| ≤ r + r⁻¹ := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  have h₁ := Real.log_le_sub_one_of_pos hr
  have h₂ := Real.log_le_sub_one_of_pos (inv_pos.mpr hr)
  rw [Real.log_inv] at h₂
  apply abs_le.mpr
  constructor <;> linarith [inv_pos.mpr hr]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.abs_log_le_self_add_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.abs_log_le_self_add_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.abs_log_le_self_add_inv ``Submission.DifferentialGeometry.Analysis.abs_log_le_self_add_inv




theorem locallyIntegrable_log_norm_complex :
    LocallyIntegrable (fun z : ℂ => Real.log ‖z‖) volume := by
  have hinv : _root_.MeasureTheory.LocallyIntegrable (fun z : ℂ => ‖z‖⁻¹) volume := by
    apply _root_.MeasureTheory.locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1)
      (by simp [Complex.finrank_real_complex]) (by norm_num [Complex.finrank_real_complex])
    · exact Eventually.of_forall fun z => by simp [Real.rpow_neg_one]
    · fun_prop
  have hnorm : _root_.MeasureTheory.LocallyIntegrable (fun z : ℂ => ‖z‖) volume := continuous_norm.locallyIntegrable
  rw [_root_.MeasureTheory.locallyIntegrable_iff] at hinv hnorm ⊢
  intro K hK
  apply ((hnorm K hK).add (hinv K hK)).mono'
  · exact (Real.measurable_log.comp measurable_norm).aestronglyMeasurable
  · exact Eventually.of_forall fun z => by
      change |Real.log ‖z‖| ≤ ‖z‖ + ‖z‖⁻¹
      exact abs_log_le_self_add_inv (norm_nonneg z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.locallyIntegrable_log_norm_complex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.locallyIntegrable_log_norm_complex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.locallyIntegrable_log_norm_complex ``Submission.DifferentialGeometry.Analysis.locallyIntegrable_log_norm_complex



def logarithmicPotential (κ : ℂ → ℝ) (z : ℂ) : ℝ :=
  -(1 / (2 * Real.pi)) * ∫ w : ℂ, κ w * Real.log ‖z - w‖

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.logarithmicPotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.logarithmicPotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.logarithmicPotential ``Submission.DifferentialGeometry.Analysis.logarithmicPotential




theorem contDiff_logarithmicPotential {κ : ℂ → ℝ}
    (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ) :
    ContDiff ℝ ∞ (logarithmicPotential κ) := by
  have h := hc.contDiff_convolution_left (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℂ))
    (ContinuousLinearMap.mul ℝ ℝ) hκ
    locallyIntegrable_log_norm_complex
  exact contDiff_const.mul h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiff_logarithmicPotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiff_logarithmicPotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiff_logarithmicPotential ``Submission.DifferentialGeometry.Analysis.contDiff_logarithmicPotential

end DifferentialGeometry.Analysis
