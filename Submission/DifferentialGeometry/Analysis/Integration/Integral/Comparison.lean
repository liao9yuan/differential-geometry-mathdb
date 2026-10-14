import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory in
theorem setIntegral_le_of_ae_eq_on_sdiff
    {P : Type*} [MeasurableSpace P] {μ : _root_.MeasureTheory.Measure P} {s t : Set P}
    (hs : MeasurableSet s) (hst : s ⊆ t) {f g : P → ℝ}
    (hf : _root_.MeasureTheory.IntegrableOn f t μ) (hg : _root_.MeasureTheory.IntegrableOn g t μ)
    (hfg : f =ᵐ[μ.restrict (t \ s)] g)
    (hle : (∫ x in t, f x ∂μ) ≤ ∫ x in t, g x ∂μ) :
    (∫ x in s, f x ∂μ) ≤ ∫ x in s, g x ∂μ := by
  have hdiff := _root_.MeasureTheory.integral_congr_ae hfg
  rw [_root_.MeasureTheory.setIntegral_sdiff hs hf hst, _root_.MeasureTheory.setIntegral_sdiff hs hg hst] at hdiff
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.setIntegral_le_of_ae_eq_on_sdiff then
    throwError "Refusing to shadow existing declaration MeasureTheory.setIntegral_le_of_ae_eq_on_sdiff"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.setIntegral_le_of_ae_eq_on_sdiff ``Submission.MeasureTheory.setIntegral_le_of_ae_eq_on_sdiff

end MeasureTheory

end

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory

namespace intervalIntegral
open _root_.intervalIntegral

open _root_.intervalIntegral in
theorem integral_ge_of_mul_sq_le {a b C : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ} (hint : IntervalIntegrable f _root_.MeasureTheory.MeasureSpace.volume a b)
    (hlower : ∀ t ∈ _root_.Set.Ioo a b, C * t ^ 2 ≤ f t) :
    (C / 3) * (b ^ 3 - a ^ 3) ≤ ∫ t in a..b, f t := by
  have hpoly : IntervalIntegrable (fun t : ℝ => C * t ^ 2) _root_.MeasureTheory.MeasureSpace.volume a b :=
    (by fun_prop : Continuous (fun t : ℝ => C * t ^ 2)).intervalIntegrable _ _
  have hle := _root_.intervalIntegral.integral_mono_on_of_le_Ioo hab hpoly hint hlower
  have heq : (∫ t in a..b, C * t ^ 2) = (C / 3) * (b ^ 3 - a ^ 3) := by
    rw [_root_.intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  rwa [heq] at hle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `intervalIntegral.integral_ge_of_mul_sq_le then
    throwError "Refusing to shadow existing declaration intervalIntegral.integral_ge_of_mul_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `intervalIntegral.integral_ge_of_mul_sq_le ``Submission.intervalIntegral.integral_ge_of_mul_sq_le

end intervalIntegral
