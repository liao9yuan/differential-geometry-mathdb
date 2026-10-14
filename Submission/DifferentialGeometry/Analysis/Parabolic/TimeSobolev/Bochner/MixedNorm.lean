import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

theorem timeL2_coeFn_ae_eq_of_eq
    {T : ℝ} {X : Type*} [NormedAddCommGroup X] {f g : timeL2 X T} (h : f = g) :
    ⇑f =ᵐ[timeMeasure T] ⇑g := by
  cases h
  exact Filter.EventuallyEq.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeL2_coeFn_ae_eq_of_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeL2_coeFn_ae_eq_of_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeL2_coeFn_ae_eq_of_eq ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeL2_coeFn_ae_eq_of_eq

theorem timeL2_norm_le_of_ae_mixed_bound
    {T : ℝ} {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z] (h : timeL2 X T) (p : timeL2 Y T) (q : timeL2 Z T) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ᵐ t ∂(timeMeasure T), ‖h t‖ ≤ A * ‖p t‖ + B * ‖q t‖) :
    ‖h‖ ≤ A * ‖p‖ + B * ‖q‖ := by
  set Pf : ℝ → ℝ := fun t => ‖(p : ℝ → Y) t‖ with hPf
  set Qf : ℝ → ℝ := fun t => ‖(q : ℝ → Z) t‖ with hQf
  have hPm : _root_.MeasureTheory.AEStronglyMeasurable Pf (timeMeasure T) :=
    (Lp.aestronglyMeasurable p).norm
  have hQm : _root_.MeasureTheory.AEStronglyMeasurable Qf (timeMeasure T) :=
    (Lp.aestronglyMeasurable q).norm
  have hAPm : _root_.MeasureTheory.AEStronglyMeasurable (A • Pf) (timeMeasure T) := hPm.const_smul A
  have hBQm : _root_.MeasureTheory.AEStronglyMeasurable (B • Qf) (timeMeasure T) := hQm.const_smul B
  have hmono : _root_.MeasureTheory.eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤
      eLpNorm (A • Pf + B • Qf) 2 (timeMeasure T) := by
    refine _root_.MeasureTheory.eLpNorm_mono_ae ?_
    filter_upwards [hbound] with t ht
    have happ : (A • Pf + B • Qf) t = A * ‖p t‖ + B * ‖q t‖ := by
      simp [hPf, hQf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hge : 0 ≤ (A • Pf + B • Qf) t := by
      rw [happ]
      exact add_nonneg (mul_nonneg hA (norm_nonneg _)) (mul_nonneg hB (norm_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg hge, happ]
    exact ht
  have htri : _root_.MeasureTheory.eLpNorm (A • Pf + B • Qf) 2 (timeMeasure T) ≤
      eLpNorm (A • Pf) 2 (timeMeasure T) + _root_.MeasureTheory.eLpNorm (B • Qf) 2 (timeMeasure T) :=
    _root_.MeasureTheory.eLpNorm_add_le hAPm hBQm (by norm_num)
  have hscaleP : _root_.MeasureTheory.eLpNorm (A • Pf) 2 (timeMeasure T) =
      ENNReal.ofReal A * _root_.MeasureTheory.eLpNorm (p : ℝ → Y) 2 (timeMeasure T) := by
    rw [_root_.MeasureTheory.eLpNorm_const_smul, _root_.MeasureTheory.eLpNorm_norm, Real.enorm_eq_ofReal hA]
  have hscaleQ : _root_.MeasureTheory.eLpNorm (B • Qf) 2 (timeMeasure T) =
      ENNReal.ofReal B * _root_.MeasureTheory.eLpNorm (q : ℝ → Z) 2 (timeMeasure T) := by
    rw [_root_.MeasureTheory.eLpNorm_const_smul, _root_.MeasureTheory.eLpNorm_norm, Real.enorm_eq_ofReal hB]
  have hfinal : _root_.MeasureTheory.eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤
      ENNReal.ofReal A * _root_.MeasureTheory.eLpNorm (p : ℝ → Y) 2 (timeMeasure T) +
        ENNReal.ofReal B * _root_.MeasureTheory.eLpNorm (q : ℝ → Z) 2 (timeMeasure T) := by
    calc
      _root_.MeasureTheory.eLpNorm (h : ℝ → X) 2 (timeMeasure T) ≤
          eLpNorm (A • Pf) 2 (timeMeasure T) + _root_.MeasureTheory.eLpNorm (B • Qf) 2 (timeMeasure T) :=
        hmono.trans htri
      _ = _ := by rw [hscaleP, hscaleQ]
  have hp_top : _root_.MeasureTheory.eLpNorm (p : ℝ → Y) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp p).2.ne
  have hq_top : _root_.MeasureTheory.eLpNorm (q : ℝ → Z) 2 (timeMeasure T) ≠ ⊤ := (Lp.memLp q).2.ne
  have hnormh : ‖h‖ = (_root_.MeasureTheory.eLpNorm (h : ℝ → X) 2 (timeMeasure T)).toReal := rfl
  have hnormp : ‖p‖ = (_root_.MeasureTheory.eLpNorm (p : ℝ → Y) 2 (timeMeasure T)).toReal := rfl
  have hnormq : ‖q‖ = (_root_.MeasureTheory.eLpNorm (q : ℝ → Z) 2 (timeMeasure T)).toReal := rfl
  have hrhs_ne : ENNReal.ofReal A * _root_.MeasureTheory.eLpNorm (p : ℝ → Y) 2 (timeMeasure T) +
      ENNReal.ofReal B * _root_.MeasureTheory.eLpNorm (q : ℝ → Z) 2 (timeMeasure T) ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq_top⟩
  rw [hnormh, hnormp, hnormq]
  refine le_trans (ENNReal.toReal_mono hrhs_ne hfinal) ?_
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp_top)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq_top),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA,
    ENNReal.toReal_ofReal hB]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeL2_norm_le_of_ae_mixed_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeL2_norm_le_of_ae_mixed_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeL2_norm_le_of_ae_mixed_bound ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeL2_norm_le_of_ae_mixed_bound

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
