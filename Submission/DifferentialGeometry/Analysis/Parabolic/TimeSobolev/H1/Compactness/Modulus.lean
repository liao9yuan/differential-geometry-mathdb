import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.ENNReal _root_.NNReal _root_.Topology

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {T : ℝ}

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem integral_norm_Icc_le (f : timeL2 X T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ s in Set.Icc (0 : ℝ) t, ‖f s‖ ≤ Real.sqrt t * ‖f‖ := by
  have hle_meas : timeMeasure t ≤ timeMeasure T := by
    unfold timeMeasure
    exact Measure.restrict_mono (_root_.Set.Icc_subset_Icc le_rfl ht.2) le_rfl
  have haem : _root_.MeasureTheory.AEStronglyMeasurable (fun s => f s) (timeMeasure t) :=
    (Lp.aestronglyMeasurable f).mono_measure hle_meas
  have hmono2 : _root_.MeasureTheory.eLpNorm (fun s => f s) 2 (timeMeasure t)
      ≤ _root_.MeasureTheory.eLpNorm (fun s => f s) 2 (timeMeasure T) :=
    _root_.MeasureTheory.eLpNorm_mono_measure _ hle_meas
  have hne2 : _root_.MeasureTheory.eLpNorm (fun s => f s) 2 (timeMeasure t) ≠ ∞ :=
    (hmono2.trans_lt (Lp.eLpNorm_ne_top f).lt_top).ne
  have hint : ∫ s in Set.Icc (0 : ℝ) t, ‖f s‖
      = (_root_.MeasureTheory.eLpNorm (fun s => f s) 1 (timeMeasure t)).toReal := by
    rw [show (∫ s in Set.Icc (0 : ℝ) t, ‖f s‖) = ∫ s, ‖f s‖ ∂(timeMeasure t) from rfl,
      _root_.MeasureTheory.integral_norm_eq_lintegral_enorm haem, _root_.MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
  have hholder := _root_.MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := timeMeasure t) (p := 1) (q := 2) (by norm_num) haem
  have hfin : _root_.MeasureTheory.eLpNorm (fun s => f s) 2 (timeMeasure t)
      * timeMeasure t Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ∞ := by
    refine ENNReal.mul_ne_top hne2 ?_
    rw [timeMeasure_univ]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by finiteness)
  rw [hint]
  refine le_trans (ENNReal.toReal_mono hfin hholder) ?_
  rw [ENNReal.toReal_mul, timeMeasure_univ,
    show (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) by norm_num,
    toReal_ofReal_rpow_half, mul_comm (Real.sqrt t) ‖f‖]
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg t)
  rw [Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) hmono2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_norm_Icc_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_norm_Icc_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_norm_Icc_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_norm_Icc_le

namespace timeH1

omit [CompleteSpace X] in
theorem norm_toFun_sub_initial_le (u : timeH1 X T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ‖u.toFun t - u.initial‖ ≤ Real.sqrt t * ‖u.deriv‖ := by
  have h0t : (0 : ℝ) ≤ t := ht.1
  have hsub : u.toFun t - u.initial = ∫ s in (0 : ℝ)..t, u.deriv s := by
    simp only [toFun_apply]; abel
  rw [hsub, intervalIntegral.integral_of_le h0t]
  refine le_trans (_root_.MeasureTheory.norm_integral_le_integral_norm _) ?_
  refine le_trans ?_ (TimeSobolev.integral_norm_Icc_le u.deriv ht)
  have hintt : _root_.MeasureTheory.IntegrableOn (fun s => ‖u.deriv s‖) (Set.Icc (0 : ℝ) t) volume :=
    ((TimeSobolev.integrableOn u.deriv).mono_set (_root_.Set.Icc_subset_Icc le_rfl ht.2)).norm
  refine _root_.MeasureTheory.setIntegral_mono_set hintt ?_ ?_
  · filter_upwards with s using norm_nonneg _
  · exact LE.le.eventuallyLE _root_.Set.Ioc_subset_Icc_self

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toFun_sub_initial_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toFun_sub_initial_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toFun_sub_initial_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_toFun_sub_initial_le

omit [CompleteSpace X] in
theorem state_le_of_sqrt_floor (u : timeH1 X T) (hinit : u.initial = 0) {B : ℝ}
    (hfloor : Real.sqrt T * ‖u.deriv‖ ≤ B) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ‖u.toFun t‖ ≤ B := by
  intro t ht
  calc ‖u.toFun t‖
      = ‖u.toFun t - u.initial‖ := by rw [hinit, sub_zero]
    _ ≤ Real.sqrt t * ‖u.deriv‖ := u.norm_toFun_sub_initial_le ht
    _ ≤ Real.sqrt T * ‖u.deriv‖ :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ht.2) (norm_nonneg _)
    _ ≤ B := hfloor

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.state_le_of_sqrt_floor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.state_le_of_sqrt_floor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.state_le_of_sqrt_floor ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.state_le_of_sqrt_floor

omit [CompleteSpace X] in
theorem norm_le_of_ae_le (u : timeH1 X T) (hT : 0 < T) {R : ℝ}
    (hae : ∀ᵐ t ∂timeMeasure T, ‖u.toFun t‖ ≤ R) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ‖u.toFun t‖ ≤ R := by
  intro t ht
  have hnorm_cont : ContinuousOn (fun s => ‖u.toFun s‖) (Set.Icc (0 : ℝ) T) :=
    continuous_norm.comp_continuousOn u.continuousOn_toFun
  have hmin_cont : ContinuousOn (fun s => _root_.Min.min ‖u.toFun s‖ R) (Set.Icc (0 : ℝ) T) :=
    hnorm_cont.inf continuousOn_const
  have hmin : (fun s => _root_.Min.min ‖u.toFun s‖ R)
      =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) T)] fun s => ‖u.toFun s‖ := by
    filter_upwards [hae] with s hs using min_eq_left hs
  exact min_eq_left_iff.mp
    (MeasureTheory.Measure.eqOn_Icc_of_ae_eq (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)) hT.ne hmin
      hmin_cont hnorm_cont ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_le_of_ae_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_le_of_ae_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_le_of_ae_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.norm_le_of_ae_le

end timeH1

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry
