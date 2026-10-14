import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecificLimits.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.Analysis

theorem exists_pos_abs_integral_ball_lt
    {e : EuclideanSpace ℝ (Fin 2) → ℝ}
    (he : _root_.MeasureTheory.IntegrableOn e (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ R ∈ _root_.Set.Ioc (0 : ℝ) δ,
      |∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R, e x| < ε := by
  let μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.ball 0 1)
  have hvolume : _root_.Filter.Tendsto
      (fun R : ℝ => _root_.MeasureTheory.MeasureSpace.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R))
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    have hpow := ENNReal.Tendsto.pow (n := 2) (ENNReal.continuous_ofReal.tendsto (0 : ℝ))
    have hmul := ENNReal.Tendsto.mul_const
      (b := ENNReal.ofReal Real.pi) hpow (Or.inr ENNReal.ofReal_ne_top)
    simpa only [EuclideanSpace.volume_ball_fin_two, ENNReal.ofReal_zero,
      zero_pow (by decide : 2 ≠ 0), _root_.MulZeroClass.zero_mul] using hmul
  have hmeasure : _root_.Filter.Tendsto
      (fun R : ℝ => μ (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R))
      (𝓝 (0 : ℝ)) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvolume
      (fun _ => bot_le) (fun R => Measure.restrict_apply_le _ _)
  have hint : _root_.MeasureTheory.Integrable e μ := he
  have hlimit := hint.tendsto_setIntegral_nhds_zero hmeasure
  obtain ⟨a, ha, hsmall⟩ := Metric.mem_nhds_iff.mp
    (Metric.tendsto_nhds.mp hlimit ε hε)
  let δ := _root_.Min.min (a / 2) (1 / 2 : ℝ)
  have hδ : 0 < δ := lt_min (half_pos ha) (by norm_num)
  have hδone : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨δ, hδ, hδone, ?_⟩
  intro R hR
  have hRa : R < a :=
    (hR.2.trans (min_le_left _ _)).trans_lt (half_lt_self ha)
  have hRball : R ∈ Metric.ball (0 : ℝ) a := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hR.1] using hRa
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R ⊆ Metric.ball 0 1 :=
    Metric.ball_subset_ball (hR.2.trans hδone.le)
  have hrestrict :
      (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R, e x ∂μ) =
        ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R, e x := by
    change (∫ x, e x ∂(((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2))).restrict
      (Metric.ball 0 1)).restrict (Metric.ball 0 R))) = _
    rw [Measure.restrict_restrict_of_subset hsub]
  have ht : |∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R, e x ∂μ| < ε := by
    simpa only [_root_.Set.mem_ofPred_eq, dist_zero_right, Real.norm_eq_abs] using hsmall hRball
  rwa [hrestrict] at ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_pos_abs_integral_ball_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_pos_abs_integral_ball_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_pos_abs_integral_ball_lt ``Submission.DifferentialGeometry.Analysis.exists_pos_abs_integral_ball_lt


end DifferentialGeometry.Analysis

end

section

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.Analysis

theorem exists_pos_uniform_abs_integral_ball_lt
    {e : EuclideanSpace ℝ (Fin 2) → ℝ}
    (he : _root_.MeasureTheory.IntegrableOn e (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (b : EuclideanSpace ℝ (Fin 2)) (R : ℝ), 0 < R → R ≤ δ →
        Metric.ball b R ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 →
        |∫ x in Metric.ball b R, e x| < ε := by
  let μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2))).restrict (Metric.ball 0 1)
  have hint : _root_.MeasureTheory.Integrable e μ := he
  have hfinite : (∫⁻ x, ENNReal.ofReal ‖e x‖ ∂μ) ≠ ⊤ :=
    ((_root_.MeasureTheory.hasFiniteIntegral_iff_norm e).mp hint.hasFiniteIntegral).ne
  obtain ⟨η, hη, hsmall⟩ := _root_.MeasureTheory.exists_pos_setLIntegral_lt_of_measure_lt hfinite
    (ENNReal.ofReal_pos.mpr hε).ne'
  have hvolume : _root_.Filter.Tendsto
      (fun R : ℝ => _root_.MeasureTheory.MeasureSpace.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R))
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    have hpow := ENNReal.Tendsto.pow (n := 2) (ENNReal.continuous_ofReal.tendsto (0 : ℝ))
    have hmul := ENNReal.Tendsto.mul_const
      (b := ENNReal.ofReal Real.pi) hpow (Or.inr ENNReal.ofReal_ne_top)
    simpa only [EuclideanSpace.volume_ball_fin_two, ENNReal.ofReal_zero,
      zero_pow (by decide : 2 ≠ 0), _root_.MulZeroClass.zero_mul] using hmul
  obtain ⟨a, ha, havolume⟩ := Metric.mem_nhds_iff.mp
    (hvolume.eventually (Iio_mem_nhds hη))
  let δ := _root_.Min.min (a / 2) (1 / 2 : ℝ)
  have hδ : 0 < δ := lt_min (half_pos ha) (by norm_num)
  have hδone : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨δ, hδ, hδone, ?_⟩
  intro b R hR hRδ hsub
  have hRa : R < a :=
    (hRδ.trans (min_le_left _ _)).trans_lt (half_lt_self ha)
  have hRball : R ∈ Metric.ball (0 : ℝ) a := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hR] using hRa
  have hvol : _root_.MeasureTheory.MeasureSpace.volume (Metric.ball b R) < η := by
    have h := havolume hRball
    change _root_.MeasureTheory.MeasureSpace.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R) < η at h
    simpa only [EuclideanSpace.volume_ball_fin_two] using h
  have hμball : μ (Metric.ball b R) < η :=
    (Measure.restrict_apply_le _ _).trans_lt hvol
  have hlin := hsmall (Metric.ball b R) hμball
  have hlinfinite : (∫⁻ x in Metric.ball b R, ENNReal.ofReal ‖e x‖ ∂μ) ≠ ⊤ :=
    (hlin.trans_le le_top).ne
  have hreal : (∫⁻ x in Metric.ball b R, ENNReal.ofReal ‖e x‖ ∂μ).toReal < ε := by
    have h := (ENNReal.toReal_lt_toReal hlinfinite ENNReal.ofReal_ne_top).mpr hlin
    simpa only [ENNReal.toReal_ofReal hε.le] using h
  have hnorm : ‖∫ x in Metric.ball b R, e x ∂μ‖ < ε :=
    (_root_.MeasureTheory.norm_integral_le_lintegral_norm e).trans_lt hreal
  have hrestrict : (∫ x in Metric.ball b R, e x ∂μ) =
      ∫ x in Metric.ball b R, e x := by
    change (∫ x, e x ∂(((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2))).restrict
      (Metric.ball 0 1)).restrict (Metric.ball b R))) = _
    rw [Measure.restrict_restrict_of_subset hsub]
  simpa only [hrestrict, Real.norm_eq_abs] using hnorm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_pos_uniform_abs_integral_ball_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_pos_uniform_abs_integral_ball_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_pos_uniform_abs_integral_ball_lt ``Submission.DifferentialGeometry.Analysis.exists_pos_uniform_abs_integral_ball_lt

end DifferentialGeometry.Analysis

end
