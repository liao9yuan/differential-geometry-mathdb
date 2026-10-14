import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Metric _root_.Filter _root_.Topology _root_.Set _root_.Function
open scoped _root_.ENNReal _root_.NNReal _root_.Convolution _root_.Pointwise _root_.BigOperators

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem eLpNorm_mollifyEps_le
    {ε : ℝ} (hε : 0 < ε) {u : E → ℝ}
    (hu : _root_.MeasureTheory.MemLp u 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) :
    eLpNorm (mollifyEps (d := d) hε u) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤
      eLpNorm u 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
  classical
  have hmem_p : _root_.MeasureTheory.MemLp u (ENNReal.ofReal 2) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
    have h_eq : (ENNReal.ofReal 2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_cast]
      rw [show (2 : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) from by norm_cast]
      exact ENNReal.ofReal_natCast 2
    rw [h_eq]; exact hu
  set ψ : E → ℝ := mollifierEps (d := d) hε with hψ_def
  have hψ_int : ∫ y, ψ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) = 1 := mollifierEps_integral_eq_one hε
  have hψ_nn : ∀ y, 0 ≤ ψ y := mollifierEps_nonneg hε
  have hψ_integrable : _root_.MeasureTheory.Integrable ψ (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := mollifierEps_integrable hε
  have hψ_cont : Continuous ψ := mollifierEps_continuous hε
  have hψ_compact : HasCompactSupport ψ := mollifierEps_compactSupport hε
  set C : ℝ≥0∞ := _root_.MeasureTheory.eLpNorm u 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) with hC_def
  have hu_aestrong : _root_.MeasureTheory.AEStronglyMeasurable u (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := hu.aestronglyMeasurable
  have h_pt_jensen : ∀ x : E,
      ‖(ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) x‖ ^ (2 : ℝ) ≤
      ((fun y => ‖u y‖ ^ (2 : ℝ))
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] ψ) x := by
    intro x
    set h_norm_sq : E → ℝ := fun y => ‖u y‖ ^ (2 : ℝ) with hh_norm_sq_def
    set ρ : E → ℝ≥0∞ := fun y => ENNReal.ofReal (ψ y) with hρ_def
    set ν : _root_.MeasureTheory.Measure E := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).withDensity ρ with hν_def
    have hρ_meas : Measurable ρ := hψ_cont.measurable.ennreal_ofReal
    have hρ_lt_top : ∀ᵐ y ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E), ρ y < ∞ := by
      filter_upwards with y
      simp [ρ]
    have hν_prob : _root_.MeasureTheory.IsProbabilityMeasure ν := by
      refine ⟨?_⟩
      rw [hν_def, _root_.MeasureTheory.withDensity_apply _ MeasurableSet.univ]
      rw [Measure.restrict_univ]
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hψ_integrable
        (Filter.Eventually.of_forall hψ_nn)]
      rw [hψ_int]
      simp
    have hu_local : _root_.MeasureTheory.LocallyIntegrable u (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
      hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hce_u : _root_.MeasureTheory.ConvolutionExistsAt ψ u x
        (ContinuousLinearMap.lsmul ℝ ℝ) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
      hψ_compact.convolutionExists_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hψ_cont hu_local x
    have hconv_ν :
        ((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) x) =
          ∫ y, u (x - y) ∂ν := by
      rw [hν_def]
      rw [integral_withDensity_eq_integral_toReal_smul hρ_meas hρ_lt_top]
      rw [MeasureTheory.convolution_def]
      refine _root_.MeasureTheory.integral_congr_ae ?_
      filter_upwards with y
      simp [ρ, ψ, ContinuousLinearMap.lsmul_apply, smul_eq_mul, hψ_nn y]
    have h_norm_sq_int_vol : _root_.MeasureTheory.Integrable (fun y => (ρ y).toReal * ‖u (x - y)‖)
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
      refine hce_u.integrable.norm.congr ?_
      filter_upwards with y
      simp [ρ, ψ, ContinuousLinearMap.lsmul_apply, smul_eq_mul, hψ_nn y]
    have h_norm_int : _root_.MeasureTheory.Integrable (fun y => ‖u (x - y)‖) ν := by
      exact (MeasureTheory.integrable_withDensity_iff_integrable_smul' hρ_meas hρ_lt_top).2 <| by
        simpa [ρ, ψ, hψ_nn] using h_norm_sq_int_vol
    have hu_sq_local : _root_.MeasureTheory.LocallyIntegrable (fun y => ‖u y‖ ^ (2 : ℝ)) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
      have hh_int : _root_.MeasureTheory.Integrable (fun y => ‖u y‖ ^ (2 : ℝ)) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
        have := hu.integrable_norm_rpow (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        simpa using this
      exact hh_int.locallyIntegrable
    have hce_h : _root_.MeasureTheory.ConvolutionExistsAt ψ h_norm_sq x
        (ContinuousLinearMap.lsmul ℝ ℝ) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
      hψ_compact.convolutionExists_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hψ_cont hu_sq_local x
    have h_rpow_int_vol :
        Integrable (fun y => (ρ y).toReal * ‖u (x - y)‖ ^ (2 : ℝ)) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
      refine hce_h.integrable.congr ?_
      filter_upwards with y
      simp [ρ, ψ, h_norm_sq, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
        hψ_nn y]
    have h_rpow_int : _root_.MeasureTheory.Integrable (fun y => ‖u (x - y)‖ ^ (2 : ℝ)) ν := by
      exact (MeasureTheory.integrable_withDensity_iff_integrable_smul' hρ_meas hρ_lt_top).2 <| by
        simpa [ρ, ψ, hψ_nn] using h_rpow_int_vol
    have hnorm_le_int : ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) x)‖ ≤
        ∫ y, ‖u (x - y)‖ ∂ν := by
      rw [hconv_ν]
      exact MeasureTheory.norm_integral_le_integral_norm _
    have hJensen_ν : (∫ y, ‖u (x - y)‖ ∂ν) ^ (2 : ℝ) ≤ ∫ y, ‖u (x - y)‖ ^ (2 : ℝ) ∂ν := by
      have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => t ^ (2 : ℝ)) :=
        convexOn_rpow (by norm_num : (1 : ℝ) ≤ 2)
      have hcont : ContinuousOn (fun t : ℝ => t ^ (2 : ℝ)) (Set.Ici (0 : ℝ)) :=
        continuousOn_id.rpow_const (fun t _ => Or.inr (by norm_num : (0 : ℝ) ≤ 2))
      have hmem : ∀ᵐ y ∂ν, ‖u (x - y)‖ ∈ Set.Ici (0 : ℝ) := by
        filter_upwards with y
        exact norm_nonneg _
      exact hconv.map_integral_le hcont isClosed_Ici hmem h_norm_int h_rpow_int
    calc
      ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) x)‖ ^ (2 : ℝ)
          ≤ (∫ y, ‖u (x - y)‖ ∂ν) ^ (2 : ℝ) :=
            Real.rpow_le_rpow (norm_nonneg _) hnorm_le_int (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ ∫ y, ‖u (x - y)‖ ^ (2 : ℝ) ∂ν := hJensen_ν
      _ = ∫ y, ψ y * ‖u (x - y)‖ ^ (2 : ℝ) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
            rw [hν_def]
            rw [integral_withDensity_eq_integral_toReal_smul hρ_meas hρ_lt_top]
            refine _root_.MeasureTheory.integral_congr_ae ?_
            filter_upwards with y
            simp [ρ, ψ, hψ_nn y]
      _ = ((fun y => ‖u y‖ ^ (2 : ℝ))
            ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] ψ) x := by
            have hMP : _root_.MeasureTheory.MeasurePreserving (fun y : E => x - y) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)
                (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
              have h_neg : _root_.MeasureTheory.MeasurePreserving (fun t : E => -t) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)
                  (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
                Measure.measurePreserving_neg (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)
              have h_addL : _root_.MeasureTheory.MeasurePreserving (fun t : E => x + t) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)
                  (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
                _root_.MeasureTheory.measurePreserving_add_left (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) x
              have heq : (fun y : E => x - y) = (fun y : E => x + (-y)) := by
                funext y; rw [sub_eq_add_neg]
              rw [heq]; exact h_addL.comp h_neg
            have h_subst : ∫ y, ψ y * ‖u (x - y)‖ ^ (2 : ℝ) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) =
                ∫ t, ψ (x - t) * ‖u (x - (x - t))‖ ^ (2 : ℝ) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
              (hMP.integral_comp (Homeomorph.subLeft x).measurableEmbedding
                (fun y : E => ψ y * ‖u (x - y)‖ ^ (2 : ℝ))).symm
            rw [h_subst]
            have h_rearr : ∀ t : E,
                ψ (x - t) * ‖u (x - (x - t))‖ ^ (2 : ℝ) =
                ‖u t‖ ^ (2 : ℝ) * ψ (x - t) := by
              intro t
              have h_simp : x - (x - t) = t := by abel
              rw [h_simp]
              ring
            rw [_root_.MeasureTheory.convolution_def]
            refine _root_.MeasureTheory.integral_congr_ae ?_
            filter_upwards with t
            rw [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
            exact h_rearr t
  have hu_local : _root_.MeasureTheory.LocallyIntegrable u (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
    hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hu_sq_int : _root_.MeasureTheory.Integrable (fun y => ‖u y‖ ^ (2 : ℝ)) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
    have := hu.integrable_norm_rpow (p := 2) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    simpa using this
  have hconv_cont : Continuous
      (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u :
        E → ℝ) :=
    hψ_compact.continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hψ_cont hu_local
  have hh_convergence_int : _root_.MeasureTheory.Integrable
      ((fun y => ‖u y‖ ^ (2 : ℝ))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] ψ)
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
    hu_sq_int.integrable_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hψ_integrable
  have hpow_int : _root_.MeasureTheory.Integrable
      (fun x => ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) x)‖
        ^ (2 : ℝ)) (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
    refine Integrable.mono' hh_convergence_int ?_ ?_
    · exact (hconv_cont.norm.rpow_const
        (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 2))).aestronglyMeasurable
    · filter_upwards with x
      have h_nn :
          0 ≤ ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) x)‖
            ^ (2 : ℝ) :=
        Real.rpow_nonneg (norm_nonneg _) _
      rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
      exact h_pt_jensen x
  have h_int_le :
      ∫ x, ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) x)‖ ^ (2 : ℝ)
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤
      ∫ x, ((fun y => ‖u y‖ ^ (2 : ℝ))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] ψ) x
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
    refine _root_.MeasureTheory.integral_mono_ae hpow_int hh_convergence_int ?_
    filter_upwards with x
    exact h_pt_jensen x
  have h_convergence_eq :
      ∫ x, ((fun y => ‖u y‖ ^ (2 : ℝ))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] ψ) x
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) =
      ∫ x, ‖u x‖ ^ (2 : ℝ) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
    have h := MeasureTheory.integral_convolution
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))
      (ν := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) hu_sq_int hψ_integrable
    rw [h]
    simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul, hψ_int]
  have hconv_memLp : _root_.MeasureTheory.MemLp (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u : E → ℝ)
      2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by
    refine ⟨hconv_cont.aestronglyMeasurable, ?_⟩
    rw [_root_.MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))
      (f := (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u : E → ℝ))
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    have h_2_toReal : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
    rw [h_2_toReal]
    have h_lint_finite : ∫⁻ x, ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) x)‖ₑ
        ^ (2 : ℝ) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) < ∞ := by
      have h_pt_lint : ∀ x : E,
          ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) x)‖ₑ
            ^ (2 : ℝ) =
          ENNReal.ofReal (‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) x)‖
            ^ (2 : ℝ)) := by
        intro x
        rw [← ofReal_norm,
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
      have h_lint_pt :
          (fun x => ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) x)‖ₑ
            ^ (2 : ℝ)) =
          (fun x => ENNReal.ofReal
            (‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) x)‖
            ^ (2 : ℝ))) := by
        funext x
        exact h_pt_lint x
      rw [h_lint_pt]
      rw [← _root_.MeasureTheory.ofReal_integral_eq_lintegral_ofReal hpow_int
        (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) _))]
      exact ENNReal.ofReal_lt_top
    refine ENNReal.rpow_lt_top_of_nonneg ?_ h_lint_finite.ne
    norm_num
  have h_2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_2_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have h_eLp_lhs :
      _root_.MeasureTheory.eLpNorm (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u : E → ℝ)
        2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) =
      ENNReal.ofReal ((∫ x,
        ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) x)‖ ^ (2 : ℝ)
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) ^ ((2 : ℝ)⁻¹)) := by
    have h := hconv_memLp.eLpNorm_eq_integral_rpow_norm h_2_ne_zero h_2_ne_top
    have h_2_toReal : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
    rw [h_2_toReal] at h
    exact h
  have h_eLp_rhs :
      _root_.MeasureTheory.eLpNorm u 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) =
      ENNReal.ofReal ((∫ x, ‖u x‖ ^ (2 : ℝ) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) ^ ((2 : ℝ)⁻¹)) := by
    have h := hu.eLpNorm_eq_integral_rpow_norm h_2_ne_zero h_2_ne_top
    have h_2_toReal : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
    rw [h_2_toReal] at h
    exact h
  have hcomm : mollifyEps (d := d) hε u =
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)]
        mollifierEps (d := d) hε) := by
    funext y
    exact mollifyEps_eq_convolution_swap hε u y
  rw [hcomm]
  have hcomm_convergence : ∀ y : E,
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)]
        mollifierEps (d := d) hε) y =
      (mollifierEps (d := d) hε
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) y := by
    intro y
    rw [_root_.MeasureTheory.convolution_lsmul, _root_.MeasureTheory.convolution_lsmul_swap]
    refine _root_.MeasureTheory.integral_congr_ae ?_
    filter_upwards with t
    rw [smul_eq_mul, smul_eq_mul, mul_comm]
  have hfun_eq :
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)]
        mollifierEps (d := d) hε) =
      (mollifierEps (d := d) hε
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) := by
    funext y; exact hcomm_convergence y
  rw [hfun_eq]
  change _root_.MeasureTheory.eLpNorm (mollifierEps (d := d) hε
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) 2
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤ _root_.MeasureTheory.eLpNorm u 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)
  rw [h_eLp_lhs, h_eLp_rhs]
  refine ENNReal.ofReal_le_ofReal ?_
  have h_int_combined :
      ∫ x, ‖((ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)] u) x)‖ ^ (2 : ℝ)
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤
      ∫ x, ‖u x‖ ^ (2 : ℝ) ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
    h_int_le.trans (le_of_eq h_convergence_eq)
  refine Real.rpow_le_rpow ?_ h_int_combined ?_
  · exact _root_.MeasureTheory.integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  · exact inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.eLpNorm_mollifyEps_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.eLpNorm_mollifyEps_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.eLpNorm_mollifyEps_le ``Submission.DifferentialGeometry.Analysis.Sobolev.eLpNorm_mollifyEps_le

end DifferentialGeometry.Analysis.Sobolev
