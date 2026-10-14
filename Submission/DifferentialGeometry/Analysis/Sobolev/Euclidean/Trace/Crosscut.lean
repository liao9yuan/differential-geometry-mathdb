import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.PolarArc
import Submission.DifferentialGeometry.Analysis.Integration.Integral.LogRadiusSelection
import Submission.DifferentialGeometry.Analysis.Sobolev.Interval.ArcEnergy
import Submission.DifferentialGeometry.Analysis.Complex.CircleArc
import Submission.DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous.Energy
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Polar.Complex
import Submission.DifferentialGeometry.Analysis.Integration.PolarAnnulus.Centered
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Submission.DifferentialGeometry.Analysis.Sobolev.Interval.TraceCompactness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.NNReal _root_.Topology

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_radius_normalized_crosscut_energy_le
    {f : ℂ → F} {K : ℝ≥0} (hf : LipschitzWith K f)
    {r R B : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < 2)
    (henergy : (∫ z in {z : ℂ | _root_.Dist.dist z (-1) ∈ _root_.Set.Icc r R} ∩
      Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ f z‖ ^ 2) ≤ B) :
    ∃ ρ ∈ _root_.Set.Ioo r R,
      let a := Real.arccos (ρ / 2)
      (∫ t in _root_.Set.Icc (0 : ℝ) 1,
        ‖deriv (fun s => f (circleMap (-1) ρ (-a + (2 * a) * s))) t‖ ^ 2) ≤
          Real.pi * B / Real.log (R / r) := by
  classical
  let Ω := Metric.closedBall (0 : ℂ) 1
  let P (ρ : ℝ) : Prop :=
    ∀ a ∈ _root_.Set.Icc (-Real.pi) Real.pi, ∀ b ∈ _root_.Set.Icc (-Real.pi) Real.pi,
      a ≤ b → _root_.Set.MapsTo (circleMap (-1) ρ) (_root_.Set.Icc a b) Ω →
        (∫ θ in _root_.Set.Icc a b, ‖deriv (f ∘ circleMap (-1) ρ) θ‖ ^ 2) ≤
          ρ * circleTangentialEnergy f Ω (-1) ρ
  have hP : ∀ᵐ ρ ∂volume.restrict (_root_.Set.Ioo r R), P ρ := by
    have h := _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (show _root_.Set.Ioo r R ⊆ _root_.Set.Ioi (0 : ℝ) from fun x hx => hr.trans hx.1)
      (ae_circle_arc_deriv_integral_le (Ω := Ω) hf measurableSet_closedBall (-1))
    exact h.mono fun ρ hρ => hρ.2
  let N := {ρ : ℝ | ¬P ρ}
  have hN : (volume.restrict (_root_.Set.Ioo r R)) N = 0 := ae_iff.mp hP
  obtain ⟨hd, hd0, hdB⟩ := integrableOn_circleTangentialEnergy_and_integral_le (Ω := Ω) hf
    measurableSet_closedBall (-1) hr hrR.le
  obtain ⟨ρ, hρ, hρN, hρd⟩ := exists_mul_le_div_log_notMem_null hr hrR hd hN
    (hdB.trans henergy)
  have hρP : P ρ := by simpa only [N, _root_.Set.mem_ofPred_eq, _root_.Classical.not_not] using hρN
  let a := Real.arccos (ρ / 2)
  have hρ0 : 0 < ρ := hr.trans hρ.1
  have hρ2 : ρ < 2 := hρ.2.trans hR
  have ha0 : 0 ≤ a := Real.arccos_nonneg _
  have haπ : a ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr (by positivity)
  have hma : -a ∈ _root_.Set.Icc (-Real.pi) Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have hpa : a ∈ _root_.Set.Icc (-Real.pi) Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have hraw : (∫ θ in _root_.Set.Icc (-a) a, ‖deriv (f ∘ circleMap (-1) ρ) θ‖ ^ 2) ≤
      B / Real.log (R / r) :=
    (hρP (-a) hma a hpa (by linarith)
      (fun θ hθ => Complex.circleMap_neg_one_mem_closedBall ρ hρ0.le hρ2.le hθ)).trans hρd
  have hnorm := integral_deriv_affine_interval_sq (f ∘ circleMap (-1) ρ)
    (show -a ≤ a by linarith)
  have hid : a - -a = 2 * a := by ring
  simp only [hid, Function.comp_apply] at hnorm
  have hnonneg : 0 ≤ (∫ θ in _root_.Set.Icc (-a) a, ‖deriv (f ∘ circleMap (-1) ρ) θ‖ ^ 2) :=
    _root_.MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  refine ⟨ρ, hρ, ?_⟩
  change (∫ t in _root_.Set.Icc (0 : ℝ) 1,
    ‖deriv (fun s => f (circleMap (-1) ρ (-a + (2 * a) * s))) t‖ ^ 2) ≤ _
  rw [hnorm]
  calc
    2 * a * (∫ θ in _root_.Set.Icc (-a) a, ‖deriv (f ∘ circleMap (-1) ρ) θ‖ ^ 2) ≤
        Real.pi * (∫ θ in _root_.Set.Icc (-a) a, ‖deriv (f ∘ circleMap (-1) ρ) θ‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) hnonneg
    _ ≤ Real.pi * (B / Real.log (R / r)) :=
      mul_le_mul_of_nonneg_left hraw Real.pi_pos.le
    _ = _ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_radius_normalized_crosscut_energy_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_radius_normalized_crosscut_energy_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_radius_normalized_crosscut_energy_le ``Submission.DifferentialGeometry.Analysis.exists_radius_normalized_crosscut_energy_le

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.NNReal

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]


theorem exists_circle_arc_oscillation_sq_le_integral_fderiv_sq_of_lipschitz
    {f : ℂ → E} {K : ℝ≥0} (hf : LipschitzWith K f)
    {Ω : Set ℂ} (hΩ : MeasurableSet Ω) (c : ℂ)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ ρ ∈ _root_.Set.Ioo r R, ∀ a ∈ _root_.Set.Icc (-Real.pi) Real.pi, ∀ b ∈ _root_.Set.Icc (-Real.pi) Real.pi,
      a ≤ b → _root_.Set.MapsTo (circleMap c ρ) (_root_.Set.Icc a b) Ω →
        ‖f (circleMap c ρ a) - f (circleMap c ρ b)‖ ^ 2 ≤
          2 * Real.pi *
            (∫ z in {z : ℂ | _root_.Dist.dist z c ∈ _root_.Set.Icc r R} ∩ Ω, ‖fderiv ℝ f z‖ ^ 2) /
              Real.log (R / r) := by
  classical
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let S : Set (ℝ × ℝ) := {p | circleMap c p.1 p.2 ∈ Ω}
  let A : ℝ × ℝ → ℝ := S.indicator (fun p => p.1⁻¹ *
    ‖fderiv ℝ f (circleMap c p.1 p.2) (circleMap 0 p.1 p.2 * Complex.I)‖ ^ 2)
  let D : ℝ × ℝ → ℝ := S.indicator (fun p =>
    p.1 * ‖fderiv ℝ f (circleMap c p.1 p.2)‖ ^ 2)
  have hc : Continuous (fun p : ℝ × ℝ => circleMap c p.1 p.2) := by
    simp only [circleMap]
    fun_prop
  have hc₀ : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    simp only [circleMap]
    fun_prop
  have hS : MeasurableSet S := hΩ.preimage hc.measurable
  have hDm : Measurable (fun p : ℝ × ℝ =>
      p.1 * ‖fderiv ℝ f (circleMap c p.1 p.2)‖ ^ 2) :=
    measurable_fst.mul (((measurable_fderiv ℝ f).comp hc.measurable).norm.pow_const 2)
  have hAm : Measurable A := by
    apply Measurable.indicator _ hS
    apply Measurable.mul measurable_fst.inv
    have happ : Measurable (fun p : ℝ × ℝ =>
        fderiv ℝ f (circleMap c p.1 p.2) (circleMap 0 p.1 p.2 * Complex.I)) :=
      (isBoundedBilinearMap_apply.continuous.measurable).comp
        (((measurable_fderiv ℝ f).comp hc.measurable).prodMk
          (hc₀.measurable.mul measurable_const))
    exact happ.norm.pow_const 2
  have hAnonneg (p : ℝ × ℝ) (hp : 0 < p.1) : 0 ≤ A p := by
    by_cases h : p ∈ S
    · simp only [A, _root_.Set.indicator_of_mem h]
      positivity
    · simp only [A, _root_.Set.indicator_of_notMem h, le_refl]
  have hAD : ∀ p ∈ _root_.Set.Icc (r, -Real.pi) (R, Real.pi), A p ≤ D p := by
    intro p hp
    by_cases h : p ∈ S
    · simp only [A, D, _root_.Set.indicator_of_mem h]
      exact tangential_energy_le (hr.trans_le hp.1.1) _
    · simp only [A, D, _root_.Set.indicator_of_notMem h, le_refl]
  have hDi : _root_.MeasureTheory.IntegrableOn D (_root_.Set.Icc (r, -Real.pi) (R, Real.pi)) := by
    apply Integrable.indicator _ hS
    apply (_root_.MeasureTheory.integrableOn_const (C := R * (K : ℝ) ^ 2) isCompact_Icc.measure_ne_top).mono'
      hDm.aestronglyMeasurable
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with p hp
    have hp0 : 0 ≤ p.1 := (hr.trans_le hp.1.1).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp0 (sq_nonneg _))]
    exact mul_le_mul hp.2.1
      ((sq_le_sq₀ (norm_nonneg _) K.coe_nonneg).2 (norm_fderiv_le_of_lipschitz ℝ hf))
      (sq_nonneg _) (hr.trans hrR).le
  have hAi : _root_.MeasureTheory.IntegrableOn A (_root_.Set.Icc (r, -Real.pi) (R, Real.pi)) := by
    apply hDi.mono' hAm.aestronglyMeasurable
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (hAnonneg p (hr.trans_le hp.1.1))]
    exact hAD p hp
  have hAprod : _root_.MeasureTheory.Integrable A
      ((volume.restrict (_root_.Set.Icc r R)).prod (volume.restrict (_root_.Set.Icc (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod, _root_.Set.Icc_prod_Icc]
    exact hAi
  have hshift : ∀ᵐ z : ℂ, DifferentiableAt ℝ f (c + z) :=
    (_root_.MeasureTheory.measurePreserving_add_left (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℂ) c).quasiMeasurePreserving.tendsto_ae.eventually
      hf.ae_differentiableAt
  have hdiff : ∀ᵐ ρ ∂volume.restrict (_root_.Set.Icc r R),
      ∀ᵐ θ ∂volume.restrict (_root_.Set.Icc (-Real.pi) Real.pi),
        DifferentiableAt ℝ f (circleMap c ρ θ) := by
    have hsub : _root_.Set.Icc r R ⊆ _root_.Set.Ioi (0 : ℝ) := fun ρ hρ => hr.trans_le hρ.1
    have h := _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub (ae_ae_comp_circleMap hshift)
    simpa only [circleMap, zero_add] using h
  have hbound : (∫ ρ in _root_.Set.Icc r R, ∫ θ in _root_.Set.Icc (-Real.pi) Real.pi, A (ρ, θ)) ≤
      ∫ z in {z : ℂ | _root_.Dist.dist z c ∈ _root_.Set.Icc r R} ∩ Ω, ‖fderiv ℝ f z‖ ^ 2 := by
    rw [← _root_.MeasureTheory.setIntegral_indicator hΩ, integral_annulus_eq_circleMap _ c hr]
    have hleft : (∫ p in _root_.Set.Icc (r, -Real.pi) (R, Real.pi), A p) =
        ∫ ρ in _root_.Set.Icc r R, ∫ θ in _root_.Set.Icc (-Real.pi) Real.pi, A (ρ, θ) := by
      rw [← _root_.Set.Icc_prod_Icc, Measure.volume_eq_prod,
        _root_.MeasureTheory.setIntegral_prod A (by rwa [← Measure.volume_eq_prod, _root_.Set.Icc_prod_Icc])]
    rw [← hleft]
    have heq : (fun p : ℝ × ℝ =>
        p.1 • Ω.indicator (fun z => ‖fderiv ℝ f z‖ ^ 2) (circleMap c p.1 p.2)) = D := by
      funext p
      by_cases hp : p ∈ S
      · have hpΩ : circleMap c p.1 p.2 ∈ Ω := hp
        simp only [D, _root_.Set.indicator_of_mem hp, _root_.Set.indicator_of_mem hpΩ, smul_eq_mul]
      · have hpΩ : circleMap c p.1 p.2 ∉ Ω := hp
        simp only [D, _root_.Set.indicator_of_notMem hp, _root_.Set.indicator_of_notMem hpΩ, smul_zero]
    rw [heq]
    apply _root_.MeasureTheory.integral_mono_ae hAi hDi
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with p hp
    exact hAD p hp
  let P : ℝ → Prop := fun ρ =>
    _root_.MeasureTheory.IntegrableOn (fun θ => A (ρ, θ)) (_root_.Set.Icc (-Real.pi) Real.pi) ∧
      ∀ᵐ θ ∂volume.restrict (_root_.Set.Icc (-Real.pi) Real.pi),
        DifferentiableAt ℝ f (circleMap c ρ θ)
  let N : Set ℝ := {ρ | ρ ∈ _root_.Set.Icc r R ∧ ¬ P ρ}
  have hP : ∀ᵐ ρ ∂volume.restrict (_root_.Set.Icc r R), P ρ := hAprod.prod_right_ae.and hdiff
  have hN : _root_.MeasureTheory.MeasureSpace.volume N = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    rw [_root_.MeasureTheory.ae_restrict_iff' measurableSet_Icc] at hP
    filter_upwards [hP] with ρ hρ
    exact fun hn => hn.2 (hρ hn.1)
  obtain ⟨ρ, hρ, hρN, hρbound⟩ := exists_mul_le_div_log_notMem_null
    hr hrR hAprod.integral_prod_left
      (le_antisymm ((Measure.restrict_apply_le _ _).trans_eq hN) bot_le) hbound
  have hρP : P ρ := by
    by_contra h
    exact hρN ⟨⟨hρ.1.le, hρ.2.le⟩, h⟩
  have hρpos : 0 < ρ := hr.trans hρ.1
  refine ⟨ρ, hρ, ?_⟩
  intro a ha b hb hab harc
  have htrace := hf.comp (lipschitzWith_circleMap c ρ)
  have hderiv : _root_.MeasureTheory.MemLp (deriv (f ∘ circleMap c ρ)) 2 (volume.restrict (_root_.Set.Icc a b)) := by
    apply (_root_.MeasureTheory.memLp_const ((K * Real.nnabs ρ : ℝ≥0) : ℝ)).of_le
      (measurable_deriv (f ∘ circleMap c ρ)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun θ => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (K * Real.nnabs ρ).coe_nonneg] using
        norm_deriv_le_of_lipschitz htrace (x₀ := θ)
  have hosc := norm_sub_sq_le_mul_integral_norm_deriv_sq_of_absolutelyContinuousOnInterval
    htrace.lipschitzOnWith.absolutelyContinuousOnInterval hderiv
      (show a ∈ _root_.Set.Icc a b from ⟨le_rfl, hab⟩) (show b ∈ _root_.Set.Icc a b from ⟨hab, le_rfl⟩)
  have hsub : _root_.Set.Icc a b ⊆ _root_.Set.Icc (-Real.pi) Real.pi := _root_.Set.Icc_subset_Icc ha.1 hb.2
  have heq : (∫ θ in a..b, ‖deriv (f ∘ circleMap c ρ) θ‖ ^ 2) =
      ρ * ∫ θ in _root_.Set.Icc a b, A (ρ, θ) := by
    rw [intervalIntegral.integral_of_le hab, ← _root_.MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← _root_.MeasureTheory.integral_const_mul]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hρP.2.filter_mono
      (_root_.MeasureTheory.ae_mono (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume hsub)), _root_.MeasureTheory.ae_restrict_mem measurableSet_Icc]
      with θ hd hθ
    rw [fderiv_comp_deriv θ hd (differentiable_circleMap _ _ _), deriv_circleMap]
    have hmem : (ρ, θ) ∈ S := harc hθ
    simp only [A, _root_.Set.indicator_of_mem hmem, ← mul_assoc,
      mul_inv_cancel₀ hρpos.ne', one_mul]
  have hnonneg : 0 ≤ ∫ θ in _root_.Set.Icc a b, A (ρ, θ) :=
    _root_.MeasureTheory.integral_nonneg fun θ => hAnonneg (ρ, θ) hρpos
  have hle : (∫ θ in _root_.Set.Icc a b, A (ρ, θ)) ≤
      ∫ θ in _root_.Set.Icc (-Real.pi) Real.pi, A (ρ, θ) :=
    _root_.MeasureTheory.setIntegral_mono_set hρP.1 (Filter.Eventually.of_forall fun θ => hAnonneg (ρ, θ) hρpos)
      (Filter.Eventually.of_forall hsub)
  calc
    _ ≤ (b - a) * (ρ * ∫ θ in _root_.Set.Icc a b, A (ρ, θ)) := by
      simpa only [Function.comp_apply, heq] using hosc
    _ ≤ (2 * Real.pi) * (ρ * ∫ θ in _root_.Set.Icc a b, A (ρ, θ)) :=
      mul_le_mul_of_nonneg_right (by linarith [ha.1, hb.2]) (mul_nonneg hρpos.le hnonneg)
    _ ≤ (2 * Real.pi) * (ρ * ∫ θ in _root_.Set.Icc (-Real.pi) Real.pi, A (ρ, θ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hρpos.le) (by positivity)
    _ ≤ _ := by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hρbound (by positivity : 0 ≤ 2 * Real.pi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_circle_arc_oscillation_sq_le_integral_fderiv_sq_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_circle_arc_oscillation_sq_le_integral_fderiv_sq_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_circle_arc_oscillation_sq_le_integral_fderiv_sq_of_lipschitz ``Submission.DifferentialGeometry.Analysis.exists_circle_arc_oscillation_sq_le_integral_fderiv_sq_of_lipschitz

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.NNReal

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_radius_circle_arc_oscillation_lt_of_energy_bound
    {R B ε : ℝ} (hR : 0 < R) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ r ∈ _root_.Set.Ioo 0 R, ∀ (Ω : Set ℂ), MeasurableSet Ω → ∀ (c : ℂ) (f : ℂ → E) (K : ℝ≥0),
      LipschitzWith K f →
      (∫ z in Metric.closedBall c R ∩ Ω, ‖fderiv ℝ f z‖ ^ 2) ≤ B →
      ∃ ρ ∈ _root_.Set.Ioo r R, ∀ a ∈ _root_.Set.Icc (-Real.pi) Real.pi, ∀ b ∈ _root_.Set.Icc (-Real.pi) Real.pi,
        a ≤ b → _root_.Set.MapsTo (circleMap c ρ) (_root_.Set.Icc a b) Ω →
          ‖f (circleMap c ρ a) - f (circleMap c ρ b)‖ < ε := by
  let q : ℝ := 2 * Real.pi * B / ε ^ 2 + 1
  have hq : 0 < q := by dsimp [q]; positivity
  let r := R / Real.exp q
  have hr : 0 < r := div_pos hR (Real.exp_pos _)
  have hrR : r < R := by
    dsimp only [r]
    exact div_lt_self hR ((Real.one_lt_exp_iff).2 hq)
  have hlog : Real.log (R / r) = q := by
    have heq : R / r = Real.exp q := by dsimp [r]; field_simp
    rw [heq, Real.log_exp]
  refine ⟨r, ⟨hr, hrR⟩, ?_⟩
  intro Ω hΩ c f K hf henergy
  have hfi : _root_.MeasureTheory.IntegrableOn (fun z : ℂ => ‖fderiv ℝ f z‖ ^ 2) (Metric.closedBall c R) := by
    apply (_root_.MeasureTheory.integrableOn_const (C := (K : ℝ) ^ 2) (_root_.ProperSpace.isCompact_closedBall c R).measure_ne_top).mono'
      ((measurable_fderiv ℝ f).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _) K.coe_nonneg).2 (norm_fderiv_le_of_lipschitz ℝ hf)
  have hsub : {z : ℂ | _root_.Dist.dist z c ∈ _root_.Set.Icc r R} ∩ Ω ⊆ Metric.closedBall c R ∩ Ω := by
    intro z hz
    exact ⟨hz.1.2, hz.2⟩
  have henergy' : (∫ z in {z : ℂ | _root_.Dist.dist z c ∈ _root_.Set.Icc r R} ∩ Ω, ‖fderiv ℝ f z‖ ^ 2) ≤ B := by
    apply le_trans _ henergy
    exact _root_.MeasureTheory.setIntegral_mono_set (hfi.mono_set _root_.Set.inter_subset_left)
      (Filter.Eventually.of_forall fun z => sq_nonneg _) (Filter.Eventually.of_forall hsub)
  obtain ⟨ρ, hρ, hosc⟩ :=
    exists_circle_arc_oscillation_sq_le_integral_fderiv_sq_of_lipschitz hf hΩ c hr hrR
  refine ⟨ρ, hρ, ?_⟩
  intro a ha b hb hab harc
  have hsq := hosc a ha b hb hab harc
  rw [hlog] at hsq
  have hbound : 2 * Real.pi * B / q < ε ^ 2 := by
    apply (div_lt_iff₀ hq).2
    dsimp only [q]
    have he : ε ^ 2 ≠ 0 := (pow_pos hε 2).ne'
    field_simp
    nlinarith [Real.pi_pos]
  have hmono : 2 * Real.pi *
      (∫ z in {z : ℂ | _root_.Dist.dist z c ∈ _root_.Set.Icc r R} ∩ Ω, ‖fderiv ℝ f z‖ ^ 2) / q ≤
        2 * Real.pi * B / q :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left henergy' (by positivity)) hq.le
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).1 (hsq.trans hmono |>.trans_lt hbound)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_radius_circle_arc_oscillation_lt_of_energy_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_radius_circle_arc_oscillation_lt_of_energy_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_radius_circle_arc_oscillation_lt_of_energy_bound ``Submission.DifferentialGeometry.Analysis.exists_radius_circle_arc_oscillation_lt_of_energy_bound

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Topology _root_.NNReal

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_radius_subseq_circle_arc_energy_bound_and_ae_tendsto
    (f : ℕ → ℂ → E) (v : ℂ → E) (K : ℕ → ℝ≥0)
    (hf : ∀ n, LipschitzWith (K n) (f n))
    {Ω : Set ℂ} (hΩ : MeasurableSet Ω) (c : ℂ)
    {r R B ε : ℝ} (hr : 0 < r) (hrR : r < R)
    (henergy : ∀ n, (∫ z in {z : ℂ | _root_.Dist.dist z c ∈ _root_.Set.Icc r R} ∩ Ω,
      ‖fderiv ℝ (f n) z‖ ^ 2) ≤ B)
    (hae : ∀ᵐ z ∂volume.restrict Ω, _root_.Filter.Tendsto (fun n => f n z) _root_.Filter.atTop (𝓝 (v z)))
    (hε : 0 < ε) :
    ∃ ρ ∈ _root_.Set.Ioo r R, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ᵐ θ ∂volume.restrict (_root_.Set.Icc (-Real.pi) Real.pi), circleMap c ρ θ ∈ Ω →
        _root_.Filter.Tendsto (fun n => f (σ n) (circleMap c ρ θ)) _root_.Filter.atTop (𝓝 (v (circleMap c ρ θ)))) ∧
      ∀ n a, a ∈ _root_.Set.Icc (-Real.pi) Real.pi → ∀ b, b ∈ _root_.Set.Icc (-Real.pi) Real.pi →
        a ≤ b → _root_.Set.MapsTo (circleMap c ρ) (_root_.Set.Icc a b) Ω →
          (∫ θ in _root_.Set.Icc a b, ‖deriv (f (σ n) ∘ circleMap c ρ) θ‖ ^ 2) ≤
            B / Real.log (R / r) + ε := by
  have hdata (n : ℕ) := integrableOn_circleTangentialEnergy_and_integral_le
    (hf n) hΩ c hr hrR.le
  have hshift : ∀ᵐ z : ℂ, c + z ∈ Ω →
      Tendsto (fun n => f n (c + z)) _root_.Filter.atTop (𝓝 (v (c + z))) :=
    (_root_.MeasureTheory.measurePreserving_add_left (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℂ) c).quasiMeasurePreserving.ae
      ((_root_.MeasureTheory.ae_restrict_iff' hΩ).mp hae)
  have hconv : ∀ᵐ ρ ∂volume.restrict (_root_.Set.Icc r R),
      ∀ᵐ θ ∂volume.restrict (_root_.Set.Icc (-Real.pi) Real.pi), circleMap c ρ θ ∈ Ω →
        Tendsto (fun n => f n (circleMap c ρ θ)) _root_.Filter.atTop (𝓝 (v (circleMap c ρ θ))) := by
    have h := _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (show _root_.Set.Icc r R ⊆ _root_.Set.Ioi (0 : ℝ) from fun x hx => hr.trans_le hx.1)
      (ae_ae_comp_circleMap hshift)
    simpa only [circleMap, zero_add] using h
  have hder := ae_all_iff.mpr fun n =>
    _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (show _root_.Set.Icc r R ⊆ _root_.Set.Ioi (0 : ℝ) from fun x hx => hr.trans_le hx.1)
      (ae_circle_arc_deriv_integral_le (hf n) hΩ c)
  have hpos (n : ℕ) :
      0 ≤ᵐ[volume.restrict (_root_.Set.Icc r R)] circleTangentialEnergy (f n) Ω c := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with ρ hρ
    exact (hdata n).2.1 ρ hρ
  obtain ⟨ρ, hρ, hP, σ, hσ, hb⟩ :=
    exists_radius_subseq_mul_le_div_log_of_integral_bound hr hrR
      (fun n => (hdata n).1) hpos
      (fun n => (hdata n).2.2.trans (henergy n)) (hconv.and hder) hε
  refine ⟨ρ, hρ, σ, hσ, ?_, ?_⟩
  · filter_upwards [hP.1] with θ hθ
    exact fun hx => (hθ hx).comp hσ.tendsto_atTop
  · intro n a ha b hb' hab harc
    exact ((hP.2 (σ n)).2 a ha b hb' hab harc).trans (hb n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_radius_subseq_circle_arc_energy_bound_and_ae_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_radius_subseq_circle_arc_energy_bound_and_ae_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_radius_subseq_circle_arc_energy_bound_and_ae_tendsto ``Submission.DifferentialGeometry.Analysis.exists_radius_subseq_circle_arc_energy_bound_and_ae_tendsto

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Topology _root_.NNReal

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_fixed_boundary_crosscut_tendsto_uniformly
    (f : ℕ → ℂ → E) (v η : ℂ → E) (K : ℕ → ℝ≥0)
    (hf : ∀ n, LipschitzWith (K n) (f n))
    (hv : ContinuousOn v (Metric.ball (0 : ℂ) 1))
    (hae : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1),
      _root_.Filter.Tendsto (fun n => f n z) _root_.Filter.atTop (𝓝 (v z)))
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → _root_.Filter.Tendsto (fun n => f n z) _root_.Filter.atTop (𝓝 (η z)))
    {r R B ε : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < 2)
    (henergy : ∀ n, (∫ z in {z : ℂ | _root_.Dist.dist z (-1) ∈ _root_.Set.Icc r R} ∩
        Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ (f n) z‖ ^ 2) ≤ B)
    (hε : 0 < ε) :
    ∃ ρ ∈ _root_.Set.Ioo r R, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      let a := Real.arccos (ρ / 2)
      ∃ β : C(_root_.Set.Icc (-a) a, E),
        TendstoUniformly (fun n (θ : _root_.Set.Icc (-a) a) => f (σ n) (circleMap (-1) ρ θ))
          β _root_.Filter.atTop ∧
        (∀ θ (hθ : θ ∈ _root_.Set.Ioo (-a) a), β ⟨θ, _root_.Set.Ioo_subset_Icc_self hθ⟩ =
          v (circleMap (-1) ρ θ)) ∧
        β ⟨-a, le_rfl, neg_le_self (Real.arccos_nonneg _)⟩ =
          η (circleMap (-1) ρ (-a)) ∧
        β ⟨a, neg_le_self (Real.arccos_nonneg _), le_rfl⟩ = η (circleMap (-1) ρ a) ∧
        ∀ s t : _root_.Set.Icc (-a) a,
          ‖β s - β t‖ ^ 2 ≤ (B / Real.log (R / r) + ε) * |(s : ℝ) - t| := by
  have hball : volume.restrict (Metric.ball (0 : ℂ) 1) =
      volume.restrict (Metric.closedBall (0 : ℂ) 1) := by
    apply Measure.restrict_congr_set
    have hnull := measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere _root_.MeasureTheory.MeasureSpace.volume (0 : ℂ) 1)
    filter_upwards [hnull] with z hz
    apply propext
    change _root_.Dist.dist z (0 : ℂ) < 1 ↔ _root_.Dist.dist z 0 ≤ 1
    exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hz⟩
  have haec : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) 1),
      Tendsto (fun n => f n z) _root_.Filter.atTop (𝓝 (v z)) := by rwa [← hball]
  obtain ⟨ρ, hρ, σ, hσ, hslices, harc⟩ :=
    exists_radius_subseq_circle_arc_energy_bound_and_ae_tendsto f v K hf
      measurableSet_closedBall (-1) hr hrR henergy haec hε
  let a := Real.arccos (ρ / 2)
  have hρ0 : 0 < ρ := hr.trans hρ.1
  have hρ2 : ρ < 2 := hρ.2.trans hR
  have ha0 : 0 < a := Real.arccos_pos.mpr (by linarith)
  have hab : -a < a := neg_lt_self ha0
  have hale : a ≤ Real.pi := Real.arccos_le_pi _
  have hma : -a ∈ _root_.Set.Icc (-Real.pi) Real.pi := ⟨neg_le_neg hale, by linarith [Real.pi_pos]⟩
  have hpa : a ∈ _root_.Set.Icc (-Real.pi) Real.pi := ⟨by linarith [Real.pi_pos], hale⟩
  let c := circleMap (-1) ρ
  let F : ℕ → ℝ → E := fun n => f (σ n) ∘ c
  have hF (n : ℕ) : LipschitzWith (K (σ n) * Real.nnabs ρ) (F n) :=
    (hf (σ n)).comp (lipschitzWith_circleMap (-1) ρ)
  have hE (n : ℕ) : (∫ θ in _root_.Set.Icc (-a) a, ‖deriv (F n) θ‖ ^ 2) ≤
      B / Real.log (R / r) + ε :=
    harc n (-a) hma a hpa hab.le
      (fun θ hθ => Complex.circleMap_neg_one_mem_closedBall ρ hρ0.le hρ2.le hθ)
  have hvc : ContinuousOn (v ∘ c) (_root_.Set.Ioo (-a) a) :=
    hv.comp (continuous_circleMap (-1) ρ).continuousOn
      (fun θ hθ => Complex.circleMap_neg_one_mem_ball ρ hρ0 hθ)
  have hfv : ∀ᵐ θ ∂volume.restrict (_root_.Set.Ioo (-a) a),
      Tendsto (fun n => F n θ) _root_.Filter.atTop (𝓝 ((v ∘ c) θ)) := by
    have hsub : _root_.Set.Ioo (-a) a ⊆ _root_.Set.Icc (-Real.pi) Real.pi :=
      Ioo_subset_Icc_self.trans (_root_.Set.Icc_subset_Icc hma.1 hpa.2)
    filter_upwards [_root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub hslices,
      _root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ hθin
    exact hθ (Complex.circleMap_neg_one_mem_closedBall ρ hρ0.le hρ2.le
      (_root_.Set.Ioo_subset_Icc_self hθin))
  have hleft : _root_.Filter.Tendsto (fun n => F n (-a)) _root_.Filter.atTop (𝓝 (η (c (-a)))) :=
    (hboundary _ (Complex.norm_circleMap_neg_one_neg_arccos ρ hρ0.le hρ2.le)).comp hσ.tendsto_atTop
  have hright : _root_.Filter.Tendsto (fun n => F n a) _root_.Filter.atTop (𝓝 (η (c a))) :=
    (hboundary _ (Complex.norm_circleMap_neg_one_arccos ρ hρ0.le hρ2.le)).comp hσ.tendsto_atTop
  obtain ⟨β, hβ, hβv, hβleft, hβright, hmod⟩ :=
    Sobolev.exists_continuous_Icc_extension_of_ae_tendsto_of_endpoint_tendsto
      hab F (fun n => K (σ n) * Real.nnabs ρ) hF hE hleft hright (v ∘ c) hvc hfv
  refine ⟨ρ, hρ, σ, hσ, β, ?_, ?_, hβleft, hβright, hmod⟩
  · rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hβ δ hδ] with n hn θ
    simpa only [Set.IccExtend_of_mem hab.le β θ.property, F, c, Function.comp_apply] using
      hn (θ : ℝ) θ.property
  · intro θ hθ
    have h := hβv hθ
    rwa [Set.IccExtend_of_mem hab.le β (_root_.Set.Ioo_subset_Icc_self hθ)] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_fixed_boundary_crosscut_tendsto_uniformly then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_fixed_boundary_crosscut_tendsto_uniformly"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_fixed_boundary_crosscut_tendsto_uniformly ``Submission.DifferentialGeometry.Analysis.exists_fixed_boundary_crosscut_tendsto_uniformly

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Topology _root_.NNReal

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_small_boundary_crosscut_tendsto_uniformly
    (f : ℕ → ℂ → E) (v η : ℂ → E) (K : ℕ → ℝ≥0)
    (hf : ∀ n, LipschitzWith (K n) (f n))
    (hv : ContinuousOn v (Metric.ball (0 : ℂ) 1))
    (hae : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) 1),
      _root_.Filter.Tendsto (fun n => f n z) _root_.Filter.atTop (𝓝 (v z)))
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → _root_.Filter.Tendsto (fun n => f n z) _root_.Filter.atTop (𝓝 (η z)))
    (hη : ContinuousWithinAt η (Metric.sphere (0 : ℂ) 1) (-1))
    {B : ℝ} (henergy : ∀ n,
      (∫ z in Metric.closedBall (0 : ℂ) 1, ‖fderiv ℝ (f n) z‖ ^ 2) ≤ B)
    {R₀ δ : ℝ} (hR₀ : 0 < R₀) (hδ : 0 < δ) :
    ∃ R ∈ _root_.Set.Ioo 0 (_root_.Min.min R₀ 2), ∃ r ∈ _root_.Set.Ioo 0 R, ∃ ρ ∈ _root_.Set.Ioo r R,
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
      let a := Real.arccos (ρ / 2)
      ∃ β : C(_root_.Set.Icc (-a) a, E),
        TendstoUniformly (fun n (θ : _root_.Set.Icc (-a) a) => f (σ n) (circleMap (-1) ρ θ))
          β _root_.Filter.atTop ∧
        (∀ θ (hθ : θ ∈ _root_.Set.Ioo (-a) a), β ⟨θ, _root_.Set.Ioo_subset_Icc_self hθ⟩ =
          v (circleMap (-1) ρ θ)) ∧
        β ⟨-a, le_rfl, neg_le_self (Real.arccos_nonneg _)⟩ =
          η (circleMap (-1) ρ (-a)) ∧
        β ⟨a, neg_le_self (Real.arccos_nonneg _), le_rfl⟩ = η (circleMap (-1) ρ a) ∧
        ∀ θ : _root_.Set.Icc (-a) a, ‖β θ - η (-1)‖ < δ := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  have hB : 0 ≤ B := (_root_.MeasureTheory.integral_nonneg fun z => sq_nonneg ‖fderiv ℝ (f 0) z‖).trans
    (henergy 0)
  obtain ⟨d, hd, hηclose⟩ := Metric.continuousWithinAt_iff.mp hη (δ / 2) (half_pos hδ)
  let R := _root_.Min.min (_root_.Min.min R₀ 2) d / 2
  have hR : 0 < R := half_pos (lt_min (lt_min hR₀ (by norm_num)) hd)
  have hRlim : R < _root_.Min.min R₀ 2 := by
    dsimp only [R]
    have hmin : 0 < _root_.Min.min R₀ 2 := lt_min hR₀ (by norm_num)
    linarith [min_le_left (_root_.Min.min R₀ 2) d]
  have hRd : R < d := by
    dsimp only [R]
    linarith [min_le_right (_root_.Min.min R₀ 2) d]
  have hR2 : R < 2 := hRlim.trans_le (min_le_right R₀ 2)
  let ε := δ ^ 2 / (16 * Real.pi)
  have hε : 0 < ε := div_pos (sq_pos_of_pos hδ) (by positivity)
  let q := B / ε + 1
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  let r := R / Real.exp q
  have hr : 0 < r := div_pos hR (Real.exp_pos _)
  have hrR : r < R := by
    dsimp only [r]
    exact div_lt_self hR ((Real.one_lt_exp_iff).2 hq)
  have hlog : Real.log (R / r) = q := by
    have heq : R / r = Real.exp q := by
      dsimp only [r]
      field_simp
    rw [heq, Real.log_exp]
  have hdiv : B / q < ε := by
    apply (div_lt_iff₀ hq).2
    have heq : ε * q = B + ε := by
      dsimp only [q]
      field_simp
    rw [heq]
    linarith
  have hsmall : (B / Real.log (R / r) + ε) * (2 * Real.pi) < (δ / 2) ^ 2 := by
    rw [hlog]
    calc
      (B / q + ε) * (2 * Real.pi) < (2 * ε) * (2 * Real.pi) :=
        mul_lt_mul_of_pos_right (by linarith) (by positivity)
      _ = (δ / 2) ^ 2 := by
        dsimp only [ε]
        field_simp
        ring
  have hcapEnergy (n : ℕ) :
      (∫ z in {z : ℂ | _root_.Dist.dist z (-1) ∈ _root_.Set.Icc r R} ∩ Metric.closedBall (0 : ℂ) 1,
        ‖fderiv ℝ (f n) z‖ ^ 2) ≤ B := by
    have hi : _root_.MeasureTheory.IntegrableOn (fun z : ℂ => ‖fderiv ℝ (f n) z‖ ^ 2)
        (Metric.closedBall (0 : ℂ) 1) := by
      apply (_root_.MeasureTheory.integrableOn_const (C := (K n : ℝ) ^ 2)
        (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) 1).measure_ne_top).mono'
        ((measurable_fderiv ℝ (f n)).norm.pow_const 2).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact (sq_le_sq₀ (norm_nonneg _) (K n).coe_nonneg).2
          (norm_fderiv_le_of_lipschitz ℝ (hf n))
    exact (_root_.MeasureTheory.setIntegral_mono_set hi (Filter.Eventually.of_forall fun z => sq_nonneg _)
      (Filter.Eventually.of_forall _root_.Set.inter_subset_right)).trans (henergy n)
  obtain ⟨ρ, hρ, σ, hσ, β, hβ, hβv, hβleft, hβright, hmod⟩ :=
    exists_fixed_boundary_crosscut_tendsto_uniformly f v η K hf hv hae hboundary
      hr hrR hR2 hcapEnergy hε
  let a := Real.arccos (ρ / 2)
  let left : _root_.Set.Icc (-a) a := ⟨-a, le_rfl, neg_le_self (Real.arccos_nonneg _)⟩
  have hρ0 : 0 < ρ := hr.trans hρ.1
  have hρ2 : ρ < 2 := hρ.2.trans hR2
  have hleftSphere : circleMap (-1) ρ (-a) ∈ Metric.sphere (0 : ℂ) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right, a] using
      Complex.norm_circleMap_neg_one_neg_arccos ρ hρ0.le hρ2.le
  have hleftDist : _root_.Dist.dist (circleMap (-1) ρ (-a)) (-1) = ρ := by
    have heq : circleMap (-1) ρ (-a) - (-1) = circleMap 0 ρ (-a) := by
      simp only [circleMap]
      ring
    rw [dist_eq_norm, heq, norm_circleMap_zero, abs_of_pos hρ0]
  have hleftClose : ‖β left - η (-1)‖ < δ / 2 := by
    rw [show β left = η (circleMap (-1) ρ (-a)) from hβleft]
    simpa only [dist_eq_norm] using
      hηclose hleftSphere (by rw [hleftDist]; exact hρ.2.trans hRd)
  have hD : 0 ≤ B / Real.log (R / r) + ε := by
    rw [hlog]
    positivity
  refine ⟨R, ⟨hR, hRlim⟩, r, ⟨hr, hrR⟩, ρ, hρ, σ, hσ, β,
    hβ, hβv, hβleft, hβright, ?_⟩
  intro θ
  have hθdist : |(θ : ℝ) - (left : ℝ)| ≤ 2 * Real.pi := by
    change |(θ : ℝ) - -a| ≤ 2 * Real.pi
    rw [abs_of_nonneg (by linarith [θ.property.1])]
    have ha : a ≤ Real.pi := Real.arccos_le_pi _
    linarith [θ.property.2]
  have hsq : ‖β θ - β left‖ ^ 2 < (δ / 2) ^ 2 :=
    ((hmod θ left).trans (mul_le_mul_of_nonneg_left hθdist hD)).trans_lt hsmall
  have hnear : ‖β θ - β left‖ < δ / 2 :=
    (sq_lt_sq₀ (norm_nonneg _) (half_pos hδ).le).mp hsq
  exact (norm_sub_le_norm_sub_add_norm_sub (β θ) (β left) (η (-1))).trans_lt (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_small_boundary_crosscut_tendsto_uniformly then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_small_boundary_crosscut_tendsto_uniformly"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_small_boundary_crosscut_tendsto_uniformly ``Submission.DifferentialGeometry.Analysis.exists_small_boundary_crosscut_tendsto_uniformly

end DifferentialGeometry.Analysis

end
