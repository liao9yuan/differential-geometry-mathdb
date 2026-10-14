import Submission.DifferentialGeometry.Analysis.Integration.EntropyJensen
import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Embedding.Intrinsic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Sobolev

noncomputable section

open _root_.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Integration
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal


theorem logSobolev_closed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank Real E = 3)
    (tauMax : Real) :
    ∃ L : Real, ∀ {tau : Real}, tau ∈ _root_.Set.Ioc 0 tauMax ->
      ∀ {v : M -> Real}, ContMDiff I 𝓘(Real, Real) ∞ v ->
        (∀ x : M, 0 < v x) ->
        (∫ x, v x ^ 2 ∂(riemannianVolumeMeasure I M g)) = 1 ->
        (∫ x, v x ^ 2 * Real.log (v x ^ 2)
            ∂(riemannianVolumeMeasure I M g)) ≤
          2 * tau *
              (∫ x, g.inner x
                  (gradFun (I := I) g v x)
                  (gradFun (I := I) g v x)
                ∂(riemannianVolumeMeasure I M g)) -
            ((3 : Real) / 2) * Real.log tau + L := by
  classical
  let _ : NeZero (Module.finrank Real E) := ⟨by rw [hdim]; norm_num⟩
  let _ : MeasurableSpace M := borel M
  let _ : BorelSpace M := ⟨rfl⟩
  let μ := riemannianVolumeMeasure I M g
  let _ : _root_.MeasureTheory.IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hpdim : (2 : Real) < (Module.finrank Real E : Real) := by
    norm_num [hdim]
  obtain ⟨C, hC, hSob⟩ :=
    sobolev_lpNorm (I := I) (M := M) g (p := (2 : Real)) (by norm_num) hpdim
  let C0 := _root_.Max.max 1 C
  have hC0 : 0 < C0 := by
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 C)
  refine ⟨3 * Real.log C0 + ((3 : Real) / 2) * Real.log 2 +
      ((3 : Real) / 2) * tauMax - (3 : Real) / 2, ?_⟩
  intro tau htau v hv hpos hmass
  have htau0 : 0 < tau := htau.1
  have htau_le : tau ≤ tauMax := htau.2
  let gradNorm : M -> Real := fun x => Real.sqrt
    (g.inner x
      (gradFun (I := I) g v x)
      (gradFun (I := I) g v x))
  let energy : M -> Real := fun x =>
    g.inner x
      (gradFun (I := I) g v x)
      (gradFun (I := I) g v x)
  let A : Real := ∫ x, energy x ∂μ
  have henergy0 (x : M) : 0 ≤ energy x := by
    by_cases hzero : gradFun (I := I) g v x = 0
    · change 0 ≤ g.inner x
        (gradFun (I := I) g v x) (gradFun (I := I) g v x)
      rw [hzero]
      simpa only [map_zero] using (le_refl (0 : Real))
    · exact (g.pos x (gradFun (I := I) g v x) hzero).le
  have hA0 : 0 ≤ A := _root_.MeasureTheory.integral_nonneg henergy0
  have hmass' : (∫ x, v x ^ 2 ∂μ) = 1 := by
    simpa only [μ] using hmass
  have hmass_pow : (∫ x, v x ^ (2 : Real) ∂μ) = 1 := by
    calc
      (∫ x, v x ^ (2 : Real) ∂μ) = ∫ x, v x ^ (2 : Nat) ∂μ := by
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards with x
        exact Real.rpow_natCast (v x) 2
      _ = 1 := hmass'
  have hgrad_cont : Continuous gradNorm := by
    have hinner := TangentBundle.continuous_g_inner_of_smooth_sections
      (I := I) (M := M) g
      (gradG (I := I) g ⟨_, hv⟩) (gradG (I := I) g ⟨_, hv⟩)
    have hinner' : Continuous (fun x ↦
        g.inner x (gradFun (I := I) g v x) (gradFun (I := I) g v x)) :=
      hinner.congr (fun _ ↦ rfl)
    exact Real.continuous_sqrt.comp hinner'
  have hv_mem2 : _root_.MeasureTheory.MemLp v (2 : ENNReal) μ := by
    exact hv.continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hv_mem6 : _root_.MeasureTheory.MemLp v (6 : ENNReal) μ := by
    exact hv.continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hgrad_mem2 : _root_.MeasureTheory.MemLp gradNorm (2 : ENNReal) μ := by
    exact hgrad_cont.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hv2 : _root_.MeasureTheory.Integrable (fun x => v x ^ 2) μ := by
    exact (hv.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hlog : _root_.MeasureTheory.Integrable (fun x => v x ^ 2 * Real.log (v x)) μ := by
    have hlogv : Continuous (fun x => Real.log (v x)) :=
      hv.continuous.log fun x => (hpos x).ne'
    exact ((hv.continuous.pow 2).mul hlogv).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmom : _root_.MeasureTheory.Integrable (fun x => v x ^ (6 : Real)) μ := by
    have hpow : _root_.MeasureTheory.Integrable (fun x => v x ^ (6 : Nat)) μ :=
      (hv.continuous.pow 6).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    refine hpow.congr ?_
    filter_upwards with x
    exact (Real.rpow_natCast (v x) 6).symm
  have hlp2 : _root_.MeasureTheory.lpNorm v (2 : ENNReal) μ = 1 := by
    rw [_root_.MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      hv.continuous.aestronglyMeasurable]
    norm_num only [ENNReal.toReal_ofNat]
    simp_rw [Real.norm_eq_abs, abs_of_pos (hpos _)]
    rw [hmass_pow]
    norm_num
  have hgrad_sq : (∫ x, ‖gradNorm x‖ ^ (2 : Real) ∂μ) = A := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      (Real.sqrt (energy x)) ^ (2 : Real) =
          (Real.sqrt (energy x)) ^ (2 : Nat) := Real.rpow_natCast _ 2
      _ = energy x := Real.sq_sqrt (henergy0 x)
  have hgrad_lp2 : _root_.MeasureTheory.lpNorm gradNorm (2 : ENNReal) μ = Real.sqrt A := by
    rw [_root_.MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      hgrad_cont.aestronglyMeasurable]
    norm_num only [ENNReal.toReal_ofNat]
    rw [hgrad_sq]
    norm_num [Real.sqrt_eq_rpow]
  have hlp6_moment :
      _root_.MeasureTheory.lpNorm v (6 : ENNReal) μ =
        (∫ x, v x ^ (6 : Real) ∂μ) ^ ((6 : Real)⁻¹) := by
    rw [_root_.MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      hv.continuous.aestronglyMeasurable]
    simp_rw [Real.norm_eq_abs, abs_of_pos (hpos _)]
    norm_num
  have hmoment0 : 0 ≤ ∫ x, v x ^ (6 : Real) ∂μ := by
    exact _root_.MeasureTheory.integral_nonneg fun x => Real.rpow_nonneg (hpos x).le _
  have hmoment_eq :
      (∫ x, v x ^ (6 : Real) ∂μ) = (_root_.MeasureTheory.lpNorm v (6 : ENNReal) μ) ^ 6 := by
    rw [hlp6_moment]
    exact (Real.rpow_inv_natCast_pow hmoment0 (by norm_num : (6 : Nat) ≠ 0)).symm
  have hentropy := entropy_le_moment μ (q := (6 : Real)) (by norm_num)
    (Filter.Eventually.of_forall hpos) hv2 hmass' hlog hmom
  rw [hmoment_eq] at hentropy
  rw [Real.log_pow (_root_.MeasureTheory.lpNorm v (6 : ENNReal) μ) 6] at hentropy
  have hentropy' :
      (∫ x, v x ^ 2 * Real.log (v x ^ 2) ∂μ) ≤
        3 * Real.log (_root_.MeasureTheory.lpNorm v (6 : ENNReal) μ) := by
    exact hentropy.trans_eq (by ring)
  have hSob' := hSob hv
  norm_num [hdim] at hSob'
  change _root_.MeasureTheory.lpNorm v (6 : ENNReal) μ ≤
    C * (_root_.MeasureTheory.lpNorm v (2 : ENNReal) μ + _root_.MeasureTheory.lpNorm gradNorm (2 : ENNReal) μ) at hSob'
  rw [hlp2, hgrad_lp2] at hSob'
  have hfactor0 : 0 ≤ 1 + Real.sqrt A := by positivity
  have hSob0 :
      lpNorm v (6 : ENNReal) μ ≤ C0 * (1 + Real.sqrt A) := by
    exact hSob'.trans (mul_le_mul_of_nonneg_right (le_max_right 1 C) hfactor0)
  have hv_ne : ¬v =ᵐ[μ] (0 : M -> Real) := by
    intro hzero
    have hsquare : (fun x => v x ^ 2) =ᵐ[μ] (0 : M -> Real) := by
      filter_upwards [hzero] with x hx
      simp [hx]
    have hz := _root_.MeasureTheory.integral_congr_ae hsquare
    have hz0 : (∫ x, v x ^ 2 ∂μ) = 0 := by
      simpa using hz
    rw [hmass'] at hz0
    norm_num at hz0
  have hlp6pos : 0 < _root_.MeasureTheory.lpNorm v (6 : ENNReal) μ := by
    have hne : _root_.MeasureTheory.lpNorm v (6 : ENNReal) μ ≠ 0 := by
      exact (_root_.MeasureTheory.lpNorm_eq_zero hv_mem6 (by norm_num)).not.mpr hv_ne
    exact lt_of_le_of_ne _root_.MeasureTheory.lpNorm_nonneg (Ne.symm hne)
  have hlogSob :
      Real.log (_root_.MeasureTheory.lpNorm v (6 : ENNReal) μ) ≤
        Real.log (C0 * (1 + Real.sqrt A)) :=
    Real.log_le_log hlp6pos hSob0
  have hentropyB :
      (∫ x, v x ^ 2 * Real.log (v x ^ 2) ∂μ) ≤
        3 * Real.log (C0 * (1 + Real.sqrt A)) := by
    exact hentropy'.trans (mul_le_mul_of_nonneg_left hlogSob (by norm_num))
  have hsquare_le : (1 + Real.sqrt A) ^ 2 ≤ 2 * (1 + A) := by
    nlinarith only [Real.sq_sqrt hA0, sq_nonneg (Real.sqrt A - 1)]
  have hlog_square :
      2 * Real.log (1 + Real.sqrt A) ≤
        Real.log 2 + Real.log (1 + A) := by
    have h := Real.log_le_log (sq_pos_of_pos (by positivity)) hsquare_le
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity)] at h
    norm_num at h ⊢
    exact h
  have hlog_scale :
      Real.log (1 + A) ≤ tau * (1 + A) - 1 - Real.log tau := by
    have h := Real.log_le_sub_one_of_pos
      (mul_pos htau0 (by positivity : 0 < 1 + A))
    rw [Real.log_mul htau0.ne' (by positivity : (1 + A) ≠ 0)] at h
    linarith
  rw [Real.log_mul hC0.ne' (by positivity : (1 + Real.sqrt A) ≠ 0)] at hentropyB
  change (∫ x, v x ^ 2 * Real.log (v x ^ 2) ∂μ) ≤
    2 * tau * A - ((3 : Real) / 2) * Real.log tau +
      (3 * Real.log C0 + ((3 : Real) / 2) * Real.log 2 +
        ((3 : Real) / 2) * tauMax - (3 : Real) / 2)
  nlinarith only [hentropyB, hlog_square, hlog_scale, htau_le,
    mul_nonneg htau0.le hA0]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.logSobolev_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.logSobolev_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.logSobolev_closed ``Submission.DifferentialGeometry.Analysis.Sobolev.logSobolev_closed

end

end DifferentialGeometry.Analysis.Sobolev
