import Submission.DifferentialGeometry.Analysis.Integration.Fatou
import Submission.DifferentialGeometry.Analysis.Integration.Convolution.SecondDifference
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Module
import Submission.DifferentialGeometry.Analysis.Integration.Integral.LocalIntegrationByParts
import Submission.DifferentialGeometry.Analysis.Convex.Convolution
import Submission.DifferentialGeometry.Analysis.Integration.Convolution.Approximation
import Submission.DifferentialGeometry.Analysis.Integration.Integral.Convergence
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Convolution _root_.Pointwise _root_.Topology

namespace ConcaveOn
open _root_.ConcaveOn

open _root_.ConcaveOn in
private theorem convolution_nonneg_left
    {f phi : Real → Real} (hf : ConcaveOn Real _root_.Set.univ f)
    (hphi : Continuous phi) (hsupp : HasCompactSupport phi)
    (hphi_nonneg : ∀ x, 0 ≤ phi x) :
    ConcaveOn Real _root_.Set.univ (phi ⋆[ContinuousLinearMap.mul Real Real] f) := by
  have hfcont : Continuous f :=
    continuousOn_univ.mp (ConcaveOn.continuousOn isOpen_univ hf)
  have hint : ∀ x : Real, _root_.MeasureTheory.Integrable (fun t ↦ phi t * f (x - t)) := by
    intro x
    simpa only [MeasureTheory.ConvolutionExistsAt, ContinuousLinearMap.mul_apply'] using
      hsupp.convolutionExists_left (ContinuousLinearMap.mul Real Real)
        hphi hfcont.locallyIntegrable x
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul, MeasureTheory.convolution_def,
    ContinuousLinearMap.mul_apply']
  rw [← _root_.MeasureTheory.integral_const_mul, ← _root_.MeasureTheory.integral_const_mul,
    ← _root_.MeasureTheory.integral_add ((hint x).const_mul a) ((hint y).const_mul b)]
  apply _root_.MeasureTheory.integral_mono
    (((hint x).const_mul a).add ((hint y).const_mul b)) (hint (a * x + b * y))
  intro t
  have hconc := hf.2 (_root_.Set.mem_univ (x - t)) (_root_.Set.mem_univ (y - t)) ha hb hab
  simp only [smul_eq_mul] at hconc
  have harg : a * (x - t) + b * (y - t) = a * x + b * y - t := by
    calc
      _ = a * x + b * y - (a + b) * t := by ring
      _ = _ := by rw [hab, one_mul]
  rw [harg] at hconc
  calc
    _ = phi t * (a * f (x - t) + b * f (y - t)) := by
      simp only [Pi.add_apply]
      ring
    _ ≤ phi t * f (a * x + b * y - t) :=
      mul_le_mul_of_nonneg_left hconc (hphi_nonneg t)

run_cmd do
  let target := ``Submission.ConcaveOn.convolution_nonneg_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `ConcaveOn.convolution_nonneg_left target :: scope.openDecls } }

open _root_.ConcaveOn in
theorem integral_mul_deriv_deriv_nonpos
    {f phi : Real → Real} (hf : ConcaveOn Real _root_.Set.univ f)
    (hphi : ContDiff Real 2 phi) (hsupp : HasCompactSupport phi)
    (hphi_nonneg : ∀ x, 0 ≤ phi x) :
    (∫ x, f x * deriv (deriv phi) x) ≤ 0 := by
  let g : Real → Real := fun x ↦ f (-x)
  have hg : ConcaveOn Real _root_.Set.univ g := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have h := hf.2 (_root_.Set.mem_univ (-x)) (_root_.Set.mem_univ (-y)) ha hb hab
    simpa only [g, smul_eq_mul, mul_neg, ← neg_add] using h
  have hgcont : Continuous g :=
    continuousOn_univ.mp (ConcaveOn.continuousOn isOpen_univ hg)
  let F : Real → Real := phi ⋆[ContinuousLinearMap.mul Real Real] g
  have hF : ContDiff Real 2 F :=
    hsupp.contDiff_convolution_left (ContinuousLinearMap.mul Real Real)
      hphi hgcont.locallyIntegrable
  have hFconc : ConcaveOn Real _root_.Set.univ F :=
    convolution_nonneg_left hg hphi.continuous hsupp hphi_nonneg
  have hFanti : Antitone (deriv F) :=
    antitoneOn_univ.mp (hFconc.antitoneOn_deriv
      (fun x _ ↦ (hF.differentiable (by norm_num)).differentiableAt))
  have hnonpos : deriv (deriv F) 0 ≤ 0 := hFanti.deriv_nonpos
  have hphi_one : ContDiff Real 1 phi := hphi.of_le (by norm_num)
  have hphi_deriv_one : ContDiff Real 1 (deriv phi) := by
    exact hphi.deriv'
  have hFderiv : deriv F =
      deriv phi ⋆[ContinuousLinearMap.mul Real Real] g := by
    funext x
    exact (hsupp.hasDerivAt_convolution_left (ContinuousLinearMap.mul Real Real)
      hphi_one hgcont.locallyIntegrable x).deriv
  have hFsecond : deriv (deriv F) 0 =
      (deriv (deriv phi) ⋆[ContinuousLinearMap.mul Real Real] g) 0 := by
    rw [hFderiv]
    exact (hsupp.deriv.hasDerivAt_convolution_left (ContinuousLinearMap.mul Real Real)
      hphi_deriv_one hgcont.locallyIntegrable 0).deriv
  rw [hFsecond] at hnonpos
  simpa only [MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply',
    zero_sub, g, neg_neg, mul_comm] using hnonpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ConcaveOn.integral_mul_deriv_deriv_nonpos then
    throwError "Refusing to shadow existing declaration ConcaveOn.integral_mul_deriv_deriv_nonpos"
  Lean.modifyEnv fun env => Lean.addAlias env `ConcaveOn.integral_mul_deriv_deriv_nonpos ``Submission.ConcaveOn.integral_mul_deriv_deriv_nonpos

open _root_.ConcaveOn in
theorem integral_mul_deriv_deriv_le_of_centered_second_difference_tendsto_ae
    {f phi q : Real → Real} (hf : ConcaveOn Real _root_.Set.univ f)
    (hphi : ContDiff Real 2 phi) (hsupp : HasCompactSupport phi)
    (hphi_nonneg : ∀ x, 0 ≤ phi x)
    (h : Nat → Real) (hh : _root_.Filter.Tendsto h _root_.Filter.atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0)
    (hq : _root_.MeasureTheory.Integrable (fun x ↦ q x * phi x))
    (hlim : ∀ᵐ x ∂volume, _root_.Filter.Tendsto
      (fun n ↦ (f (x + h n) - 2 * f x + f (x - h n)) / (h n) ^ 2)
      _root_.Filter.atTop (𝓝 (q x))) :
    (∫ x, f x * deriv (deriv phi) x) ≤ ∫ x, q x * phi x := by
  have hfcont : Continuous f :=
    continuousOn_univ.mp (ConcaveOn.continuousOn isOpen_univ hf)
  let g : Real → Real := fun x ↦ f (-x)
  have hgcont : Continuous g := hfcont.comp _root_.ContinuousNeg.continuous_neg
  let F : Real → Real := phi ⋆[ContinuousLinearMap.mul Real Real] g
  have hF : ContDiff Real 2 F :=
    hsupp.contDiff_convolution_left (ContinuousLinearMap.mul Real Real)
      hphi hgcont.locallyIntegrable
  have hphi_one : ContDiff Real 1 phi := hphi.of_le (by norm_num)
  have hphi_deriv_one : ContDiff Real 1 (deriv phi) := hphi.deriv'
  have hFderiv : deriv F =
      deriv phi ⋆[ContinuousLinearMap.mul Real Real] g := by
    funext x
    exact (hsupp.hasDerivAt_convolution_left (ContinuousLinearMap.mul Real Real)
      hphi_one hgcont.locallyIntegrable x).deriv
  have hFsecond : deriv (deriv F) 0 = ∫ x, f x * deriv (deriv phi) x := by
    rw [hFderiv]
    have hraw := (hsupp.deriv.hasDerivAt_convolution_left
      (μ := _root_.MeasureTheory.MeasureSpace.volume) (ContinuousLinearMap.mul Real Real) hphi_deriv_one
      hgcont.locallyIntegrable 0).deriv
    simpa only [MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply',
      g, zero_sub, neg_neg, mul_comm] using hraw
  have hFvalue : ∀ a, F a = ∫ x, f (x - a) * phi x := by
    intro a
    simp only [F, MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply', g]
    apply _root_.MeasureTheory.integral_congr_ae
    exact Eventually.of_forall fun x ↦ by simp only [neg_sub, mul_comm]
  let D : Nat → Real → Real := fun n x ↦
    (f (x + h n) - 2 * f x + f (x - h n)) / (h n) ^ 2 * phi x
  have hDint : ∀ n, _root_.MeasureTheory.Integrable (D n) := by
    intro n
    have hcont : Continuous (D n) := by
      dsimp only [D]
      fun_prop
    exact hcont.integrable_of_hasCompactSupport hsupp.mul_left
  have hDnonpos : ∀ n, ∀ x, D n x ≤ 0 := by
    intro n x
    have hconc := hf.2 (_root_.Set.mem_univ (x + h n)) (_root_.Set.mem_univ (x - h n))
      (show (0 : Real) ≤ 1 / 2 by norm_num)
      (show (0 : Real) ≤ 1 / 2 by norm_num) (by norm_num)
    simp only [smul_eq_mul] at hconc
    have hmid : (1 / 2 : Real) * (x + h n) + 1 / 2 * (x - h n) = x := by ring
    rw [hmid] at hconc
    have hnum : f (x + h n) - 2 * f x + f (x - h n) ≤ 0 := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg (h n))) (hphi_nonneg x)
  have hpair : ∀ n, (∫ x, D n x) =
      (F (h n) - 2 * F 0 + F (-h n)) / (h n) ^ 2 := by
    intro n
    have hp : _root_.MeasureTheory.Integrable (fun x ↦ f (x + h n) * phi x) := by
      apply Continuous.integrable_of_hasCompactSupport _ hsupp.mul_left
      exact (hfcont.comp (continuous_id.add continuous_const)).mul hphi.continuous
    have hm : _root_.MeasureTheory.Integrable (fun x ↦ f (x - h n) * phi x) := by
      apply Continuous.integrable_of_hasCompactSupport _ hsupp.mul_left
      exact (hfcont.comp (continuous_id.sub continuous_const)).mul hphi.continuous
    have hz : _root_.MeasureTheory.Integrable (fun x ↦ f x * phi x) :=
      (hfcont.mul hphi.continuous).integrable_of_hasCompactSupport hsupp.mul_left
    calc
      (∫ x, D n x) =
          ∫ x, ((f (x + h n) * phi x - 2 * (f x * phi x)) +
            f (x - h n) * phi x) / (h n) ^ 2 := by
        apply _root_.MeasureTheory.integral_congr_ae
        exact Eventually.of_forall fun x ↦ by dsimp only [D]; ring
      _ = ((∫ x, f (x + h n) * phi x) - 2 * (∫ x, f x * phi x) +
          (∫ x, f (x - h n) * phi x)) / (h n) ^ 2 := by
        have hadd := _root_.MeasureTheory.integral_add (hp.sub (hz.const_mul 2)) hm
        have hsub := _root_.MeasureTheory.integral_sub hp (hz.const_mul 2)
        simp only [Pi.sub_apply] at hadd hsub
        rw [_root_.MeasureTheory.integral_div, hadd, hsub, _root_.MeasureTheory.integral_const_mul]
      _ = _ := by
        rw [hFvalue, hFvalue, hFvalue]
        simp only [sub_zero, sub_neg_eq_add]
        ring
  have hhne : _root_.Filter.Tendsto h _root_.Filter.atTop (𝓝[≠] (0 : Real)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hh, Eventually.of_forall hne⟩
  have hpairlim : _root_.Filter.Tendsto (fun n ↦ ∫ x, D n x) _root_.Filter.atTop
      (𝓝 (∫ x, f x * deriv (deriv phi) x)) := by
    have hraw := (hF.tendsto_centered_second_difference 0).comp hhne
    simp only [Function.comp_def, zero_add, zero_sub, hFsecond] at hraw
    exact hraw.congr (fun n ↦ (hpair n).symm)
  apply MeasureTheory.tendsto_integral_le_integral_of_nonpos hDint hq
    (fun n ↦ Eventually.of_forall (hDnonpos n)) ?_ hpairlim
  filter_upwards [hlim] with x hx
  exact hx.mul_const (phi x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ConcaveOn.integral_mul_deriv_deriv_le_of_centered_second_difference_tendsto_ae then
    throwError "Refusing to shadow existing declaration ConcaveOn.integral_mul_deriv_deriv_le_of_centered_second_difference_tendsto_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `ConcaveOn.integral_mul_deriv_deriv_le_of_centered_second_difference_tendsto_ae ``Submission.ConcaveOn.integral_mul_deriv_deriv_le_of_centered_second_difference_tendsto_ae

end ConcaveOn

namespace DifferentialGeometry.Analysis

theorem integral_mul_deriv_deriv_le_of_concaveOn_sub_quadratic
    {f phi q : Real → Real} {U : Set Real} (C : Real)
    (hf : ConcaveOn Real U (fun x ↦ f x - C * x ^ 2 / 2)) (hU : IsOpen U)
    (hphi : ContDiff Real 2 phi) (hsupp : HasCompactSupport phi)
    (hsuppU : tsupport phi ⊆ U) (hphi_nonneg : ∀ x, 0 ≤ phi x)
    (h : Nat → Real) (hh : _root_.Filter.Tendsto h _root_.Filter.atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0)
    (hq : _root_.MeasureTheory.Integrable (fun x ↦ q x * phi x))
    (hlim : ∀ᵐ x ∂volume, x ∈ U → _root_.Filter.Tendsto
      (fun n ↦ (f (x + h n) - 2 * f x + f (x - h n)) / (h n) ^ 2)
      _root_.Filter.atTop (𝓝 (q x))) :
    (∫ x, f x * deriv (deriv phi) x) ≤ ∫ x, q x * phi x := by
  classical
  obtain ⟨V, hV, hVU⟩ := compact_open_separated_add_right hsupp.isCompact hU hsuppU
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hV
  let delta : Real := epsilon / 2
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  let K : Set Real := tsupport phi + Metric.closedBall 0 delta
  have hK : IsCompact K := hsupp.isCompact.add (_root_.ProperSpace.isCompact_closedBall 0 delta)
  have hKU : K ⊆ U := by
    intro z hz
    rcases hz with ⟨x, hx, v, hv, rfl⟩
    apply hVU
    refine ⟨x, hx, v, hball ?_, rfl⟩
    apply Metric.mem_ball.mpr
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hv) (by dsimp only [delta]; linarith)
  have hsuppK : tsupport phi ⊆ K := by
    intro x hx
    exact ⟨x, hx, 0, Metric.mem_closedBall_self hdelta.le, add_zero x⟩
  have hshift : ∀ x ∈ tsupport phi, ∀ a : Real, |a| ≤ delta →
      x + a ∈ K ∧ x - a ∈ K := by
    intro x hx a ha
    constructor
    · exact ⟨x, hx, a, by simpa only [Metric.mem_closedBall, dist_zero_right,
        Real.norm_eq_abs] using ha, rfl⟩
    · exact ⟨x, hx, -a, by simpa only [Metric.mem_closedBall, dist_zero_right,
        Real.norm_eq_abs, abs_neg] using ha, (sub_eq_add_neg x a).symm⟩
  have hpoly : Continuous (fun x : Real ↦ C * x ^ 2 / 2) := by fun_prop
  have hfcont : ContinuousOn f U := by
    have hsum : ContinuousOn (fun x ↦ (f x - C * x ^ 2 / 2) + C * x ^ 2 / 2) U :=
      (ConcaveOn.continuousOn hU hf).add hpoly.continuousOn
    simpa only [sub_add_cancel] using hsum
  let F : Real → Real := K.indicator f
  have hFint : _root_.MeasureTheory.Integrable F :=
    (ContinuousOn.integrableOn_compact hK (hfcont.mono hKU)).integrable_indicator
      hK.measurableSet
  have hsmall : ∀ᶠ n in _root_.Filter.atTop, |h n| ≤ delta := by
    have hevent := hh (Metric.ball_mem_nhds (0 : Real) hdelta)
    filter_upwards [hevent] with n hn
    have hnabs : |h n| < delta := by
      simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hn
    exact hnabs.le
  let D : Nat → Real → Real := fun n x ↦
    (F (x + h n) - 2 * F x + F (x - h n)) / (h n) ^ 2 * phi x
  have hDint : ∀ n, _root_.MeasureTheory.Integrable (D n) := by
    intro n
    have hraw : _root_.MeasureTheory.Integrable (fun x ↦
        (F (x + h n) - 2 * F x + F (x - h n)) / (h n) ^ 2) :=
      (((hFint.comp_add_right (h n)).sub (hFint.const_mul 2)).add
        (hFint.comp_sub_right (h n))).div_const _
    simpa only [D, smul_eq_mul] using
      hraw.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hphi.continuous hsupp
  have hDevent : ∀ᶠ n in _root_.Filter.atTop, ∀ᵐ x ∂volume, D n x ≤ C * phi x := by
    filter_upwards [hsmall] with n hn
    apply Eventually.of_forall
    intro x
    by_cases hx : phi x = 0
    · simp only [D, hx, _root_.MulZeroClass.mul_zero, le_refl]
    have hxK : x ∈ tsupport phi := subset_tsupport phi hx
    have hplus := (hshift x hxK (h n) hn).1
    have hminus := (hshift x hxK (h n) hn).2
    have hconc := hf.2 (hKU hplus) (hKU hminus)
      (show (0 : Real) ≤ 1 / 2 by norm_num)
      (show (0 : Real) ≤ 1 / 2 by norm_num) (by norm_num)
    simp only [smul_eq_mul] at hconc
    have hmid : (1 / 2 : Real) * (x + h n) + 1 / 2 * (x - h n) = x := by ring
    rw [hmid] at hconc
    have hnum : f (x + h n) - 2 * f x + f (x - h n) ≤ C * (h n) ^ 2 := by
      nlinarith [hconc]
    dsimp only [D, F]
    rw [_root_.Set.indicator_of_mem hplus, _root_.Set.indicator_of_mem (hsuppK hxK), _root_.Set.indicator_of_mem hminus]
    exact mul_le_mul_of_nonneg_right
      ((div_le_iff₀ (sq_pos_of_ne_zero (hne n))).mpr hnum) (hphi_nonneg x)
  have hDlim : ∀ᵐ x ∂volume,
      Tendsto (fun n ↦ D n x) _root_.Filter.atTop (𝓝 (q x * phi x)) := by
    filter_upwards [hlim] with x hx
    by_cases hxzero : phi x = 0
    · simpa only [D, hxzero, _root_.MulZeroClass.mul_zero] using
        (tendsto_const_nhds : _root_.Filter.Tendsto (fun _ : Nat ↦ (0 : Real)) _root_.Filter.atTop (𝓝 0))
    have hxK : x ∈ tsupport phi := subset_tsupport phi hxzero
    apply ((hx (hsuppU hxK)).mul_const (phi x)).congr'
    filter_upwards [hsmall] with n hn
    have hplus := (hshift x hxK (h n) hn).1
    have hminus := (hshift x hxK (h n) hn).2
    simp only [D, F, _root_.Set.indicator_of_mem hplus,
      _root_.Set.indicator_of_mem (hsuppK hxK), _root_.Set.indicator_of_mem hminus]
  have hpair := hFint.tendsto_integral_mul_centered_second_difference hphi hsupp h hh hne
  have hCint : _root_.MeasureTheory.Integrable (fun x ↦ C * phi x) :=
    (hphi.continuous.integrable_of_hasCompactSupport hsupp).const_mul C
  have hbound := MeasureTheory.tendsto_integral_le_integral_of_eventually_le
    hDint hq hCint hDevent hDlim hpair
  have heq : (∫ x, F x * deriv (deriv phi) x) =
      ∫ x, f x * deriv (deriv phi) x := by
    apply _root_.MeasureTheory.integral_congr_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ tsupport phi
    · simp only [F, _root_.Set.indicator_of_mem (hsuppK hx)]
    · have hx' : x ∉ tsupport (deriv phi) :=
        fun hmem ↦ hx (tsupport_deriv_subset hmem)
      simp only [deriv_of_notMem_tsupport hx', _root_.MulZeroClass.mul_zero]
  rwa [heq] at hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_mul_deriv_deriv_le_of_concaveOn_sub_quadratic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_mul_deriv_deriv_le_of_concaveOn_sub_quadratic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_mul_deriv_deriv_le_of_concaveOn_sub_quadratic ``Submission.DifferentialGeometry.Analysis.integral_mul_deriv_deriv_le_of_concaveOn_sub_quadratic

end DifferentialGeometry.Analysis

namespace ConcaveOn
open _root_.ConcaveOn

open _root_.ConcaveOn in
theorem integral_mul_deriv_deriv_le_of_centered_second_difference_tendsto_ae_on
    {f phi q : Real → Real} {U : Set Real}
    (hf : ConcaveOn Real U f) (hU : IsOpen U)
    (hphi : ContDiff Real 2 phi) (hsupp : HasCompactSupport phi)
    (hsuppU : tsupport phi ⊆ U) (hphi_nonneg : ∀ x, 0 ≤ phi x)
    (h : Nat → Real) (hh : _root_.Filter.Tendsto h _root_.Filter.atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0)
    (hq : _root_.MeasureTheory.Integrable (fun x ↦ q x * phi x))
    (hlim : ∀ᵐ x ∂volume, x ∈ U → _root_.Filter.Tendsto
      (fun n ↦ (f (x + h n) - 2 * f x + f (x - h n)) / (h n) ^ 2)
      _root_.Filter.atTop (𝓝 (q x))) :
    (∫ x, f x * deriv (deriv phi) x) ≤ ∫ x, q x * phi x := by
  have hfzero : ConcaveOn Real U (fun x ↦ f x - (0 : Real) * x ^ 2 / 2) := by
    simpa only [_root_.MulZeroClass.zero_mul, zero_div, sub_zero] using hf
  exact DifferentialGeometry.Analysis.integral_mul_deriv_deriv_le_of_concaveOn_sub_quadratic
    0 hfzero hU hphi hsupp hsuppU hphi_nonneg h hh hne hq hlim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ConcaveOn.integral_mul_deriv_deriv_le_of_centered_second_difference_tendsto_ae_on then
    throwError "Refusing to shadow existing declaration ConcaveOn.integral_mul_deriv_deriv_le_of_centered_second_difference_tendsto_ae_on"
  Lean.modifyEnv fun env => Lean.addAlias env `ConcaveOn.integral_mul_deriv_deriv_le_of_centered_second_difference_tendsto_ae_on ``Submission.ConcaveOn.integral_mul_deriv_deriv_le_of_centered_second_difference_tendsto_ae_on

end ConcaveOn

namespace DifferentialGeometry.Analysis

theorem integral_mul_fderiv_fderiv_le_of_concaveOn_sub_quadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
    [MeasurableSpace E] [BorelSpace E] {mu : _root_.MeasureTheory.Measure E}
    [_root_.MeasureTheory.SFinite mu] [mu.IsAddLeftInvariant] [mu.IsNegInvariant] [_root_.MeasureTheory.IsFiniteMeasureOnCompacts mu]
    {f phi q : E → Real} {U : Set E} (B : E →L[Real] E →L[Real] Real)
    (hf : ConcaveOn Real U (fun x ↦ f x - B x x / 2)) (hU : IsOpen U)
    (hphi : ContDiff Real 2 phi) (hsupp : HasCompactSupport phi)
    (hsuppU : tsupport phi ⊆ U) (hphi_nonneg : ∀ x, 0 ≤ phi x) (v : E)
    (h : Nat → Real) (hh : _root_.Filter.Tendsto h _root_.Filter.atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0)
    (hq : _root_.MeasureTheory.Integrable (fun x ↦ q x * phi x) mu)
    (hlim : ∀ᵐ x ∂mu, x ∈ U → _root_.Filter.Tendsto
      (fun n ↦ (f (x + h n • v) - 2 * f x + f (x - h n • v)) / (h n) ^ 2)
      _root_.Filter.atTop (𝓝 (q x))) :
    (∫ x, f x * fderiv Real (fun y ↦ fderiv Real phi y v) x v ∂mu) ≤
      ∫ x, q x * phi x ∂mu := by
  classical
  obtain ⟨V, hV, hVU⟩ := compact_open_separated_add_right hsupp.isCompact hU hsuppU
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hV
  let delta : Real := epsilon / 2
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  let K : Set E := tsupport phi + Metric.closedBall 0 delta
  have hK : IsCompact K := hsupp.isCompact.add (_root_.ProperSpace.isCompact_closedBall 0 delta)
  have hKU : K ⊆ U := by
    intro z hz
    rcases hz with ⟨x, hx, w, hw, rfl⟩
    apply hVU
    refine ⟨x, hx, w, hball ?_, rfl⟩
    apply Metric.mem_ball.mpr
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hw) (by dsimp only [delta]; linarith)
  have hsuppK : tsupport phi ⊆ K := by
    intro x hx
    exact ⟨x, hx, 0, Metric.mem_closedBall_self hdelta.le, add_zero x⟩
  have hshift : ∀ x ∈ tsupport phi, ∀ w : E, ‖w‖ ≤ delta →
      x + w ∈ K ∧ x - w ∈ K := by
    intro x hx w hw
    constructor
    · exact ⟨x, hx, w, by simpa only [Metric.mem_closedBall, dist_zero_right] using hw, rfl⟩
    · exact ⟨x, hx, -w, by simpa only [Metric.mem_closedBall, dist_zero_right,
        norm_neg] using hw, (sub_eq_add_neg x w).symm⟩
  have hpoly : Continuous (fun x : E ↦ B x x / 2) := by fun_prop
  have hfcont : ContinuousOn f U := by
    have hsum : ContinuousOn (fun x ↦ (f x - B x x / 2) + B x x / 2) U :=
      (ConcaveOn.continuousOn hU hf).add hpoly.continuousOn
    simpa only [sub_add_cancel] using hsum
  let F : E → Real := K.indicator f
  have hFint : _root_.MeasureTheory.Integrable F mu :=
    (ContinuousOn.integrableOn_compact hK (hfcont.mono hKU)).integrable_indicator
      hK.measurableSet
  have hsmall : ∀ᶠ n in _root_.Filter.atTop, ‖h n • v‖ ≤ delta := by
    have hvec : _root_.Filter.Tendsto (fun n ↦ h n • v) _root_.Filter.atTop (𝓝 (0 : E)) := by
      simpa only [zero_smul] using hh.smul_const v
    have hevent := hvec (Metric.ball_mem_nhds (0 : E) hdelta)
    filter_upwards [hevent] with n hn
    have hnorm : ‖h n • v‖ < delta := by
      simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using hn
    exact hnorm.le
  let D : Nat → E → Real := fun n x ↦
    (F (x + h n • v) - 2 * F x + F (x - h n • v)) / (h n) ^ 2 * phi x
  have hDint : ∀ n, _root_.MeasureTheory.Integrable (D n) mu := by
    intro n
    have hraw : _root_.MeasureTheory.Integrable (fun x ↦
        (F (x + h n • v) - 2 * F x + F (x - h n • v)) / (h n) ^ 2) mu :=
      (((hFint.comp_add_right (h n • v)).sub (hFint.const_mul 2)).add
        (hFint.comp_sub_right (h n • v))).div_const _
    simpa only [D, smul_eq_mul] using
      hraw.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hphi.continuous hsupp
  have hDevent : ∀ᶠ n in _root_.Filter.atTop, ∀ᵐ x ∂mu, D n x ≤ B v v * phi x := by
    filter_upwards [hsmall] with n hn
    apply Eventually.of_forall
    intro x
    by_cases hx : phi x = 0
    · simp only [D, hx, _root_.MulZeroClass.mul_zero, le_refl]
    have hxK : x ∈ tsupport phi := subset_tsupport phi hx
    have hplus := (hshift x hxK (h n • v) hn).1
    have hminus := (hshift x hxK (h n • v) hn).2
    have hconc := hf.2 (hKU hplus) (hKU hminus)
      (show (0 : Real) ≤ 1 / 2 by norm_num)
      (show (0 : Real) ≤ 1 / 2 by norm_num) (by norm_num)
    have hmid : (1 / 2 : Real) • (x + h n • v) + (1 / 2 : Real) • (x - h n • v) = x := by
      module
    rw [hmid] at hconc
    simp only [smul_eq_mul, map_add, map_sub, map_smul,
      add_apply, sub_apply, smul_apply] at hconc
    have hnum : f (x + h n • v) - 2 * f x + f (x - h n • v) ≤
        B v v * (h n) ^ 2 := by nlinarith [hconc]
    dsimp only [D, F]
    rw [_root_.Set.indicator_of_mem hplus, _root_.Set.indicator_of_mem (hsuppK hxK), _root_.Set.indicator_of_mem hminus]
    exact mul_le_mul_of_nonneg_right
      ((div_le_iff₀ (sq_pos_of_ne_zero (hne n))).mpr hnum) (hphi_nonneg x)
  have hDlim : ∀ᵐ x ∂mu,
      Tendsto (fun n ↦ D n x) _root_.Filter.atTop (𝓝 (q x * phi x)) := by
    filter_upwards [hlim] with x hx
    by_cases hxzero : phi x = 0
    · simpa only [D, hxzero, _root_.MulZeroClass.mul_zero] using
        (tendsto_const_nhds : _root_.Filter.Tendsto (fun _ : Nat ↦ (0 : Real)) _root_.Filter.atTop (𝓝 0))
    have hxK : x ∈ tsupport phi := subset_tsupport phi hxzero
    apply ((hx (hsuppU hxK)).mul_const (phi x)).congr'
    filter_upwards [hsmall] with n hn
    have hplus := (hshift x hxK (h n • v) hn).1
    have hminus := (hshift x hxK (h n • v) hn).2
    simp only [D, F, _root_.Set.indicator_of_mem hplus,
      _root_.Set.indicator_of_mem (hsuppK hxK), _root_.Set.indicator_of_mem hminus]
  have hpair := hFint.tendsto_integral_mul_directional_second_difference
    hphi hsupp v h hh hne
  have hBint : _root_.MeasureTheory.Integrable (fun x ↦ B v v * phi x) mu :=
    (hphi.continuous.integrable_of_hasCompactSupport hsupp).const_mul (B v v)
  have hbound := MeasureTheory.tendsto_integral_le_integral_of_eventually_le
    hDint hq hBint hDevent hDlim hpair
  have heq : (∫ x, F x * fderiv Real (fun y ↦ fderiv Real phi y v) x v ∂mu) =
      ∫ x, f x * fderiv Real (fun y ↦ fderiv Real phi y v) x v ∂mu := by
    apply _root_.MeasureTheory.integral_congr_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ tsupport phi
    · simp only [F, _root_.Set.indicator_of_mem (hsuppK hx)]
    · have hx' : x ∉ tsupport (fun y ↦ fderiv Real phi y v) :=
        fun hmem ↦ hx (tsupport_fderiv_apply_subset Real v hmem)
      simp only [fderiv_of_notMem_tsupport Real hx', zero_apply, _root_.MulZeroClass.mul_zero]
  rwa [heq] at hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_mul_fderiv_fderiv_le_of_concaveOn_sub_quadratic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_mul_fderiv_fderiv_le_of_concaveOn_sub_quadratic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_mul_fderiv_fderiv_le_of_concaveOn_sub_quadratic ``Submission.DifferentialGeometry.Analysis.integral_mul_fderiv_fderiv_le_of_concaveOn_sub_quadratic

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Topology _root_.Convolution

private theorem integral_hessian_apply_le_of_integral_identity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : _root_.MeasureTheory.Measure E} [μ.IsAddHaarMeasure]
    {u : E → ℝ} (A : E →L[ℝ] E →L[ℝ] ℝ) (hA : A.flip = A)
    (hu : ConvexOn ℝ _root_.Set.univ (fun x => u x + (1 / 2 : ℝ) * A x x))
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ᵐ x ∂μ, (B x).flip = B x ∧ ∃ p : E →L[ℝ] ℝ,
      (fun y => u y - u x - p (y - x) - (1 / 2 : ℝ) * B x (y - x) (y - x))
        =o[𝓝 x] (fun y => ‖y - x‖ ^ 2))
    {Ω : Set E} (hΩ : IsOpen Ω)
    {φ : E → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) (hφ0 : ∀ x, 0 ≤ φ x)
    {V : E → E} (hV : ContinuousOn V Ω)
    {K : E → ℝ} (hK : Continuous K) (hKc : HasCompactSupport K)
    (hidentity : ∀ g : E → ℝ, ContDiff ℝ 2 g →
      (∫ x, fderiv ℝ (fderiv ℝ g) x (V x) (V x) * φ x ∂μ) = ∫ x, g x * K x ∂μ) :
    _root_.MeasureTheory.Integrable (fun x => B x (V x) (V x) * φ x) μ ∧
      (∫ x, B x (V x) (V x) * φ x ∂μ) ≤ ∫ x, u x * K x ∂μ := by
  have huc : Continuous u := by
    have hq : Continuous (fun x => (1 / 2 : ℝ) * A x x) := by fun_prop
    have h : Continuous (fun x => (u x + (1 / 2 : ℝ) * A x x) - (1 / 2 : ℝ) * A x x) :=
      (continuousOn_univ.mp (hu.continuousOn isOpen_univ)).sub hq
    simpa only [add_sub_cancel_right] using h
  let χ : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩
  let κ := χ.normed μ
  have hκd : ContDiff ℝ 2 κ := χ.contDiff_normed
  have hκc : HasCompactSupport κ := χ.hasCompactSupport_normed
  have hκ0 : ∀ x, 0 ≤ κ x := χ.nonneg_normed
  have hκm : ∫ x, κ x ∂μ = 1 := χ.integral_normed
  let k : ℝ → E → ℝ := fun r z => (r ^ Module.finrank ℝ E)⁻¹ * κ (r⁻¹ • z)
  let g : ℝ → E → ℝ := fun r => k r ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u
  have hkd (r : ℝ) : ContDiff ℝ 2 (k r) :=
    contDiff_const.mul (hκd.comp (contDiff_const.smul contDiff_id))
  have hkc {r : ℝ} (hr : 0 < r) : HasCompactSupport (k r) := by
    have h : HasCompactSupport (fun z : E => κ (r⁻¹ • z)) :=
      hκc.comp_homeomorph (Homeomorph.smul (isUnit_iff_ne_zero.mpr (inv_ne_zero hr.ne')).unit)
    exact h.mul_left
  have hkm {r : ℝ} (hr : 0 < r) : ∫ x, k r x ∂μ = 1 := by
    dsimp only [k]
    rw [_root_.MeasureTheory.integral_const_mul, μ.integral_comp_inv_smul_of_nonneg κ hr.le, hκm]
    simp only [smul_eq_mul, mul_one, inv_mul_cancel₀ (pow_ne_zero _ hr.ne')]
  have hg {r : ℝ} (hr : 0 < r) : ContDiff ℝ 2 (g r) :=
    (hkc hr).contDiff_convolution_left _ (hkd r) huc.locallyIntegrable
  have hlow {r : ℝ} (hr : 0 < r) (x : E) :
      -A (V x) (V x) ≤ fderiv ℝ (fderiv ℝ (g r)) x (V x) (V x) := by
    have hk0 : ∀ᵐ z ∂μ, 0 ≤ k r z := _root_.MeasureTheory.ae_of_all μ fun z =>
      mul_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _)) (hκ0 _)
    have h := hu.fderiv_fderiv_convolution_left_lower_bound A hA hk0
      ((hkd r).continuous.integrable_of_hasCompactSupport (hkc hr))
      (hkd r) (hkc hr) huc.locallyIntegrable x (V x)
    simpa only [hkm hr, neg_one_mul] using h
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hrt : _root_.Filter.Tendsto r _root_.Filter.atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hr⟩
  have huni := DifferentialGeometry.Analysis.tendstoLocallyUniformly_convolution_rescale
    (μ := μ) hκ0 (hκc.isCompact.isBounded.subset (subset_tsupport κ)) hκm huc
  have hKuni : TendstoUniformlyOn g u (𝓝[>] (0 : ℝ)) (Function.support K) :=
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hKc.isCompact).mp
      huni.tendstoLocallyUniformlyOn).mono (subset_tsupport K)
  have hgi : ∀ᶠ t in 𝓝[>] (0 : ℝ), _root_.MeasureTheory.Integrable (fun x => K x • g t x) μ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hK.smul (hg ht).continuous).integrable_of_hasCompactSupport hKc.smul_right
  have hui : _root_.MeasureTheory.Integrable (fun x => K x • u x) μ :=
    (hK.smul huc).integrable_of_hasCompactSupport hKc.smul_right
  have hI := hKuni.integral_smul (hK.integrable_of_hasCompactSupport hKc) hgi hui
  have hIBP (n : ℕ) : (∫ x, fderiv ℝ (fderiv ℝ (g (r n))) x (V x) (V x) * φ x ∂μ) =
      ∫ x, g (r n) x * K x ∂μ := hidentity _ (hg (hr n))
  have hint : _root_.Filter.Tendsto (fun n => ∫ x, fderiv ℝ (fderiv ℝ (g (r n))) x (V x) (V x) * φ x ∂μ)
      atTop (𝓝 (∫ x, u x * K x ∂μ)) := by
    simp_rw [hIBP]
    simpa only [Function.comp_def, smul_eq_mul, mul_comm] using hI.comp hrt
  have hFi (n : ℕ) : _root_.MeasureTheory.Integrable (fun x => fderiv ℝ (fderiv ℝ (g (r n))) x (V x) (V x) * φ x) μ := by
    have hc : ContinuousOn (fun x => fderiv ℝ (fderiv ℝ (g (r n))) x (V x) (V x)) Ω :=
      ((((hg (hr n)).fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).continuousOn.clm_apply
        hV).clm_apply hV
    exact ((hc.mul hφ.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)).integrable_of_hasCompactSupport hφc.mul_left
  have hlower : _root_.MeasureTheory.Integrable (fun x => -A (V x) (V x) * φ x) μ := by
    have hc : ContinuousOn (fun x => -A (V x) (V x) * φ x) Ω :=
      (((A.continuous.comp_continuousOn hV).clm_apply hV).neg).mul hφ.continuousOn
    exact (hc.continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hφs)).integrable_of_hasCompactSupport hφc.mul_left
  have hbound (n : ℕ) : (fun x => -A (V x) (V x) * φ x) ≤ᵐ[μ]
      (fun x => fderiv ℝ (fderiv ℝ (g (r n))) x (V x) (V x) * φ x) :=
    _root_.MeasureTheory.ae_of_all μ fun x => mul_le_mul_of_nonneg_right (hlow (hr n) x) (hφ0 x)
  have hlim : ∀ᵐ x ∂μ, _root_.Filter.Tendsto
      (fun n => fderiv ℝ (fderiv ℝ (g (r n))) x (V x) (V x) * φ x)
      atTop (𝓝 (B x (V x) (V x) * φ x)) := by
    filter_upwards [hB] with x hx
    obtain ⟨hsym, p, hp⟩ := hx
    have ht := DifferentialGeometry.Analysis.tendsto_fderiv_fderiv_convolution_rescale_of_isLittleO
      hκd hκc hκm huc.locallyIntegrable hsym hp
    have heval : Continuous (fun D : E →L[ℝ] E →L[ℝ] ℝ => D (V x) (V x)) := by fun_prop
    exact ((heval.tendsto (B x)).comp (ht.comp hrt)).mul_const _
  exact MeasureTheory.integrable_and_integral_le_of_tendsto_ae hFi hlower hbound hlim hint

run_cmd do
  let target := ``Submission.integral_hessian_apply_le_of_integral_identity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `integral_hessian_apply_le_of_integral_identity target :: scope.openDecls } }

open _root_.ConvexOn in
theorem ConvexOn.integral_hessian_vector_field_le
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    [MeasurableSpace E] [BorelSpace E] {μ : _root_.MeasureTheory.Measure E} [μ.IsAddHaarMeasure]
    (b : Module.Basis ι ℝ E) {u : E → ℝ} (A : E →L[ℝ] E →L[ℝ] ℝ) (hA : A.flip = A)
    (hu : ConvexOn ℝ _root_.Set.univ (fun x => u x + (1 / 2 : ℝ) * A x x))
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ᵐ x ∂μ, (B x).flip = B x ∧ ∃ p : E →L[ℝ] ℝ,
      (fun y => u y - u x - p (y - x) - (1 / 2 : ℝ) * B x (y - x) (y - x))
        =o[𝓝 x] (fun y => ‖y - x‖ ^ 2))
    {Ω : Set E} (hΩ : IsOpen Ω)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ω) (hφ0 : ∀ x, 0 ≤ φ x)
    {V : E → E} (hV : ContDiffOn ℝ 2 V Ω) :
    _root_.MeasureTheory.Integrable (fun x => B x (V x) (V x) * φ x) μ ∧
      (∫ x, B x (V x) (V x) * φ x ∂μ) ≤
        ∑ i, ∑ j, ∫ x, u x * fderiv ℝ
          (fderiv ℝ (fun y => b.repr (V y) i * b.repr (V y) j * φ y)) x (b j) (b i) ∂μ := by
  let : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  have huc : Continuous u := by
    have hq : Continuous (fun x => (1 / 2 : ℝ) * A x x) := by fun_prop
    have h : Continuous (fun x => (u x + (1 / 2 : ℝ) * A x x) - (1 / 2 : ℝ) * A x x) :=
      (continuousOn_univ.mp (hu.continuousOn isOpen_univ)).sub hq
    simpa only [add_sub_cancel_right] using h
  let ψ (i j : ι) : E → ℝ := fun x => b.repr (V x) i * b.repr (V x) j * φ x
  have hψs (i j : ι) : tsupport (ψ i j) ⊆ Ω := tsupport_mul_subset_right.trans hφs
  have hψ (i j : ι) : ContDiff ℝ 2 (ψ i j) :=
    ((((b.coord i).toContinuousLinearMap.contDiff.comp_contDiffOn hV).mul
      ((b.coord j).toContinuousLinearMap.contDiff.comp_contDiffOn hV)).mul
        hφ.contDiffOn).contDiff_of_tsupport_subset hΩ (hψs i j)
  have hψc (i j : ι) : HasCompactSupport (ψ i j) := hφc.mul_left
  let D (i j : ι) : E → ℝ := fun x => fderiv ℝ (fderiv ℝ (ψ i j)) x (b j) (b i)
  have hD (i j : ι) : Continuous (D i j) :=
    ((((hψ i j).fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).clm_apply continuous_const
  have hDc (i j : ι) : HasCompactSupport (D i j) :=
    (((hψc i j).fderiv ℝ).fderiv_apply ℝ (b j)).comp_left
      (g := fun C : E →L[ℝ] ℝ => C (b i)) rfl
  have hDs (i j : ι) : tsupport (D i j) ⊆ Ω :=
    ((tsupport_comp_subset (g := fun C : E →L[ℝ] ℝ => C (b i)) rfl _).trans
      ((tsupport_fderiv_apply_subset ℝ (b j)).trans (tsupport_fderiv_subset ℝ))).trans (hψs i j)
  let K : E → ℝ := fun x => ∑ i, ∑ j, D i j x
  have hK : Continuous K := continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => hD i j
  have hKc : HasCompactSupport K := by
    have h : HasCompactSupport (∑ i, ∑ j, D i j) :=
      HasCompactSupport.finset_sum (fun i _ =>
        HasCompactSupport.finset_sum (fun j _ => hDc i j))
    convert h using 1
    funext x
    simp only [K, Finset.sum_apply]
  have hsum (f : E → ℝ) (hf : Continuous f) : (∫ x, f x * K x ∂μ) =
      ∑ i, ∑ j, ∫ x, f x * D i j x ∂μ := by
    have hi (i j : ι) : _root_.MeasureTheory.Integrable (fun x => f x * D i j x) μ :=
      (hf.mul (hD i j)).integrable_of_hasCompactSupport (hDc i j).mul_left
    simp only [K, Finset.mul_sum]
    rw [_root_.MeasureTheory.integral_finsetSum Finset.univ
      (fun i _ => _root_.MeasureTheory.integrable_finsetSum Finset.univ (fun j _ => hi i j))]
    exact Finset.sum_congr rfl (fun i _ => _root_.MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hi i j))
  obtain ⟨hi, hle⟩ := integral_hessian_apply_le_of_integral_identity A hA hu hB
    hΩ hφ.continuous hφc hφs hφ0 hV.continuousOn hK hKc (fun f hf => by
      rw [hsum f hf.continuous]
      have h := DifferentialGeometry.Analysis.integral_fderiv_fderiv_apply_mul_eq
        (μ := μ) b hΩ (hf.differentiable (by norm_num)).differentiableOn
        (hf.fderiv_right (m := 1) (by norm_num)).locallyLipschitz.locallyLipschitzOn
        hV hV hφ hφc hφs
      have hz (x : E) (hx : x ∉ Ω) :
          fderiv ℝ (fderiv ℝ f) x (V x) (V x) * φ x = 0 := by
        rw [image_eq_zero_of_notMem_tsupport (f := φ) (fun h => hx (hφs h)), _root_.MulZeroClass.mul_zero]
      have hDz (i j : ι) : (∫ x in Ω, f x * D i j x ∂μ) = ∫ x, f x * D i j x ∂μ :=
        _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          rw [image_eq_zero_of_notMem_tsupport (f := D i j) (fun h => hx (hDs i j h)), _root_.MulZeroClass.mul_zero])
      change (∫ x in Ω, fderiv ℝ (fderiv ℝ f) x (V x) (V x) * φ x ∂μ) =
        ∑ i, ∑ j, ∫ x in Ω, f x * D i j x ∂μ at h
      simpa only [_root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hz, hDz] using h)
  exact ⟨hi, hle.trans_eq (hsum u huc)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ConvexOn.integral_hessian_vector_field_le then
    throwError "Refusing to shadow existing declaration ConvexOn.integral_hessian_vector_field_le"
  Lean.modifyEnv fun env => Lean.addAlias env `ConvexOn.integral_hessian_vector_field_le ``Submission.ConvexOn.integral_hessian_vector_field_le

open _root_.ConvexOn in
theorem ConvexOn.integral_hessian_apply_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : _root_.MeasureTheory.Measure E} [μ.IsAddHaarMeasure]
    {u : E → ℝ} (A : E →L[ℝ] E →L[ℝ] ℝ) (hA : A.flip = A)
    (hu : ConvexOn ℝ _root_.Set.univ (fun x => u x + (1 / 2 : ℝ) * A x x))
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ᵐ x ∂μ, (B x).flip = B x ∧ ∃ p : E →L[ℝ] ℝ,
      (fun y => u y - u x - p (y - x) - (1 / 2 : ℝ) * B x (y - x) (y - x))
        =o[𝓝 x] (fun y => ‖y - x‖ ^ 2))
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ x, 0 ≤ φ x) (v : E) :
    _root_.MeasureTheory.Integrable (fun x => B x v v * φ x) μ ∧
      (∫ x, B x v v * φ x ∂μ) ≤ ∫ x, u x * fderiv ℝ (fderiv ℝ φ) x v v ∂μ := by
  let b := Module.finBasis ℝ E
  obtain ⟨hi, hle⟩ := hu.integral_hessian_vector_field_le b A hA hB isOpen_univ hφ hφc (_root_.Set.subset_univ _) hφ0
    (V := fun _ => v) contDiffOn_const
  have huc : Continuous u := by
    have hq : Continuous (fun x => (1 / 2 : ℝ) * A x x) := by fun_prop
    have h : Continuous (fun x => (u x + (1 / 2 : ℝ) * A x x) - (1 / 2 : ℝ) * A x x) :=
      (continuousOn_univ.mp (hu.continuousOn isOpen_univ)).sub hq
    simpa only [add_sub_cancel_right] using h
  have hcoeff (i j : Fin (Module.finrank ℝ E)) (x : E) :
      fderiv ℝ (fderiv ℝ (fun y => b.repr v i * b.repr v j * φ y)) x (b j) (b i) =
        b.repr v i * b.repr v j * fderiv ℝ (fderiv ℝ φ) x (b j) (b i) := by
    change fderiv ℝ (fderiv ℝ ((b.repr v i * b.repr v j) • φ)) x (b j) (b i) = _
    rw [fderiv_const_smul_field, fderiv_const_smul_field]
    rfl
  simp_rw [hcoeff] at hle
  have hDi (i j : Fin (Module.finrank ℝ E)) :
      _root_.MeasureTheory.Integrable (fun x => u x * (b.repr v i * b.repr v j *
        fderiv ℝ (fderiv ℝ φ) x (b j) (b i))) μ := by
    have hc : Continuous (fun x => u x * (b.repr v i * b.repr v j *
        fderiv ℝ (fderiv ℝ φ) x (b j) (b i))) := by
      exact huc.mul (continuous_const.mul
        ((((hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).clm_apply
          continuous_const).clm_apply continuous_const))
    have hs : HasCompactSupport (fun x => fderiv ℝ (fderiv ℝ φ) x (b j) (b i)) :=
      ((hφc.fderiv ℝ).fderiv_apply ℝ (b j)).comp_left
        (g := fun C : E →L[ℝ] ℝ => C (b i)) rfl
    exact hc.integrable_of_hasCompactSupport hs.mul_left.mul_left
  have hexp (x : E) : (∑ i, ∑ j, b.repr v i * b.repr v j *
      fderiv ℝ (fderiv ℝ φ) x (b j) (b i)) = fderiv ℝ (fderiv ℝ φ) x v v := by
    conv_rhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have heq : (∑ i, ∑ j, ∫ x, u x * (b.repr v i * b.repr v j *
      fderiv ℝ (fderiv ℝ φ) x (b j) (b i)) ∂μ) =
      ∫ x, u x * fderiv ℝ (fderiv ℝ φ) x v v ∂μ := by
    have hinner (i : Fin (Module.finrank ℝ E)) :
        (∑ j, ∫ x, u x * (b.repr v i * b.repr v j *
          fderiv ℝ (fderiv ℝ φ) x (b j) (b i)) ∂μ) =
        ∫ x, ∑ j, u x * (b.repr v i * b.repr v j *
          fderiv ℝ (fderiv ℝ φ) x (b j) (b i)) ∂μ :=
      (_root_.MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hDi i j)).symm
    simp_rw [hinner]
    rw [← _root_.MeasureTheory.integral_finsetSum Finset.univ (fun i _ =>
      _root_.MeasureTheory.integrable_finsetSum Finset.univ (fun j _ => hDi i j))]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards with x
    simpa only [Finset.mul_sum] using congrArg (fun z : ℝ => u x * z) (hexp x)
  exact ⟨hi, hle.trans_eq heq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ConvexOn.integral_hessian_apply_le then
    throwError "Refusing to shadow existing declaration ConvexOn.integral_hessian_apply_le"
  Lean.modifyEnv fun env => Lean.addAlias env `ConvexOn.integral_hessian_apply_le ``Submission.ConvexOn.integral_hessian_apply_le

end

end
