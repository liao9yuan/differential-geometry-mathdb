import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.Interval _root_.Topology

namespace DifferentialGeometry

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F]

theorem hasDerivAt_of_right
    {f f' : Real -> F} {a b t : Real} (hab : a < b)
    (hf : ContinuousOn f (_root_.Set.Icc a b)) (hf' : ContinuousOn f' (_root_.Set.Icc a b))
    (hderiv : ∀ x ∈ _root_.Set.Ico a b,
      HasDerivWithinAt f (f' x) (_root_.Set.Ici x) x)
    (ht : t ∈ _root_.Set.Ioo a b) :
    HasDerivAt f (f' t) t := by
  let g : Real -> F := fun x => f a + intervalIntegral f' a x _root_.MeasureTheory.MeasureSpace.volume
  have hint : IntervalIntegrable f' _root_.MeasureTheory.MeasureSpace.volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab.le hf'
  have hgderivIcc : ∀ x ∈ _root_.Set.Icc a b,
      HasDerivWithinAt g (f' x) (_root_.Set.Icc a b) x := by
    intro x hxIcc
    let : Fact (x ∈ _root_.Set.Icc a b) := ⟨hxIcc⟩
    have hxU : x ∈ _root_.Set.uIcc a b := by
      simpa only [_root_.Set.uIcc_of_le hab.le] using hxIcc
    have hprim : HasDerivWithinAt
        (fun y => intervalIntegral f' a y _root_.MeasureTheory.MeasureSpace.volume) (f' x) (_root_.Set.Icc a b) x :=
      intervalIntegral.integral_hasDerivWithinAt_right
        (hint.mono_set (_root_.Set.uIcc_subset_uIcc _root_.Set.left_mem_uIcc hxU))
        (hf'.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x)
        (hf' x hxIcc)
    simpa only [g] using hprim.const_add (f a)
  have hgderiv : ∀ x ∈ _root_.Set.Ico a b,
      HasDerivWithinAt g (f' x) (_root_.Set.Ici x) x := by
    intro x hx
    exact (hgderivIcc x (_root_.Set.mem_Icc_of_Ico hx)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hx)
  have hgcont : ContinuousOn g (_root_.Set.Icc a b) := by
    have hprim : ContinuousOn
        (fun x => intervalIntegral f' a x _root_.MeasureTheory.MeasureSpace.volume) (_root_.Set.Icc a b) := by
      rw [← _root_.Set.uIcc_of_le hab.le]
      exact intervalIntegral.continuousOn_primitive_interval
        ((intervalIntegrable_iff').mp hint)
    change ContinuousOn ((fun _ => f a) +
      fun x => intervalIntegral f' a x _root_.MeasureTheory.MeasureSpace.volume) (_root_.Set.Icc a b)
    exact continuousOn_const.add hprim
  have hfg : ∀ x ∈ _root_.Set.Icc a b, f x = g x := by
    apply eq_of_has_deriv_right_eq hderiv hgderiv hf hgcont
    simp only [g, intervalIntegral.integral_same, add_zero]
  have hfg_ev : f =ᶠ[nhds t] g := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with x hx
    exact hfg x hx
  have hgAt : HasDerivAt g (f' t) t := by
    have htIcc : t ∈ _root_.Set.Icc a b := _root_.Set.Ioo_subset_Icc_self ht
    exact (hgderivIcc t htIcc).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  exact hgAt.congr_of_eventuallyEq hfg_ev

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.hasDerivAt_of_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.hasDerivAt_of_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.hasDerivAt_of_right ``Submission.DifferentialGeometry.hasDerivAt_of_right

theorem exp_neg_intervalIntegral_mul_le_of_deriv_add_mul_nonneg
    {f f' a : Real → Real} {u v : Real} (huv : u < v)
    (hf : ContinuousOn f (_root_.Set.Icc u v))
    (ha : ContinuousOn a (_root_.Set.Icc u v))
    (hderiv : ∀ t ∈ _root_.Set.Ioo u v, HasDerivAt f (f' t) t)
    (hnonneg : ∀ t ∈ _root_.Set.Ioo u v, 0 ≤ f' t + a t * f t) :
    Real.exp (-intervalIntegral a u v _root_.MeasureTheory.MeasureSpace.volume) * f u ≤ f v := by
  let A : Real → Real := fun t => intervalIntegral a u t _root_.MeasureTheory.MeasureSpace.volume
  let q : Real → Real := fun t => Real.exp (A t) * f t
  have haInt : IntervalIntegrable a _root_.MeasureTheory.MeasureSpace.volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc huv.le ha
  have hAcont : ContinuousOn A (_root_.Set.Icc u v) := by
    dsimp only [A]
    rw [← _root_.Set.uIcc_of_le huv.le]
    exact intervalIntegral.continuousOn_primitive_interval
      ((intervalIntegrable_iff').mp haInt)
  have hqcont : ContinuousOn q (_root_.Set.Icc u v) :=
    (Real.continuous_exp.comp_continuousOn hAcont).mul hf
  have hqmono : MonotoneOn q (_root_.Set.Icc u v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc u v) hqcont
    · intro t ht
      have hti : t ∈ _root_.Set.Ioo u v := by
        simpa only [interior_Icc] using ht
      have hat : ContinuousAt a t :=
        (ha t (_root_.Set.Ioo_subset_Icc_self hti)).continuousAt
          (Icc_mem_nhds hti.1 hti.2)
      have haIntT : IntervalIntegrable a _root_.MeasureTheory.MeasureSpace.volume u t :=
        ContinuousOn.intervalIntegrable_of_Icc hti.1.le
          (ha.mono fun _ hs => ⟨hs.1, hs.2.trans hti.2.le⟩)
      have hameas : StronglyMeasurableAtFilter a (𝓝 t) volume :=
        ⟨Icc u v, Icc_mem_nhds hti.1 hti.2,
          ha.aestronglyMeasurable measurableSet_Icc⟩
      have hAd : HasDerivAt A (a t) t := by
        dsimp only [A]
        exact intervalIntegral.integral_hasDerivAt_right haIntT hameas hat
      exact ((Real.hasDerivAt_exp (A t)).comp t hAd).mul (hderiv t hti)
        |>.differentiableAt.differentiableWithinAt
    · intro t ht
      have hti : t ∈ _root_.Set.Ioo u v := by
        simpa only [interior_Icc] using ht
      have hat : ContinuousAt a t :=
        (ha t (_root_.Set.Ioo_subset_Icc_self hti)).continuousAt
          (Icc_mem_nhds hti.1 hti.2)
      have haIntT : IntervalIntegrable a _root_.MeasureTheory.MeasureSpace.volume u t :=
        ContinuousOn.intervalIntegrable_of_Icc hti.1.le
          (ha.mono fun _ hs => ⟨hs.1, hs.2.trans hti.2.le⟩)
      have hameas : StronglyMeasurableAtFilter a (𝓝 t) volume :=
        ⟨Icc u v, Icc_mem_nhds hti.1 hti.2,
          ha.aestronglyMeasurable measurableSet_Icc⟩
      have hAd : HasDerivAt A (a t) t := by
        dsimp only [A]
        exact intervalIntegral.integral_hasDerivAt_right haIntT hameas hat
      have hqd := ((Real.hasDerivAt_exp (A t)).comp t hAd).mul (hderiv t hti)
      change 0 ≤ deriv ((Real.exp ∘ A) * f) t
      rw [hqd.deriv]
      have hexp : 0 ≤ Real.exp (A t) := (Real.exp_pos _).le
      have hfactor :
          Real.exp (A t) * a t * f t + (Real.exp ∘ A) t * f' t =
            Real.exp (A t) * (f' t + a t * f t) := by
        simp only [Function.comp_apply]
        ring
      rw [hfactor]
      exact mul_nonneg hexp (hnonneg t hti)
  have hqend := hqmono (left_mem_Icc.mpr huv.le)
    (right_mem_Icc.mpr huv.le) huv.le
  have hAu : A u = 0 := by simp [A]
  have hAv : A v = intervalIntegral a u v volume := rfl
  dsimp only [q] at hqend
  rw [hAu, Real.exp_zero, one_mul, hAv] at hqend
  calc
    Real.exp (-intervalIntegral a u v _root_.MeasureTheory.MeasureSpace.volume) * f u ≤
        Real.exp (-intervalIntegral a u v _root_.MeasureTheory.MeasureSpace.volume) *
          (Real.exp (intervalIntegral a u v _root_.MeasureTheory.MeasureSpace.volume) * f v) :=
      mul_le_mul_of_nonneg_left hqend (Real.exp_pos _).le
    _ = f v := by rw [← mul_assoc, ← Real.exp_add]; simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.exp_neg_intervalIntegral_mul_le_of_deriv_add_mul_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.exp_neg_intervalIntegral_mul_le_of_deriv_add_mul_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.exp_neg_intervalIntegral_mul_le_of_deriv_add_mul_nonneg ``Submission.DifferentialGeometry.exp_neg_intervalIntegral_mul_le_of_deriv_add_mul_nonneg

theorem contDiffOn_of_right
    {v : F → F} {f : Real → F} {a b : Real} (hab : a < b)
    (hv : ContDiff Real ∞ v) (hf : ContinuousOn f (_root_.Set.Icc a b))
    (hderiv : ∀ t ∈ _root_.Set.Ico a b,
      HasDerivWithinAt f (v (f t)) (_root_.Set.Ici t) t) :
    ContDiffOn Real ∞ f (_root_.Set.Ioo a b) := by
  have hvcomp : ContinuousOn (fun t ↦ v (f t)) (_root_.Set.Icc a b) :=
    hv.continuous.comp_continuousOn hf
  have hfull : ∀ t ∈ _root_.Set.Ioo a b, HasDerivAt f (v (f t)) t :=
    fun t ht ↦ hasDerivAt_of_right hab hf hvcomp hderiv ht
  intro t ht
  let c : Real := (a + t) / 2
  let d : Real := (t + b) / 2
  have hct : c < t := by dsimp only [c]; linarith [ht.1]
  have htd : t < d := by dsimp only [d]; linarith [ht.2]
  have hcd : c < d := hct.trans htd
  have hsub : _root_.Set.Icc c d ⊆ _root_.Set.Ioo a b := by
    intro r hr
    dsimp only [c, d] at hr
    constructor
    · linarith [hr.1, ht.1]
    · linarith [hr.2, ht.2]
  have hfield : ContDiffOn Real ∞
      (Function.uncurry (fun _ : Real ↦ v))
      ((_root_.Set.Icc c d) ×ˢ (Set.univ : Set F)) := by
    have hglobal : ContDiff Real ∞
        (Function.uncurry (fun _ : Real ↦ v)) := by
      change ContDiff Real ∞ (v ∘ Prod.snd)
      exact hv.comp contDiff_snd
    exact hglobal.contDiffOn
  have hlocal : ∀ r ∈ _root_.Set.Icc c d, HasDerivWithinAt f
      ((fun _ : Real ↦ v) r (f r)) (_root_.Set.Icc c d) r := by
    intro r hr
    exact (hfull r (hsub hr)).hasDerivWithinAt
  have hsmooth : ContDiffOn Real ∞ f (_root_.Set.Icc c d) :=
    ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt hfield hlocal
      (fun _ _ ↦ Set.mem_univ _)
  have htcd : t ∈ _root_.Set.Ioo c d := ⟨hct, htd⟩
  exact ((hsmooth t (_root_.Set.Ioo_subset_Icc_self htcd)).contDiffAt
    (Icc_mem_nhds hct htd)).contDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.contDiffOn_of_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.contDiffOn_of_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.contDiffOn_of_right ``Submission.DifferentialGeometry.contDiffOn_of_right

theorem eventually_pos_of_hasDerivAt_pos
    (g : ℝ → ℝ) (ψ : ℝ) (hψ : 0 < ψ) (hg0 : g 0 = 0)
    (hg : HasDerivAt g ψ 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < g t := by
  have hlim' : _root_.Filter.Tendsto (slope g 0) (𝓝[≠] 0) (𝓝 ψ) :=
    hasDerivAt_iff_tendsto_slope.mp hg
  have hmono : _root_.Filter.Tendsto (slope g 0) (𝓝[>] 0) (𝓝 ψ) :=
    hlim'.mono_left (nhdsWithin_mono 0 (by intro x hx; exact ne_of_gt hx))
  have hsimpa : (fun t : ℝ => slope g 0 t) = fun t : ℝ => g t / t := by
    funext t
    dsimp [slope]
    rw [hg0]
    ring_nf
  have hlim : _root_.Filter.Tendsto (fun t : ℝ => g t / t) (𝓝[>] 0) (𝓝 ψ) := by
    simpa [hsimpa] using hmono
  have hψ2 : 0 < ψ / 2 := half_pos hψ
  have hψ2' : ψ / 2 < ψ := by linarith
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, ψ / 2 < g t / t :=
    hlim.eventually (lt_mem_nhds hψ2')
  filter_upwards [hev, self_mem_nhdsWithin] with t ht ht_mem
  have htpos : 0 < t := ht_mem
  have hgt : (ψ / 2) * t < g t := by
    have hmul := mul_lt_mul_of_pos_right ht htpos
    have hcancel : (g t / t) * t = g t := by
      field_simp [htpos.ne']
    nlinarith
  exact lt_of_lt_of_le (mul_pos hψ2 htpos) (le_of_lt hgt)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.eventually_pos_of_hasDerivAt_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.eventually_pos_of_hasDerivAt_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.eventually_pos_of_hasDerivAt_pos ``Submission.DifferentialGeometry.eventually_pos_of_hasDerivAt_pos

theorem eventually_pos_of_continuousAt_pos
    (g : ℝ → ℝ) (hg : ContinuousAt g 0) (hg0 : 0 < g 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < g t := by
  have hlt : g 0 / 2 < g 0 := by linarith
  have hh : ∀ᶠ t : ℝ in 𝓝 0, g 0 / 2 < g t :=
    hg.eventually (Ioi_mem_nhds hlt)
  have hh' : ∀ᶠ t : ℝ in 𝓝[>] 0, g 0 / 2 < g t := hh.filter_mono nhdsWithin_le_nhds
  filter_upwards [hh', self_mem_nhdsWithin] with t ht _htm
  have hgt : 0 < g t := by
    have hhalf : 0 < g 0 / 2 := half_pos hg0
    exact lt_of_lt_of_le hhalf (le_of_lt ht)
  exact hgt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.eventually_pos_of_continuousAt_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.eventually_pos_of_continuousAt_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.eventually_pos_of_continuousAt_pos ``Submission.DifferentialGeometry.eventually_pos_of_continuousAt_pos

theorem eventually_neg_of_continuousAt_neg
    (g : ℝ → ℝ) (hg : ContinuousAt g 0) (hg0 : g 0 < 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, g t < 0 := by
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < -g t :=
    eventually_pos_of_continuousAt_pos (fun t => -g t) hg.neg (by linarith)
  filter_upwards [hev] with t ht
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.eventually_neg_of_continuousAt_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.eventually_neg_of_continuousAt_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.eventually_neg_of_continuousAt_neg ``Submission.DifferentialGeometry.eventually_neg_of_continuousAt_neg

theorem eventually_le_of_continuousAt_lt
    (g : ℝ → ℝ) (hg : ContinuousAt g 0) (c : ℝ) (hgc : g 0 < c) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, g t ≤ c := by
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < c - g t :=
    eventually_pos_of_continuousAt_pos (fun t => c - g t) (continuousAt_const.sub hg) (by linarith)
  filter_upwards [hev] with t ht
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.eventually_le_of_continuousAt_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.eventually_le_of_continuousAt_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.eventually_le_of_continuousAt_lt ``Submission.DifferentialGeometry.eventually_le_of_continuousAt_lt

theorem exists_pos_Ioo_of_eventually_nhdsWithin
    (P : ℝ → Prop) (hev : ∀ᶠ t : ℝ in 𝓝[>] 0, P t) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ t : ℝ, t ∈ Set.Ioo 0 eps → P t := by
  have hev_nhds : ∀ᶠ t : ℝ in 𝓝 0, t ∈ Set.Ioi 0 → P t :=
    eventually_nhdsWithin_iff.mp hev
  rcases Metric.eventually_nhds_iff.mp hev_nhds with ⟨eps, heps, hball⟩
  let eps' : ℝ := eps / 2
  refine ⟨eps', half_pos heps, ?_⟩
  intro t ht
  have htpos : 0 < t := ht.1
  have htle : t ≤ eps / 2 := by
    dsimp [eps'] at ht
    exact le_of_lt ht.2
  have htlt : t < eps := by
    have hhalf : eps / 2 < eps := half_lt_self heps
    nlinarith [htle]
  have hdist : _root_.Dist.dist t 0 < eps := by
    rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
    exact htlt
  exact hball hdist htpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.exists_pos_Ioo_of_eventually_nhdsWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.exists_pos_Ioo_of_eventually_nhdsWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.exists_pos_Ioo_of_eventually_nhdsWithin ``Submission.DifferentialGeometry.exists_pos_Ioo_of_eventually_nhdsWithin
theorem le_of_upper_support
    {f : Real -> Real} {a b c : Real}
    (hf : ContinuousOn f (_root_.Set.Icc a b)) (ha : f a <= c)
    (hsupport : ∀ t ∈ _root_.Set.Ico a b, c < f t ->
      exists phi : Real -> Real, exists d : Real,
        phi t = f t ∧
        f ≤ᶠ[nhdsWithin t (_root_.Set.Ioi t)] phi ∧
        HasDerivAt phi d t ∧ d < 0) :
    ∀ t ∈ _root_.Set.Icc a b, f t <= c := by
  intro t ht
  refine le_of_forall_pos_le_add fun delta hdelta => ?_
  let s : Set Real := {r | f r <= c + delta}
  have hs_closed : IsClosed (s ∩ _root_.Set.Icc a b) := by
    have hconst : ContinuousOn (fun _ : Real => c + delta) (_root_.Set.Icc a b) :=
      continuousOn_const
    change IsClosed {x | f x ≤ c + delta ∧ x ∈ _root_.Set.Icc a b}
    simpa only [and_comm] using isClosed_Icc.isClosed_le hf hconst
  have ha_s : a ∈ s := by
    dsimp only [s]
    exact ha.trans (le_add_of_nonneg_right hdelta.le)
  have hs_all : _root_.Set.Icc a b ⊆ s := by
    apply hs_closed.Icc_subset_of_forall_exists_gt ha_s
    rintro x ⟨hx_s, hx⟩ y hxy
    change f x <= c + delta at hx_s
    rcases hx_s.lt_or_eq with hx_lt | hx_eq
    · have hnear : ∀ᶠ z in nhdsWithin x (_root_.Set.Icc a b), f z < c + delta :=
        hf x (_root_.Set.Ico_subset_Icc_self hx) (Iio_mem_nhds hx_lt)
      have hright : ∀ᶠ z in nhdsWithin x (_root_.Set.Ioi x), f z < c + delta :=
        nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem hx) hnear
      obtain ⟨z, hz_lt, hz_mem⟩ :=
        (hright.and (Ioc_mem_nhdsGT (show x < y from hxy))).exists
      exact ⟨z, ⟨show z ∈ s from hz_lt.le, hz_mem⟩⟩
    · have hcfx : c < f x := by
        rw [hx_eq]
        linarith
      obtain ⟨phi, d, hphi_eq, hupper, hphi_deriv, hd_neg⟩ :=
        hsupport x hx hcfx
      have hslope : ∀ᶠ z in nhdsWithin x (_root_.Set.Ioi x), slope phi x z < 0 :=
        (hphi_deriv.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)).eventually_lt_const hd_neg
      have hphi_lt : ∀ᶠ z in nhdsWithin x (_root_.Set.Ioi x), phi z < phi x := by
        filter_upwards [hslope, self_mem_nhdsWithin] with z hz_slope hxz
        rw [slope_def_field] at hz_slope
        have hdiff : phi z - phi x < 0 := by
          simpa only [_root_.MulZeroClass.zero_mul] using
            (div_lt_iff₀ (sub_pos.mpr hxz)).mp hz_slope
        exact sub_lt_zero.mp hdiff
      have hright : ∀ᶠ z in nhdsWithin x (_root_.Set.Ioi x), f z < c + delta := by
        filter_upwards [hupper, hphi_lt] with z hle hlt
        calc
          f z <= phi z := hle
          _ < phi x := hlt
          _ = c + delta := hphi_eq.trans hx_eq
      obtain ⟨z, hz_lt, hz_mem⟩ :=
        (hright.and (Ioc_mem_nhdsGT (show x < y from hxy))).exists
      exact ⟨z, ⟨show z ∈ s from hz_lt.le, hz_mem⟩⟩
  exact hs_all ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.le_of_upper_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.le_of_upper_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.le_of_upper_support ``Submission.DifferentialGeometry.le_of_upper_support

end DifferentialGeometry
