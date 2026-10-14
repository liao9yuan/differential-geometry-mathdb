import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.L2Space

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.instMeasurableSpaceEuclideanSpaceRealFin_differentialGeometry : MeasurableSpace E := WithLp.measurableSpace 2 (Fin d → ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.instMeasurableSpaceEuclideanSpaceRealFin_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.instMeasurableSpaceEuclideanSpaceRealFin_differentialGeometry target :: scope.openDecls } }

private theorem integral_translate_congr_ae
    {w f : E → ℝ} (h : w =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] f) (v : E) (a b : ℝ) :
    (fun x => ∫ r in a..b, w (x + r • v)) =ᵐ[_root_.MeasureTheory.MeasureSpace.volume]
      fun x => ∫ r in a..b, f (x + r • v) := by
  have hq : Measure.QuasiMeasurePreserving (fun p : E × ℝ => p.1 + p.2 • v)
      (volume.prod (volume.restrict (_root_.Set.uIoc a b))) volume := by
    apply MeasureTheory.QuasiMeasurePreserving.prod_of_left (measurable_fst.add (measurable_snd.smul_const v))
    exact Eventually.of_forall fun r =>
      (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume (r • v)).quasiMeasurePreserving
  filter_upwards [Measure.ae_ae_of_ae_prod (hq.ae_eq h)] with x hx
  exact intervalIntegral.integral_congr_ae_restrict hx

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_translate_congr_ae
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.integral_translate_congr_ae target :: scope.openDecls } }

private theorem integral_norm_mul_norm_le_lp_norm
    {P : Type*} [MeasurableSpace P] {μ : _root_.MeasureTheory.Measure P}
    (u : _root_.MeasureTheory.Lp ℝ 2 μ) (v : _root_.MeasureTheory.Lp ℝ 2 μ) :
    (∫ t, ‖u t‖ * ‖v t‖ ∂μ) ≤ ‖u‖ * ‖v‖ := by
  let uN : _root_.MeasureTheory.Lp ℝ 2 μ := (Lp.memLp u).norm.toLp (fun t => ‖u t‖)
  let vN : _root_.MeasureTheory.Lp ℝ 2 μ := (Lp.memLp v).norm.toLp (fun t => ‖v t‖)
  have hpair : (∫ t, ‖u t‖ * ‖v t‖ ∂μ) = _root_.Inner.inner ℝ uN vN := by
    rw [L2.inner_def]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [(Lp.memLp u).norm.coeFn_toLp, (Lp.memLp v).norm.coeFn_toLp]
      with t hu hv
    simp only [Real.inner_apply]
    change ‖u t‖ * ‖v t‖ = uN t * vN t
    rw [show uN t = ‖u t‖ from hu, show vN t = ‖v t‖ from hv]
  have hun : ‖uN‖ = ‖u‖ := by rw [Lp.norm_toLp, _root_.MeasureTheory.eLpNorm_norm, Lp.norm_def]
  have hvn : ‖vN‖ = ‖v‖ := by rw [Lp.norm_toLp, _root_.MeasureTheory.eLpNorm_norm, Lp.norm_def]
  rw [hpair, ← hun, ← hvn]
  exact real_inner_le_norm _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_norm_mul_norm_le_lp_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.integral_norm_mul_norm_le_lp_norm target :: scope.openDecls } }

private theorem integral_norm_mul_norm_le
    {f g : E → ℝ} (hf : _root_.MeasureTheory.MemLp f 2 _root_.MeasureTheory.MeasureSpace.volume) (hg : _root_.MeasureTheory.MemLp g 2 _root_.MeasureTheory.MeasureSpace.volume) :
    (∫ x, ‖f x‖ * ‖g x‖) ≤ (_root_.MeasureTheory.eLpNorm f 2 _root_.MeasureTheory.MeasureSpace.volume).toReal * (_root_.MeasureTheory.eLpNorm g 2 _root_.MeasureTheory.MeasureSpace.volume).toReal := by
  have heq : (∫ x, ‖f x‖ * ‖g x‖) = ∫ x, ‖hf.toLp f x‖ * ‖hg.toLp g x‖ := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    rw [hx, hy]
  rw [heq]
  simpa only [Lp.norm_toLp] using integral_norm_mul_norm_le_lp_norm (hf.toLp f) (hg.toLp g)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_norm_mul_norm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.integral_norm_mul_norm_le target :: scope.openDecls } }

private theorem integrable_translate_mul_prod
    {w φ : E → ℝ} (hw : _root_.MeasureTheory.StronglyMeasurable w) (hφ : _root_.MeasureTheory.StronglyMeasurable φ)
    (hwL : _root_.MeasureTheory.MemLp w 2 _root_.MeasureTheory.MeasureSpace.volume) (hφL : _root_.MeasureTheory.MemLp φ 2 _root_.MeasureTheory.MeasureSpace.volume) (v : E) (a b : ℝ) :
    _root_.MeasureTheory.Integrable (fun p : ℝ × E => w (p.2 + p.1 • v) * φ p.2)
      ((volume.restrict (_root_.Set.uIoc a b)).prod _root_.MeasureTheory.MeasureSpace.volume) := by
  let _ : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (_root_.Set.uIoc a b)) :=
    ⟨by simp [Real.volume_uIoc]⟩
  have hm : _root_.MeasureTheory.StronglyMeasurable (fun p : ℝ × E => w (p.2 + p.1 • v) * φ p.2) :=
    (hw.comp_measurable (measurable_snd.add (measurable_fst.smul_const v))).mul
      (hφ.comp_measurable measurable_snd)
  apply (_root_.MeasureTheory.integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun r =>
      (hwL.comp_measurePreserving (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume (r • v))).integrable_mul hφL
  · apply Integrable.mono' (_root_.MeasureTheory.integrable_const
      ((_root_.MeasureTheory.eLpNorm w 2 _root_.MeasureTheory.MeasureSpace.volume).toReal * (_root_.MeasureTheory.eLpNorm φ 2 _root_.MeasureTheory.MeasureSpace.volume).toReal))
      hm.norm.aestronglyMeasurable.integral_prod_right'
    refine Eventually.of_forall fun r => ?_
    rw [Real.norm_of_nonneg (_root_.MeasureTheory.integral_nonneg fun x => norm_nonneg _)]
    simp only [norm_mul]
    have hb := integral_norm_mul_norm_le
      (hwL.comp_measurePreserving (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume (r • v))) hφL
    have he := _root_.MeasureTheory.eLpNorm_comp_measurePreserving (p := 2) hwL.aestronglyMeasurable
      (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume (r • v))
    rw [he] at hb
    exact hb

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.integrable_translate_mul_prod
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.integrable_translate_mul_prod target :: scope.openDecls } }

private theorem integral_translate_mul_eq_mul_translate
    (w φ : E → ℝ) (v : E) :
    (∫ x, w (x + v) * φ x) = ∫ x, w x * φ (x - v) := by
  have heq : (fun x => w (x + v) * φ x) = fun x =>
      (fun y => w y * φ (y - v)) (x + v) := by
    funext x
    simp only [add_sub_cancel_right]
  rw [heq]
  exact _root_.MeasureTheory.integral_add_right_eq_self (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) (fun y => w y * φ (y - v)) v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_translate_mul_eq_mul_translate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.integral_translate_mul_eq_mul_translate target :: scope.openDecls } }

private theorem integral_fderiv_shift_eq_sub
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (v : E) (h : ℝ) (x : E) :
    (∫ r in (0 : ℝ)..h, fderiv ℝ φ (x - r • v) v) = φ x - φ (x - h • v) := by
  have hd (r : ℝ) : HasDerivAt (fun r => φ (x - r • v))
      (-fderiv ℝ φ (x - r • v) v) r := by
    have hline : HasDerivAt (fun r : ℝ => x - r • v) (-v) r := by
      have hsmul : HasDerivAt (fun r : ℝ => r • v) v r := by
        simpa using (hasDerivAt_id r).smul_const v
      exact hsmul.const_sub x
    have hdφ : HasFDerivAt φ (fderiv ℝ φ (x - r • v)) (x - r • v) :=
      (hφ.differentiable (by simp) _).hasFDerivAt
    rw [← map_neg]
    exact hdφ.comp_hasDerivAt r hline
  have hi : IntervalIntegrable (fun r : ℝ => fderiv ℝ φ (x - r • v) v) _root_.MeasureTheory.MeasureSpace.volume 0 h :=
    (((hφ.continuous_fderiv (by simp)).comp
      (continuous_const.sub (continuous_id.smul continuous_const))).clm_apply continuous_const).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hi.neg
  rw [intervalIntegral.integral_neg] at he
  simpa only [zero_smul, sub_zero] using (neg_eq_iff_eq_neg.mp he).trans (neg_sub _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_fderiv_shift_eq_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.integral_fderiv_shift_eq_sub target :: scope.openDecls } }

private theorem hasWeakPartialDeriv_steklovAverage_of_stronglyMeasurable
    {w : E → ℝ} (hw : _root_.MeasureTheory.StronglyMeasurable w) (hwL : _root_.MeasureTheory.MemLp w 2 _root_.MeasureTheory.MeasureSpace.volume)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    DeGiorgi.HasWeakPartialDeriv k (diffQuot k h w)
      (fun x => h⁻¹ * ∫ r in (0 : ℝ)..h, w (x + r • EuclideanSpace.single k 1)) univ := by
  intro φ hφ hφc _
  let v : E := EuclideanSpace.single k 1
  let Dφ : E → ℝ := fun x => fderiv ℝ φ x v
  have hDφ : Continuous Dφ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDφc : HasCompactSupport Dφ := hφc.fderiv_apply (𝕜 := ℝ) v
  have hDφL : _root_.MeasureTheory.MemLp Dφ 2 volume := hDφ.memLp_of_hasCompactSupport hDφc
  have hleft := integrable_translate_mul_prod hw hDφ.stronglyMeasurable hwL hDφL v 0 h
  have hright : _root_.MeasureTheory.Integrable (fun p : ℝ × E => w p.2 * Dφ (p.2 - p.1 • v))
      ((volume.restrict (_root_.Set.uIoc (0 : ℝ) h)).prod _root_.MeasureTheory.MeasureSpace.volume) := by
    have hi := integrable_translate_mul_prod hDφ.stronglyMeasurable hw hDφL hwL (-v) 0 h
    simpa only [smul_neg, ← sub_eq_add_neg, mul_comm] using hi
  have hpair : (∫ x, (h⁻¹ * ∫ r in (0 : ℝ)..h, w (x + r • v)) * Dφ x) =
      ∫ x, w x * diffQuot k (-h) φ x := by
    calc
      _ = h⁻¹ * ∫ x, ∫ r in (0 : ℝ)..h, w (x + r • v) * Dφ x := by
        simp_rw [intervalIntegral.integral_mul_const]
        rw [← _root_.MeasureTheory.integral_const_mul]
        apply _root_.MeasureTheory.integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = h⁻¹ * ∫ r in (0 : ℝ)..h, ∫ x, w (x + r • v) * Dφ x :=
        congrArg (fun y : ℝ => h⁻¹*y) (_root_.MeasureTheory.intervalIntegral_integral_swap hleft).symm
      _ = h⁻¹ * ∫ r in (0 : ℝ)..h, ∫ x, w x * Dφ (x - r • v) := by
        congr 1
        apply intervalIntegral.integral_congr
        intro r _
        exact integral_translate_mul_eq_mul_translate w Dφ (r • v)
      _ = h⁻¹ * ∫ x, ∫ r in (0 : ℝ)..h, w x * Dφ (x - r • v) :=
        congrArg (fun y : ℝ => h⁻¹*y) (_root_.MeasureTheory.intervalIntegral_integral_swap hright)
      _ = h⁻¹ * ∫ x, w x * (φ x - φ (x - h • v)) := by
        congr 1
        apply _root_.MeasureTheory.integral_congr_ae
        refine Eventually.of_forall fun x => ?_
        dsimp only
        rw [intervalIntegral.integral_const_mul]
        exact congrArg (fun y => w x * y) (integral_fderiv_shift_eq_sub hφ v h x)
      _ = _ := by
        rw [← _root_.MeasureTheory.integral_const_mul]
        apply _root_.MeasureTheory.integral_congr_ae
        refine Eventually.of_forall fun x => ?_
        dsimp only
        rw [diffQuot_apply_of_ne k (neg_ne_zero.mpr hh)]
        dsimp only [v]
        rw [neg_smul, ← sub_eq_add_neg]
        field_simp
        ring
  have hIBP := integral_diffQuot_mul_eq_neg_integral_mul_diffQuot k hh hwL
    (hφ.continuous.memLp_of_hasCompactSupport hφc : _root_.MeasureTheory.MemLp φ 2 _root_.MeasureTheory.MeasureSpace.volume)
  simp only [Measure.restrict_univ]
  change (∫ x, (h⁻¹ * ∫ r in (0 : ℝ)..h, w (x + r • v)) * Dφ x) = _
  rw [hpair, hIBP, neg_neg]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_steklovAverage_of_stronglyMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_steklovAverage_of_stronglyMeasurable target :: scope.openDecls } }

theorem hasWeakPartialDeriv_integral_translate
    {w : E → ℝ} (hw : _root_.MeasureTheory.MemLp w 2 _root_.MeasureTheory.MeasureSpace.volume) (k : Fin d) (h : ℝ) :
    DeGiorgi.HasWeakPartialDeriv k (diffQuot k h w)
      (fun x => h⁻¹ * ∫ r in (0 : ℝ)..h, w (x + r • EuclideanSpace.single k 1)) univ := by
  by_cases hh : h = 0
  · intro φ _ _ _
    simp only [hh, inv_zero, _root_.MulZeroClass.zero_mul, diffQuot_zero_h, Pi.zero_apply, _root_.MeasureTheory.integral_zero, neg_zero]
  let f : _root_.MeasureTheory.Lp ℝ 2 volume := hw.toLp w
  have hf := hasWeakPartialDeriv_steklovAverage_of_stronglyMeasurable
    (Lp.stronglyMeasurable f) (Lp.memLp f) k hh
  have heq : (f : E → ℝ) =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] w := hw.coeFn_toLp
  have hav := integral_translate_congr_ae heq (EuclideanSpace.single k 1) 0 h
  have hdq : diffQuot k h f =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] diffQuot k h w := by
    have ht := (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume (h • EuclideanSpace.single k 1)).quasiMeasurePreserving.ae_eq heq
    filter_upwards [heq, ht] with x hx htx
    dsimp only [Function.comp_def] at htx
    simp only [diffQuot_apply_of_ne k hh, htx, hx]
  intro φ hφ hφc hφs
  have hi := hf φ hφ hφc hφs
  simp only [Measure.restrict_univ] at hi ⊢
  have heleft : (∫ x, (h⁻¹ * ∫ r in (0 : ℝ)..h, f (x + r • EuclideanSpace.single k 1)) *
      fderiv ℝ φ x (EuclideanSpace.single k 1)) =
      ∫ x, (h⁻¹ * ∫ r in (0 : ℝ)..h, w (x + r • EuclideanSpace.single k 1)) *
        fderiv ℝ φ x (EuclideanSpace.single k 1) := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hav] with x hx
    rw [hx]
  have heright : (∫ x, diffQuot k h f x * φ x) = ∫ x, diffQuot k h w x * φ x := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hdq] with x hx
    rw [hx]
  exact heleft.symm.trans (hi.trans (congrArg Neg.neg heright))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_integral_translate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_integral_translate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_integral_translate ``Submission.DifferentialGeometry.Analysis.Sobolev.hasWeakPartialDeriv_integral_translate

end DifferentialGeometry.Analysis.Sobolev
