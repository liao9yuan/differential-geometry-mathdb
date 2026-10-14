import Submission.DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def steklovAverage (h : ℝ) (f : ℝ → X) (t : ℝ) : X :=
  h⁻¹ • ∫ s in t..t + h, f s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage

theorem steklovAverage_congr_ae
    {f g : ℝ → X} (hfg : f =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] g) (h t : ℝ) :
    steklovAverage h f t = steklovAverage h g t := by
  unfold steklovAverage
  congr 1
  exact intervalIntegral.integral_congr_ae (hfg.mono fun _ hx _ => hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage_congr_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage_congr_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage_congr_ae ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage_congr_ae

theorem steklovAverage_comp_continuousLinearMap {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace X] [CompleteSpace Y]
    (L : X →L[ℝ] Y) {f : ℝ → X} {h t : ℝ}
    (hf : IntervalIntegrable f _root_.MeasureTheory.MeasureSpace.volume t (t + h)) :
    steklovAverage h (fun s => L (f s)) t = L (steklovAverage h f t) := by
  simp only [steklovAverage, map_smul, L.intervalIntegral_comp_comm hf]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage_comp_continuousLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage_comp_continuousLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage_comp_continuousLinearMap ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage_comp_continuousLinearMap

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace MeasureTheory.Lp
open _root_.MeasureTheory _root_.MeasureTheory.Lp

variable {X : Type*} [NormedAddCommGroup X]

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
def translate (r : ℝ) (u : _root_.MeasureTheory.Lp X 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)) : _root_.MeasureTheory.Lp X 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ) :=
  _root_.MeasureTheory.Lp.compMeasurePreserving (fun t => t + r) (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume r) u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.translate then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.translate"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.translate ``Submission.MeasureTheory.Lp.translate

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem coeFn_translate (r : ℝ) (u : _root_.MeasureTheory.Lp X 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)) :
    translate r u =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] (fun t => u (t + r)) :=
  _root_.MeasureTheory.Lp.coeFn_compMeasurePreserving u (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume r)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.coeFn_translate then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.coeFn_translate"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.coeFn_translate ``Submission.MeasureTheory.Lp.coeFn_translate

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
@[simp] theorem norm_translate (r : ℝ) (u : _root_.MeasureTheory.Lp X 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)) :
    ‖translate r u‖ = ‖u‖ := _root_.MeasureTheory.Lp.norm_compMeasurePreserving u _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.norm_translate then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.norm_translate"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.norm_translate ``Submission.MeasureTheory.Lp.norm_translate

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
@[simp] theorem translate_zero (u : _root_.MeasureTheory.Lp X 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)) : translate 0 u = u := by
  simp only [translate, add_zero]
  exact _root_.MeasureTheory.Lp.compMeasurePreserving_id_apply u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.translate_zero then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.translate_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.translate_zero ``Submission.MeasureTheory.Lp.translate_zero

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem continuous_translate (u : _root_.MeasureTheory.Lp X 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)) : Continuous (fun r : ℝ => translate r u) := by
  let g : C(ℝ, C(ℝ, ℝ)) := (ContinuousMap.mk (fun p : ℝ × ℝ => p.2 + p.1)
    (continuous_snd.add continuous_fst)).curry
  exact continuous_const.compMeasurePreservingLp g.continuous
    (fun r => _root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume r) (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.continuous_translate then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.continuous_translate"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.continuous_translate ``Submission.MeasureTheory.Lp.continuous_translate

variable [NormedSpace ℝ X]

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
def steklovAverage (h : ℝ) (u : _root_.MeasureTheory.Lp X 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)) : _root_.MeasureTheory.Lp X 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ) :=
  h⁻¹ • ∫ r in (0 : ℝ)..h, translate r u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.steklovAverage then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.steklovAverage"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.steklovAverage ``Submission.MeasureTheory.Lp.steklovAverage

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem norm_steklovAverage_le (h : ℝ) (u : _root_.MeasureTheory.Lp X 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)) :
    ‖steklovAverage h u‖ ≤ ‖u‖ := by
  by_cases hh : h = 0
  · simp [steklovAverage, hh]
  have hhabs : |h| ≠ 0 := abs_ne_zero.mpr hh
  calc
    ‖steklovAverage h u‖ = |h|⁻¹ * ‖∫ r in (0 : ℝ)..h, translate r u‖ := by
      rw [steklovAverage, norm_smul, Real.norm_eq_abs, abs_inv]
    _ ≤ |h|⁻¹ * (‖u‖ * |h|) := by
      gcongr
      simpa only [sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := h)
        (fun r _ => (norm_translate r u).le)
    _ = ‖u‖ := by field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.norm_steklovAverage_le then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.norm_steklovAverage_le"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.norm_steklovAverage_le ``Submission.MeasureTheory.Lp.norm_steklovAverage_le

variable [CompleteSpace X]

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem tendsto_steklovAverage (u : _root_.MeasureTheory.Lp X 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)) :
    Tendsto (fun h => steklovAverage h u) (𝓝[≠] 0) (𝓝 u) := by
  have hc := continuous_translate u
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 0) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simpa only [translate_zero, steklovAverage, zero_add, intervalIntegral.integral_same,
    sub_zero] using hd.tendsto_slope_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.tendsto_steklovAverage then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.tendsto_steklovAverage"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.tendsto_steklovAverage ``Submission.MeasureTheory.Lp.tendsto_steklovAverage

end MeasureTheory.Lp

namespace MeasureTheory.Lp
open _root_.MeasureTheory _root_.MeasureTheory.Lp

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private def setIntegralContinuousLinearMap (S : Set ℝ) (hS : MeasurableSet S)
    (hvol : _root_.MeasureTheory.MeasureSpace.volume S ≠ ∞) : _root_.MeasureTheory.Lp X 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ) →L[ℝ] X :=
  (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing _root_.MeasureTheory.MeasureSpace.volume 2 2 (_root_.MeasureTheory.indicatorConstLp 2 hS hvol (1 : ℝ))

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.setIntegralContinuousLinearMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.setIntegralContinuousLinearMap target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private theorem setIntegralContinuousLinearMap_apply (S : Set ℝ) (hS : MeasurableSet S)
    (hvol : _root_.MeasureTheory.MeasureSpace.volume S ≠ ∞) (u : _root_.MeasureTheory.Lp X 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)) :
    setIntegralContinuousLinearMap S hS hvol u = ∫ t in S, u t := by
  rw [setIntegralContinuousLinearMap, ContinuousLinearMap.lpPairing_eq_integral]
  rw [← _root_.MeasureTheory.integral_indicator hS]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [_root_.MeasureTheory.indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := hvol) (c := (1 : ℝ))] with t ht
  rw [ContinuousLinearMap.lsmul_apply, ht]
  by_cases htS : t ∈ S
  · simp only [_root_.Set.indicator_of_mem htS, one_smul]
  · simp only [_root_.Set.indicator_of_notMem htS, zero_smul]

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.setIntegralContinuousLinearMap_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.setIntegralContinuousLinearMap_apply target :: scope.openDecls } }

omit [NormedSpace ℝ X] [CompleteSpace X] in
open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private theorem setIntegral_norm_le_mul_norm (S : Set ℝ) (hS : MeasurableSet S)
    (hvol : _root_.MeasureTheory.MeasureSpace.volume S ≠ ∞) (u : _root_.MeasureTheory.Lp X 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)) :
    (∫ t in S, ‖u t‖) ≤ ‖setIntegralContinuousLinearMap (X := ℝ) S hS hvol‖ * ‖u‖ := by
  let v : _root_.MeasureTheory.Lp ℝ 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ) := (Lp.memLp u).norm.toLp (fun t => ‖u t‖)
  have hnorm : ‖v‖ = ‖u‖ := by
    rw [show v = (Lp.memLp u).norm.toLp (fun t => ‖u t‖) from rfl, Lp.norm_toLp, _root_.MeasureTheory.eLpNorm_norm]
    rfl
  have heq : (∫ t in S, ‖u t‖) = setIntegralContinuousLinearMap S hS hvol v := by
    rw [setIntegralContinuousLinearMap_apply]
    exact _root_.MeasureTheory.integral_congr_ae (_root_.MeasureTheory.ae_restrict_of_ae (MemLp.coeFn_toLp (Lp.memLp u).norm).symm)
  rw [heq]
  calc
    _ ≤ ‖setIntegralContinuousLinearMap S hS hvol v‖ := le_abs_self _
    _ ≤ ‖setIntegralContinuousLinearMap S hS hvol‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [hnorm]

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.setIntegral_norm_le_mul_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.setIntegral_norm_le_mul_norm target :: scope.openDecls } }

omit [NormedSpace ℝ X] [CompleteSpace X] in
open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private theorem integrable_translate_prod (u : _root_.MeasureTheory.Lp X 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ))
    (a b : ℝ) {S : Set ℝ} (hS : MeasurableSet S) (hvol : _root_.MeasureTheory.MeasureSpace.volume S < ∞) :
    _root_.MeasureTheory.Integrable (fun q : ℝ × ℝ => u (q.2 + q.1))
      ((volume.restrict (_root_.Set.Ioc a b)).prod (volume.restrict S)) := by
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hvol⟩
  have hmeas : _root_.MeasureTheory.StronglyMeasurable (fun q : ℝ × ℝ => u (q.2 + q.1)) :=
    (Lp.stronglyMeasurable u).comp_measurable (measurable_snd.add measurable_fst)
  apply (_root_.MeasureTheory.integrable_prod_iff hmeas.aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun r =>
      (((Lp.memLp u).comp_measurePreserving (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume r)).restrict S).integrable (by norm_num)
  · apply Integrable.mono' (_root_.MeasureTheory.integrable_const (‖setIntegralContinuousLinearMap (X := ℝ) S hS hvol.ne‖ * ‖u‖))
      hmeas.norm.aestronglyMeasurable.integral_prod_right'
    refine Eventually.of_forall fun r => ?_
    rw [Real.norm_of_nonneg (_root_.MeasureTheory.integral_nonneg fun t => norm_nonneg (u (t + r)))]
    have heq : (∫ t in S, ‖u (t + r)‖) = ∫ t in S, ‖translate r u t‖ :=
      _root_.MeasureTheory.integral_congr_ae (_root_.MeasureTheory.ae_restrict_of_ae ((coeFn_translate r u).fun_comp _root_.Norm.norm).symm)
    rw [heq]
    exact (setIntegral_norm_le_mul_norm S hS hvol.ne (translate r u)).trans_eq
      (by rw [norm_translate])

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.integrable_translate_prod
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.integrable_translate_prod target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private theorem coeFn_setIntegral_translate (u : _root_.MeasureTheory.Lp X 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ))
    (a b : ℝ) :
    ((∫ r in _root_.Set.Ioc a b, translate r u : _root_.MeasureTheory.Lp X 2 _root_.MeasureTheory.MeasureSpace.volume) : ℝ → X) =ᵐ[_root_.MeasureTheory.MeasureSpace.volume]
      fun t => ∫ r in _root_.Set.Ioc a b, u (t + r) := by
  apply _root_.MeasureTheory.ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro S hS hvol
    let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hvol⟩
    exact ((Lp.memLp _).restrict S).integrable (by norm_num)
  · intro S hS hvol
    exact (integrable_translate_prod u a b hS hvol).integral_prod_right
  · intro S hS hvol
    have htranslate : _root_.MeasureTheory.IntegrableOn (fun r => translate r u) (_root_.Set.Ioc a b) :=
      (continuous_translate u).integrableOn_Icc.mono_set _root_.Set.Ioc_subset_Icc_self
    rw [← setIntegralContinuousLinearMap_apply S hS hvol.ne]
    rw [← ContinuousLinearMap.integral_comp_comm _ htranslate]
    calc
      _ = ∫ r in _root_.Set.Ioc a b, ∫ t in S, u (t + r) := by
        apply _root_.MeasureTheory.integral_congr_ae
        refine Eventually.of_forall fun r => ?_
        dsimp only
        rw [setIntegralContinuousLinearMap_apply]
        exact _root_.MeasureTheory.integral_congr_ae (_root_.MeasureTheory.ae_restrict_of_ae (coeFn_translate r u))
      _ = _ := _root_.MeasureTheory.integral_integral_swap (integrable_translate_prod u a b hS hvol)

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.coeFn_setIntegral_translate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.coeFn_setIntegral_translate target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private theorem coeFn_intervalIntegral_translate (u : _root_.MeasureTheory.Lp X 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ))
    (a b : ℝ) :
    ((∫ r in a..b, translate r u : _root_.MeasureTheory.Lp X 2 _root_.MeasureTheory.MeasureSpace.volume) : ℝ → X) =ᵐ[_root_.MeasureTheory.MeasureSpace.volume]
      fun t => ∫ r in a..b, u (t + r) := by
  simp only [intervalIntegral]
  exact (_root_.MeasureTheory.Lp.coeFn_sub _ _).trans
    ((coeFn_setIntegral_translate u a b).sub (coeFn_setIntegral_translate u b a))

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.coeFn_intervalIntegral_translate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.coeFn_intervalIntegral_translate target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem coeFn_steklovAverage (h : ℝ) (u : _root_.MeasureTheory.Lp X 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)) :
    steklovAverage h u =ᵐ[_root_.MeasureTheory.MeasureSpace.volume]
      fun t => DifferentialGeometry.Analysis.Parabolic.TimeSobolev.steklovAverage h u t := by
  rw [steklovAverage]
  filter_upwards [_root_.MeasureTheory.Lp.coeFn_smul (h⁻¹) (∫ r in (0 : ℝ)..h, translate r u),
    coeFn_intervalIntegral_translate u 0 h] with t hsmul hint
  rw [hsmul, Pi.smul_apply, hint]
  congr 1
  simpa only [add_zero] using intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := h) (⇑u) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.coeFn_steklovAverage then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.coeFn_steklovAverage"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.coeFn_steklovAverage ``Submission.MeasureTheory.Lp.coeFn_steklovAverage

end MeasureTheory.Lp

open scoped _root_.NNReal

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem integral_mul_bilinear_sub_translate
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B)
    {f : ℝ → X} (hf : _root_.MeasureTheory.MemLp f 2 _root_.MeasureTheory.MeasureSpace.volume)
    {ζ : ℝ → ℝ} (hζ : _root_.MeasureTheory.MemLp ζ ∞ _root_.MeasureTheory.MeasureSpace.volume) (s : ℝ) :
    2 * (∫ t, ζ t * B (f t) (f (t + s) - f t)) =
      (∫ t, (ζ (t - s) - ζ t) * B (f t) (f t)) -
        ∫ t, ζ t * B (f (t + s) - f t) (f (t + s) - f t) := by
  have hfshift : _root_.MeasureTheory.MemLp (fun t => f (t + s)) 2 volume :=
    hf.comp_measurePreserving (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume s)
  have hζshift : _root_.MeasureTheory.MemLp (fun t => ζ (t - s)) ∞ volume := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      hζ.comp_measurePreserving (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume (-s))
  have hint {u v : ℝ → X} (hu : _root_.MeasureTheory.MemLp u 2 _root_.MeasureTheory.MeasureSpace.volume) (hv : _root_.MeasureTheory.MemLp v 2 _root_.MeasureTheory.MeasureSpace.volume) :
      Integrable (fun t => B (u t) (v t)) volume :=
    MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable (fun _ : ℝ => B)
      (fun _ _ => _root_.MeasureTheory.aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl) hu hv
  have hζsq : _root_.MeasureTheory.Integrable (fun t => ζ t * B (f t) (f t)) volume :=
    (hint hf hf).mul_of_top_right hζ
  have hζsqs : _root_.MeasureTheory.Integrable (fun t => ζ t * B (f (t + s)) (f (t + s))) volume :=
    (hint hfshift hfshift).mul_of_top_right hζ
  have hζsqd : _root_.MeasureTheory.Integrable (fun t => ζ t * B (f (t + s) - f t) (f (t + s) - f t)) volume :=
    (hint (hfshift.sub hf) (hfshift.sub hf)).mul_of_top_right hζ
  have hζshsq : _root_.MeasureTheory.Integrable (fun t => ζ (t - s) * B (f t) (f t)) volume :=
    (hint hf hf).mul_of_top_right hζshift
  have hζsub : _root_.MeasureTheory.Integrable (fun t => ζ t * B (f (t + s)) (f (t + s)) - ζ t * B (f t) (f t))
      volume := hζsqs.sub hζsq
  have hsymm (x y : X) : B y x = B x y := by
    exact congrArg (fun L : X →L[ℝ] X →L[ℝ] ℝ => L x y) hB
  have hnorm : ∀ t, 2 * (ζ t * B (f t) (f (t + s) - f t)) =
      ζ t * B (f (t + s)) (f (t + s)) - ζ t * B (f t) (f t) -
        ζ t * B (f (t + s) - f t) (f (t + s) - f t) := by
    intro t
    simp only [map_sub, sub_apply]
    rw [hsymm (f t) (f (t + s))]
    ring
  have htranslate : (∫ t, ζ t * B (f (t + s)) (f (t + s))) =
      ∫ t, ζ (t - s) * B (f t) (f t) := by
    conv_lhs =>
      rw [← _root_.MeasureTheory.integral_add_right_eq_self (fun t => ζ t * B (f (t + s)) (f (t + s))) (-s)]
    simp only [neg_add_cancel_right, sub_eq_add_neg]
  rw [← _root_.MeasureTheory.integral_const_mul]
  calc
    _ = ∫ t, ζ t * B (f (t + s)) (f (t + s)) - ζ t * B (f t) (f t) -
        ζ t * B (f (t + s) - f t) (f (t + s) - f t) :=
      _root_.MeasureTheory.integral_congr_ae (Eventually.of_forall hnorm)
    _ = (∫ t, ζ t * B (f (t + s)) (f (t + s))) - (∫ t, ζ t * B (f t) (f t)) -
        ∫ t, ζ t * B (f (t + s) - f t) (f (t + s) - f t) := by
      rw [_root_.MeasureTheory.integral_sub hζsub hζsqd, _root_.MeasureTheory.integral_sub hζsqs hζsq]
    _ = _ := by
      rw [htranslate, ← _root_.MeasureTheory.integral_sub hζshsq hζsq]
      congr 1
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [] with t
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_mul_bilinear_sub_translate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_mul_bilinear_sub_translate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_mul_bilinear_sub_translate ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_mul_bilinear_sub_translate

theorem integral_mul_bilinear_sub_translate_le
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B) (hBpos : ∀ x, 0 ≤ B x x)
    {f : ℝ → X} (hf : _root_.MeasureTheory.MemLp f 2 _root_.MeasureTheory.MeasureSpace.volume)
    {ζ : ℝ → ℝ} (hζ : _root_.MeasureTheory.MemLp ζ ∞ _root_.MeasureTheory.MeasureSpace.volume) (hζpos : ∀ᵐ t, 0 ≤ ζ t) (s : ℝ) :
    (∫ t, ζ t * B (f t) (f (t + s) - f t)) ≤
      (1 / 2) * ∫ t, (ζ (t - s) - ζ t) * B (f t) (f t) := by
  have hid := integral_mul_bilinear_sub_translate B hB hf hζ s
  have hn : 0 ≤ ∫ t, ζ t * B (f (t + s) - f t) (f (t + s) - f t) := by
    apply _root_.MeasureTheory.integral_nonneg_of_ae
    filter_upwards [hζpos] with t ht
    exact mul_nonneg ht (hBpos _)
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_mul_bilinear_sub_translate_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_mul_bilinear_sub_translate_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_mul_bilinear_sub_translate_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_mul_bilinear_sub_translate_le

theorem integral_mul_bilinear_diffQuot_le
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B) (hBpos : ∀ x, 0 ≤ B x x)
    {f : ℝ → X} (hf : _root_.MeasureTheory.MemLp f 2 _root_.MeasureTheory.MeasureSpace.volume)
    {ζ : ℝ → ℝ} (hζ : _root_.MeasureTheory.MemLp ζ ∞ _root_.MeasureTheory.MeasureSpace.volume) (hζpos : ∀ᵐ t, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ) {s : ℝ} (hs : 0 < s) :
    (∫ t, ζ t * B (f t) (s⁻¹ • (f (t + s) - f t))) ≤
      ((K : ℝ) / 2) * ∫ t, B (f t) (f t) := by
  have hbase := integral_mul_bilinear_sub_translate_le B hB hBpos hf hζ hζpos s
  have hdiag : _root_.MeasureTheory.Integrable (fun t => B (f t) (f t)) volume :=
    MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable (fun _ : ℝ => B)
      (fun _ _ => _root_.MeasureTheory.aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl) hf hf
  have hζshift : _root_.MeasureTheory.MemLp (fun t => ζ (t - s)) ∞ volume := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      hζ.comp_measurePreserving (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume (-s))
  have hdiff : _root_.MeasureTheory.Integrable (fun t => (ζ (t - s) - ζ t) * B (f t) (f t)) volume :=
    hdiag.mul_of_top_right (hζshift.sub hζ)
  have hb : (∫ t, (ζ (t - s) - ζ t) * B (f t) (f t)) ≤
      (K : ℝ) * s * ∫ t, B (f t) (f t) := by
    rw [← _root_.MeasureTheory.integral_const_mul]
    apply _root_.MeasureTheory.integral_mono_ae hdiff (hdiag.const_mul _)
    filter_upwards [] with t
    apply mul_le_mul_of_nonneg_right _ (hBpos _)
    have h := hζlip.dist_le_mul (t - s) t
    simp only [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hs] at h
    exact (le_abs_self _).trans h
  have hid : (∫ t, ζ t * B (f t) (s⁻¹ • (f (t + s) - f t))) =
      s⁻¹ * ∫ t, ζ t * B (f t) (f (t + s) - f t) := by
    rw [← _root_.MeasureTheory.integral_const_mul]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [] with t
    simp only [map_smul, smul_eq_mul]
    ring
  rw [hid]
  have hbound : (∫ t, ζ t * B (f t) (f (t + s) - f t)) ≤
      s * (((K : ℝ) / 2) * ∫ t, B (f t) (f t)) := by nlinarith
  exact (mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hs.le)).trans_eq
    (by rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_mul_bilinear_diffQuot_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_mul_bilinear_diffQuot_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_mul_bilinear_diffQuot_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_mul_bilinear_diffQuot_le

theorem integral_mul_bilinear_diffQuot_ge
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B) (hBneg : ∀ x, B x x ≤ 0)
    {f : ℝ → X} (hf : _root_.MeasureTheory.MemLp f 2 _root_.MeasureTheory.MeasureSpace.volume)
    {ζ : ℝ → ℝ} (hζ : _root_.MeasureTheory.MemLp ζ ∞ _root_.MeasureTheory.MeasureSpace.volume) (hζpos : ∀ᵐ t, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ) {s : ℝ} (hs : 0 < s) :
    ((K : ℝ) / 2) * (∫ t, B (f t) (f t)) ≤
      ∫ t, ζ t * B (f t) (s⁻¹ • (f (t + s) - f t)) := by
  have hsym : (-B).flip = -B := by
    ext x y
    have h := congrArg (fun L : X →L[ℝ] X →L[ℝ] ℝ => L x y) hB
    change -B y x = -B x y
    exact congrArg Neg.neg h
  have hpos : ∀ x, 0 ≤ (-B) x x := by
    intro x
    change 0 ≤ -B x x
    exact neg_nonneg.mpr (hBneg x)
  have h := integral_mul_bilinear_diffQuot_le (-B) hsym hpos hf hζ hζpos hζlip hs
  simp only [neg_apply, mul_neg, _root_.MeasureTheory.integral_neg] at h
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_mul_bilinear_diffQuot_ge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_mul_bilinear_diffQuot_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_mul_bilinear_diffQuot_ge ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_mul_bilinear_diffQuot_ge

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem tendsto_integral_bilinear_steklovAverage
    (A : ℝ → X →L[ℝ] Y →L[ℝ] Z)
    (hA : ∀ x y, _root_.MeasureTheory.AEStronglyMeasurable (fun t => A t x y) _root_.MeasureTheory.MeasureSpace.volume)
    {C : ℝ} (hC : ∀ᵐ t ∂volume, ‖A t‖ ≤ C)
    (u : _root_.MeasureTheory.Lp X 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)) (v : _root_.MeasureTheory.Lp Y 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)) :
    _root_.Filter.Tendsto (fun h => ∫ t, A t (u t) (steklovAverage h v t))
      (𝓝[≠] 0) (𝓝 (∫ t, A t (u t) (v t))) := by
  have h := ((MeasureTheory.continuous_integral_bilinear_lp_right A hA hC u).tendsto v).comp
    (Lp.tendsto_steklovAverage v)
  apply h.congr'
  filter_upwards [] with h
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [Lp.coeFn_steklovAverage h v] with t ht
  rw [ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.tendsto_integral_bilinear_steklovAverage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.tendsto_integral_bilinear_steklovAverage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.tendsto_integral_bilinear_steklovAverage ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.tendsto_integral_bilinear_steklovAverage

variable [CompleteSpace X]

theorem integral_bilinear_le_of_cutoff_steklov_identity
    (A D : ℝ → X →L[ℝ] X →L[ℝ] ℝ)
    (hA : ∀ x y, _root_.MeasureTheory.AEStronglyMeasurable (fun t => A t x y) _root_.MeasureTheory.MeasureSpace.volume)
    (hD : ∀ x y, _root_.MeasureTheory.AEStronglyMeasurable (fun t => D t x y) _root_.MeasureTheory.MeasureSpace.volume)
    {CA CD : ℝ} (hCA : ∀ᵐ t ∂volume, ‖A t‖ ≤ CA)
    (hCD : ∀ᵐ t ∂volume, ‖D t‖ ≤ CD)
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : B.flip = B) (hBpos : ∀ x, 0 ≤ B x x)
    (u : _root_.MeasureTheory.Lp X 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ))
    {ζ : ℝ → ℝ} (hζ : _root_.MeasureTheory.MemLp ζ ∞ _root_.MeasureTheory.MeasureSpace.volume) (hζpos : ∀ᵐ t ∂volume, 0 ≤ ζ t)
    {K : ℝ≥0} (hζlip : LipschitzWith K ζ)
    (htest : ∀ s : ℝ, 0 < s →
      (∫ t, A t (u t) (steklovAverage s u t)) =
        (∫ t, D t (u t) (steklovAverage s u t)) +
          ∫ t, ζ t * B (u t) (s⁻¹ • (u (t + s) - u t))) :
    (∫ t, A t (u t) (u t)) ≤
      (∫ t, D t (u t) (u t)) + ((K : ℝ) / 2) * ∫ t, B (u t) (u t) := by
  have hfilter : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono _ (fun _ h => ne_of_gt h)
  have hleft : _root_.Filter.Tendsto (fun s => ∫ t, A t (u t) (steklovAverage s u t))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ t, A t (u t) (u t))) := (tendsto_integral_bilinear_steklovAverage A hA hCA u u).mono_left
    hfilter
  have hright := ((tendsto_integral_bilinear_steklovAverage D hD hCD u u).mono_left
    hfilter).add_const (((K : ℝ) / 2) * ∫ t, B (u t) (u t))
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [htest s hs]
  exact add_le_add_right
    (integral_mul_bilinear_diffQuot_le B hB hBpos (Lp.memLp u) hζ hζpos hζlip hs) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_bilinear_le_of_cutoff_steklov_identity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_bilinear_le_of_cutoff_steklov_identity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_bilinear_le_of_cutoff_steklov_identity ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.integral_bilinear_le_of_cutoff_steklov_identity

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
