import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Prod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.Topology

namespace MeasureTheory.Lp
open _root_.MeasureTheory _root_.MeasureTheory.Lp

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} [SFinite μ]

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
local notation "E" => EuclideanSpace ℝ (Fin d)
open _root_.MeasureTheory _root_.MeasureTheory.Lp in
local notation "X" => _root_.MeasureTheory.Lp ℝ 2 (μ.prod (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private theorem measurePreserving_spatialTranslate (v : E) :
    MeasurePreserving (fun p : Z × E => (p.1, p.2 + v)) (μ.prod _root_.MeasureTheory.MeasureSpace.volume) (μ.prod _root_.MeasureTheory.MeasureSpace.volume) :=
  (MeasurePreserving.id μ).prod (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume v)

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.measurePreserving_spatialTranslate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.measurePreserving_spatialTranslate target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
def spatialTranslate (v : E) (u : X) : X :=
  _root_.MeasureTheory.Lp.compMeasurePreserving _ (measurePreserving_spatialTranslate v) u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.spatialTranslate then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.spatialTranslate"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.spatialTranslate ``Submission.MeasureTheory.Lp.spatialTranslate

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem coeFn_spatialTranslate (v : E) (u : X) :
    spatialTranslate v u =ᵐ[μ.prod _root_.MeasureTheory.MeasureSpace.volume] fun p => u (p.1, p.2 + v) :=
  _root_.MeasureTheory.Lp.coeFn_compMeasurePreserving u (measurePreserving_spatialTranslate v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.coeFn_spatialTranslate then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.coeFn_spatialTranslate"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.coeFn_spatialTranslate ``Submission.MeasureTheory.Lp.coeFn_spatialTranslate

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
@[simp] theorem norm_spatialTranslate (v : E) (u : X) : ‖spatialTranslate v u‖ = ‖u‖ :=
  _root_.MeasureTheory.Lp.norm_compMeasurePreserving u _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.norm_spatialTranslate then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.norm_spatialTranslate"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.norm_spatialTranslate ``Submission.MeasureTheory.Lp.norm_spatialTranslate

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
@[simp] theorem spatialTranslate_zero (u : X) : spatialTranslate 0 u = u := by
  simp only [spatialTranslate, add_zero, Prod.mk.eta]
  exact _root_.MeasureTheory.Lp.compMeasurePreserving_id_apply u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.spatialTranslate_zero then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.spatialTranslate_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.spatialTranslate_zero ``Submission.MeasureTheory.Lp.spatialTranslate_zero

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
def spatialSteklovAverage (v : E) (h : ℝ) (u : X) : X :=
  h⁻¹ • ∫ r in (0 : ℝ)..h, spatialTranslate (r • v) u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.spatialSteklovAverage then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.spatialSteklovAverage"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.spatialSteklovAverage ``Submission.MeasureTheory.Lp.spatialSteklovAverage

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem norm_spatialSteklovAverage_le (v : E) (h : ℝ) (u : X) :
    ‖spatialSteklovAverage v h u‖ ≤ ‖u‖ := by
  by_cases hh : h = 0
  · simp [spatialSteklovAverage, hh]
  have hhabs : |h| ≠ 0 := abs_ne_zero.mpr hh
  calc
    ‖spatialSteklovAverage v h u‖ = |h|⁻¹ * ‖∫ r in (0 : ℝ)..h, spatialTranslate (r • v) u‖ := by
      rw [spatialSteklovAverage, norm_smul, Real.norm_eq_abs, abs_inv]
    _ ≤ |h|⁻¹ * (‖u‖ * |h|) := by
      gcongr
      simpa only [sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := h)
        (fun r _ => (norm_spatialTranslate (r • v) u).le)
    _ = ‖u‖ := by field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.norm_spatialSteklovAverage_le then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.norm_spatialSteklovAverage_le"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.norm_spatialSteklovAverage_le ``Submission.MeasureTheory.Lp.norm_spatialSteklovAverage_le

end MeasureTheory.Lp

namespace MeasureTheory.Lp
open _root_.MeasureTheory _root_.MeasureTheory.Lp

variable {d : ℕ} {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
local notation "E" => EuclideanSpace ℝ (Fin d)
open _root_.MeasureTheory _root_.MeasureTheory.Lp in
local notation "X" => _root_.MeasureTheory.Lp ℝ 2 (μ.prod (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E))

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem continuous_spatialTranslate (u : X) : Continuous (fun v : E => spatialTranslate v u) := by
  let g : C(E, C(ℝ × E, ℝ × E)) := (ContinuousMap.mk
    (fun p : E × (ℝ × E) => (p.2.1, p.2.2 + p.1))
    ((continuous_fst.comp continuous_snd).prodMk
      ((continuous_snd.comp continuous_snd).add continuous_fst))).curry
  exact continuous_const.compMeasurePreservingLp g.continuous
    (fun v => measurePreserving_spatialTranslate v) (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.continuous_spatialTranslate then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.continuous_spatialTranslate"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.continuous_spatialTranslate ``Submission.MeasureTheory.Lp.continuous_spatialTranslate

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem tendsto_spatialSteklovAverage (v : E) (u : X) :
    Tendsto (fun h => spatialSteklovAverage v h u) (𝓝[≠] 0) (𝓝 u) := by
  have hc : Continuous (fun r : ℝ => spatialTranslate (r • v) u) :=
    (continuous_spatialTranslate u).comp (continuous_id.smul continuous_const)
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 0) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simpa only [zero_smul, spatialTranslate_zero, spatialSteklovAverage, zero_add,
    intervalIntegral.integral_same, sub_zero] using hd.tendsto_slope_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.tendsto_spatialSteklovAverage then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.tendsto_spatialSteklovAverage"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.tendsto_spatialSteklovAverage ``Submission.MeasureTheory.Lp.tendsto_spatialSteklovAverage

end MeasureTheory.Lp


namespace MeasureTheory.Lp
open _root_.MeasureTheory _root_.MeasureTheory.Lp

variable {d : ℕ} {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Y" => ℝ × E
open _root_.MeasureTheory _root_.MeasureTheory.Lp in
local notation "ν" => μ.prod (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)
open _root_.MeasureTheory _root_.MeasureTheory.Lp in
local notation "X" => _root_.MeasureTheory.Lp ℝ 2 ν

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private def setIntegralContinuousLinearMap (S : Set Y) (hS : MeasurableSet S)
    (hvol : ν S ≠ ∞) : X →L[ℝ] ℝ :=
  (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing ν 2 2 (_root_.MeasureTheory.indicatorConstLp 2 hS hvol (1 : ℝ))

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.setIntegralContinuousLinearMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.setIntegralContinuousLinearMap target :: scope.openDecls } }

omit [IsLocallyFiniteMeasure μ] in
open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private theorem setIntegralContinuousLinearMap_apply (S : Set Y) (hS : MeasurableSet S)
    (hvol : ν S ≠ ∞) (u : X) :
    setIntegralContinuousLinearMap S hS hvol u = ∫ t in S, u t ∂ν := by
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

omit [IsLocallyFiniteMeasure μ] in
open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private theorem setIntegral_norm_le_mul_norm (S : Set Y) (hS : MeasurableSet S)
    (hvol : ν S ≠ ∞) (u : X) :
    (∫ t in S, ‖u t‖ ∂ν) ≤ ‖setIntegralContinuousLinearMap S hS hvol‖ * ‖u‖ := by
  let v : X := (Lp.memLp u).norm.toLp (fun t => ‖u t‖)
  have hnorm : ‖v‖ = ‖u‖ := by
    rw [show v = (Lp.memLp u).norm.toLp (fun t => ‖u t‖) from rfl, Lp.norm_toLp, _root_.MeasureTheory.eLpNorm_norm]
    rfl
  have heq : (∫ t in S, ‖u t‖ ∂ν) = setIntegralContinuousLinearMap S hS hvol v := by
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

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private theorem integrable_translate_prod (u : X)
    (v : E) (a b : ℝ) {S : Set Y} (hS : MeasurableSet S) (hvol : ν S < ∞) :
    _root_.MeasureTheory.Integrable (fun q : ℝ × Y => u (q.2.1, q.2.2 + q.1 • v))
      ((volume.restrict (_root_.Set.Ioc a b)).prod ((ν).restrict S)) := by
  let : _root_.MeasureTheory.IsFiniteMeasure ((ν).restrict S) := ⟨by simpa using hvol⟩
  have hmeas : _root_.MeasureTheory.StronglyMeasurable (fun q : ℝ × Y => u (q.2.1, q.2.2 + q.1 • v)) :=
    (Lp.stronglyMeasurable u).comp_measurable ((measurable_fst.comp measurable_snd).prodMk ((measurable_snd.comp measurable_snd).add (measurable_fst.smul_const v)))
  apply (_root_.MeasureTheory.integrable_prod_iff hmeas.aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun r =>
      (((Lp.memLp u).comp_measurePreserving ((MeasurePreserving.id μ).prod (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume (r • v)))).restrict S).integrable (by norm_num)
  · apply Integrable.mono' (_root_.MeasureTheory.integrable_const (‖setIntegralContinuousLinearMap S hS hvol.ne‖ * ‖u‖))
      hmeas.norm.aestronglyMeasurable.integral_prod_right'
    refine Eventually.of_forall fun r => ?_
    rw [Real.norm_of_nonneg (_root_.MeasureTheory.integral_nonneg (μ := (ν).restrict S) fun t : Y => norm_nonneg (u (t.1, t.2 + r • v)))]
    have heq : (∫ t in S, ‖u (t.1, t.2 + r • v)‖ ∂ν) = ∫ t in S, ‖spatialTranslate (r • v) u t‖ ∂ν :=
      _root_.MeasureTheory.integral_congr_ae (_root_.MeasureTheory.ae_restrict_of_ae ((coeFn_spatialTranslate (r • v) u).fun_comp _root_.Norm.norm).symm)
    rw [heq]
    exact (setIntegral_norm_le_mul_norm S hS hvol.ne (spatialTranslate (r • v) u)).trans_eq
      (by rw [norm_spatialTranslate])

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.integrable_translate_prod
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.integrable_translate_prod target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private theorem coeFn_setIntegral_translate (u : X)
    (v : E) (a b : ℝ) :
    ((∫ r in _root_.Set.Ioc a b, spatialTranslate (r • v) u : X) : Y → ℝ) =ᵐ[ν]
      fun t => ∫ r in _root_.Set.Ioc a b, u (t.1, t.2 + r • v) := by
  apply _root_.MeasureTheory.ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro S hS hvol
    let : _root_.MeasureTheory.IsFiniteMeasure ((ν).restrict S) := ⟨by simpa using hvol⟩
    exact ((Lp.memLp _).restrict S).integrable (by norm_num)
  · intro S hS hvol
    exact (integrable_translate_prod u v a b hS hvol).integral_prod_right
  · intro S hS hvol
    have htranslate : _root_.MeasureTheory.IntegrableOn (fun r => spatialTranslate (r • v) u) (_root_.Set.Ioc a b) :=
      ((continuous_spatialTranslate u).comp (continuous_id.smul continuous_const)).integrableOn_Icc.mono_set _root_.Set.Ioc_subset_Icc_self
    rw [← setIntegralContinuousLinearMap_apply S hS hvol.ne]
    rw [← ContinuousLinearMap.integral_comp_comm _ htranslate]
    calc
      _ = ∫ r in _root_.Set.Ioc a b, ∫ t in S, u (t.1, t.2 + r • v) ∂ν := by
        apply _root_.MeasureTheory.integral_congr_ae
        refine Eventually.of_forall fun r => ?_
        dsimp only
        rw [setIntegralContinuousLinearMap_apply]
        exact _root_.MeasureTheory.integral_congr_ae (_root_.MeasureTheory.ae_restrict_of_ae (coeFn_spatialTranslate (r • v) u))
      _ = _ := _root_.MeasureTheory.integral_integral_swap (integrable_translate_prod u v a b hS hvol)

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.coeFn_setIntegral_translate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.coeFn_setIntegral_translate target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
private theorem coeFn_intervalIntegral_translate (u : X)
    (v : E) (a b : ℝ) :
    ((∫ r in a..b, spatialTranslate (r • v) u : X) : Y → ℝ) =ᵐ[ν]
      fun t => ∫ r in a..b, u (t.1, t.2 + r • v) := by
  simp only [intervalIntegral]
  exact (_root_.MeasureTheory.Lp.coeFn_sub _ _).trans
    ((coeFn_setIntegral_translate u v a b).sub (coeFn_setIntegral_translate u v b a))

run_cmd do
  let target := ``Submission.MeasureTheory.Lp.coeFn_intervalIntegral_translate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.Lp.coeFn_intervalIntegral_translate target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem coeFn_spatialSteklovAverage (v : E) (h : ℝ) (u : X) :
    spatialSteklovAverage v h u =ᵐ[ν]
      fun z => h⁻¹ * ∫ r in (0 : ℝ)..h, u (z.1, z.2 + r • v) := by
  rw [spatialSteklovAverage]
  filter_upwards [_root_.MeasureTheory.Lp.coeFn_smul (h⁻¹) (∫ r in (0 : ℝ)..h, spatialTranslate (r • v) u),
    coeFn_intervalIntegral_translate u v 0 h] with z hsmul hint
  rw [hsmul, Pi.smul_apply, hint, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.coeFn_spatialSteklovAverage then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.coeFn_spatialSteklovAverage"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.coeFn_spatialSteklovAverage ``Submission.MeasureTheory.Lp.coeFn_spatialSteklovAverage

end MeasureTheory.Lp
