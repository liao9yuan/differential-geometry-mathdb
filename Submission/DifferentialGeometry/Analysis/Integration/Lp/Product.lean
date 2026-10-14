import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Set
open scoped _root_.ENNReal _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable {μ : Measure A} {ν : Measure B} [SFinite ν]
variable {p : ℝ≥0∞}

section ENorm

variable {E : Type*} [ENorm E]

open _root_.MeasureTheory in
theorem eLpNorm_eLpNorm {f : A × B → E}
    (hp : p ≠ (⊤ : ℝ≥0∞))
    (hf : AEMeasurable (fun z => ‖f z‖ₑ) (μ.prod ν)) :
    _root_.MeasureTheory.eLpNorm (fun a => _root_.MeasureTheory.eLpNorm (fun b => f (a, b)) p ν) p μ =
      eLpNorm f p (μ.prod ν) := by
  by_cases hp₀ : p = 0
  · simp [hp₀]
  have hp' : p.toReal ≠ 0 := (ENNReal.toReal_pos hp₀ hp).ne'
  simp_rw [_root_.MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp, enorm_eq_self,
    ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp', ENNReal.rpow_one]
  rw [← _root_.MeasureTheory.lintegral_prod _ (hf.pow_const p.toReal)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.eLpNorm_eLpNorm then
    throwError "Refusing to shadow existing declaration MeasureTheory.eLpNorm_eLpNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.eLpNorm_eLpNorm ``Submission.MeasureTheory.eLpNorm_eLpNorm

end ENorm

section ContinuousENorm

variable {E : Type*} [TopologicalSpace E] [ContinuousENorm E]

open _root_.MeasureTheory _root_.MeasureTheory.MemLp in
theorem MemLp.prodMk_left {f : A × B → E}
    (hf : _root_.MeasureTheory.MemLp f p (μ.prod ν)) (hp : p ≠ (⊤ : ℝ≥0∞)) :
    ∀ᵐ a ∂μ, _root_.MeasureTheory.MemLp (fun b => f (a, b)) p ν := by
  by_cases hp₀ : p = 0
  · subst p
    filter_upwards [hf.aestronglyMeasurable.prodMk_left] with a ha
    exact ⟨ha, by simp⟩
  have hnorm := eLpNorm_eLpNorm hp hf.aestronglyMeasurable.enorm
  have hfinite : (∫⁻ a, (_root_.MeasureTheory.eLpNorm (fun b => f (a, b)) p ν) ^ p.toReal ∂μ) < ⊤ := by
    apply (ENNReal.rpow_lt_top_iff_of_pos (one_div_pos.mpr (ENNReal.toReal_pos hp₀ hp))).mp
    simpa only [_root_.MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp, enorm_eq_self] using
      (hnorm.trans_lt hf.2)
  have hmeas : AEMeasurable (fun a => (_root_.MeasureTheory.eLpNorm (fun b => f (a, b)) p ν) ^ p.toReal) μ := by
    simp_rw [_root_.MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp, ← ENNReal.rpow_mul,
      one_div, inv_mul_cancel₀ (ENNReal.toReal_pos hp₀ hp).ne', ENNReal.rpow_one]
    exact (hf.aestronglyMeasurable.enorm.pow_const p.toReal).lintegral_prod_right'
  filter_upwards [hf.aestronglyMeasurable.prodMk_left, _root_.MeasureTheory.ae_lt_top' hmeas hfinite.ne] with a ha₁ ha₂
  exact ⟨ha₁, (ENNReal.rpow_lt_top_iff_of_pos (ENNReal.toReal_pos hp₀ hp)).mp ha₂⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MeasureTheory.MemLp
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.MemLp.prodMk_left then
    throwError "Refusing to shadow existing declaration MeasureTheory.MemLp.prodMk_left"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.MemLp.prodMk_left ``Submission.MeasureTheory.MemLp.prodMk_left

open _root_.MeasureTheory _root_.MeasureTheory.MemLp in
theorem MemLp.prodMk_left_top {f : A × B → E}
    (hf : _root_.MeasureTheory.MemLp f ∞ (μ.prod ν)) :
    ∀ᵐ a ∂μ, _root_.MeasureTheory.MemLp (fun b => f (a, b)) ∞ ν := by
  have hfinite : _root_.MeasureTheory.eLpNormEssSup f (μ.prod ν) ≠ ∞ := hf.eLpNorm_ne_top
  have hbound : ∀ᵐ z ∂μ.prod ν,
      ‖f z‖ₑ ≤ (_root_.MeasureTheory.eLpNormEssSup f (μ.prod ν)).toNNReal := by
    rw [ENNReal.coe_toNNReal hfinite]
    exact _root_.MeasureTheory.ae_le_eLpNormEssSup
  filter_upwards [hf.aestronglyMeasurable.prodMk_left,
    Measure.ae_ae_of_ae_prod hbound] with a ha hb
  exact _root_.MeasureTheory.memLp_top_of_bound_enorm ha _ hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.MemLp.prodMk_left_top then
    throwError "Refusing to shadow existing declaration MeasureTheory.MemLp.prodMk_left_top"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.MemLp.prodMk_left_top ``Submission.MeasureTheory.MemLp.prodMk_left_top

open _root_.MeasureTheory in
theorem eLpNorm_eLpNorm_toReal {f : A × B → E}
    (hf : _root_.MeasureTheory.MemLp f p (μ.prod ν)) (hp : p ≠ (⊤ : ℝ≥0∞)) :
    _root_.MeasureTheory.eLpNorm (fun a => (_root_.MeasureTheory.eLpNorm (fun b => f (a, b)) p ν).toReal) p μ =
      eLpNorm f p (μ.prod ν) := by
  rw [← eLpNorm_eLpNorm hp hf.aestronglyMeasurable.enorm]
  apply _root_.MeasureTheory.eLpNorm_congr_enorm_ae
  filter_upwards [hf.prodMk_left hp] with a ha
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ha.2.ne, enorm_eq_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.eLpNorm_eLpNorm_toReal then
    throwError "Refusing to shadow existing declaration MeasureTheory.eLpNorm_eLpNorm_toReal"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.eLpNorm_eLpNorm_toReal ``Submission.MeasureTheory.eLpNorm_eLpNorm_toReal

open _root_.MeasureTheory _root_.MeasureTheory.MemLp in
theorem MemLp.eLpNorm_toReal {f : A × B → E}
    (hf : _root_.MeasureTheory.MemLp f p (μ.prod ν)) (hp : p ≠ (⊤ : ℝ≥0∞)) :
    MemLp (fun a => (_root_.MeasureTheory.eLpNorm (fun b => f (a, b)) p ν).toReal) p μ := by
  by_cases hp₀ : p = 0
  · subst p
    simp only [_root_.MeasureTheory.eLpNorm_exponent_zero, ENNReal.toReal_zero]
    exact ⟨aestronglyMeasurable_const, by simp⟩
  constructor
  · apply AEMeasurable.aestronglyMeasurable
    simp_rw [_root_.MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp]
    exact (((hf.aestronglyMeasurable.enorm.pow_const p.toReal).lintegral_prod_right').pow_const
      (1 / p.toReal)).ennreal_toReal
  · rw [eLpNorm_eLpNorm_toReal hf hp]
    exact hf.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.MemLp.eLpNorm_toReal then
    throwError "Refusing to shadow existing declaration MeasureTheory.MemLp.eLpNorm_toReal"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.MemLp.eLpNorm_toReal ``Submission.MeasureTheory.MemLp.eLpNorm_toReal

end ContinuousENorm

variable {E : Type*} [NormedAddCommGroup E]

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem Lp.ext_curry {f g : _root_.MeasureTheory.Lp E p (μ.prod ν)}
    (h : ∀ᵐ a ∂μ, (fun b => f (a, b)) =ᵐ[ν] fun b => g (a, b)) : f = g := by
  apply Lp.ext
  exact (Measure.ae_prod_iff_ae_ae
    ((Lp.stronglyMeasurable f).measurableSet_eq_fun (Lp.stronglyMeasurable g))).mpr h

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MeasureTheory.Lp
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.ext_curry then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.ext_curry"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.ext_curry ``Submission.MeasureTheory.Lp.ext_curry

variable [Fact (1 ≤ p)]

open _root_.MeasureTheory in
private def uncurrySimple (f : _root_.MeasureTheory.SimpleFunc A (_root_.MeasureTheory.Lp E p ν)) : A × B → E :=
  fun z => f z.1 z.2

run_cmd do
  let target := ``Submission.MeasureTheory.uncurrySimple
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.uncurrySimple target :: scope.openDecls } }

omit [SFinite ν] [Fact (1 ≤ p)] in
open _root_.MeasureTheory in
private theorem stronglyMeasurable_uncurrySimple (f : _root_.MeasureTheory.SimpleFunc A (_root_.MeasureTheory.Lp E p ν)) :
    StronglyMeasurable (uncurrySimple f) := by
  classical
  have h (v : _root_.MeasureTheory.Lp E p ν) : _root_.MeasureTheory.StronglyMeasurable
      ((Prod.fst ⁻¹' (f ⁻¹' {v})).indicator (fun z : A × B => v z.2)) :=
    ((Lp.stronglyMeasurable v).comp_measurable measurable_snd).indicator
      ((f.measurableSet_fiber v).preimage measurable_fst)
  convert Finset.stronglyMeasurable_sum f.range (fun v _ => h v) using 1
  funext z
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single (f z.1)]
  · simp only [Set.indicator_of_mem (show z ∈ Prod.fst ⁻¹' (f ⁻¹' {f z.1}) from rfl)]
    rfl
  · intro v _ hv
    exact Set.indicator_of_notMem
      (show z ∉ Prod.fst ⁻¹' (f ⁻¹' {v}) from fun h => hv (Eq.symm h)) _
  · intro hnot
    exact False.elim (hnot (f.mem_range_self z.1))

run_cmd do
  let target := ``Submission.MeasureTheory.stronglyMeasurable_uncurrySimple
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.stronglyMeasurable_uncurrySimple target :: scope.openDecls } }

open _root_.MeasureTheory in
private theorem eLpNorm_uncurrySimple (f : _root_.MeasureTheory.SimpleFunc A (_root_.MeasureTheory.Lp E p ν))
    (hp : p ≠ (⊤ : ℝ≥0∞)) :
    eLpNorm (uncurrySimple f) p (μ.prod ν) = _root_.MeasureTheory.eLpNorm f p μ := by
  rw [← eLpNorm_eLpNorm hp (stronglyMeasurable_uncurrySimple f).enorm.aemeasurable]
  change _root_.MeasureTheory.eLpNorm (fun a => _root_.MeasureTheory.eLpNorm (f a) p ν) p μ = _
  simp_rw [← Lp.enorm_def]
  exact _root_.MeasureTheory.eLpNorm_enorm f

run_cmd do
  let target := ``Submission.MeasureTheory.eLpNorm_uncurrySimple
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.eLpNorm_uncurrySimple target :: scope.openDecls } }

open _root_.MeasureTheory in
private theorem memLp_uncurrySimple {f : _root_.MeasureTheory.SimpleFunc A (_root_.MeasureTheory.Lp E p ν)}
    (hf : _root_.MeasureTheory.MemLp f p μ) (hp : p ≠ (⊤ : ℝ≥0∞)) :
    MemLp (uncurrySimple f) p (μ.prod ν) := by
  refine ⟨(stronglyMeasurable_uncurrySimple f).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_uncurrySimple f hp]
  exact hf.2

run_cmd do
  let target := ``Submission.MeasureTheory.memLp_uncurrySimple
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.memLp_uncurrySimple target :: scope.openDecls } }

open _root_.MeasureTheory in
private def uncurrySimpleLp (hp : p ≠ (⊤ : ℝ≥0∞))
    (f : Lp.simpleFunc (_root_.MeasureTheory.Lp E p ν) p μ) : _root_.MeasureTheory.Lp E p (μ.prod ν) :=
  (memLp_uncurrySimple (Lp.simpleFunc.memLp f) hp).toLp _

run_cmd do
  let target := ``Submission.MeasureTheory.uncurrySimpleLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.uncurrySimpleLp target :: scope.openDecls } }

open _root_.MeasureTheory in
private theorem uncurrySimpleLp_coeFn (hp : p ≠ (⊤ : ℝ≥0∞))
    (f : Lp.simpleFunc (_root_.MeasureTheory.Lp E p ν) p μ) :
    ∀ᵐ a ∂μ, (fun b => uncurrySimpleLp hp f (a, b)) =ᵐ[ν]
      ((f : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ) a : B → E) := by
  have h := Measure.ae_ae_of_ae_prod
    (MemLp.coeFn_toLp (memLp_uncurrySimple (Lp.simpleFunc.memLp f) hp))
  filter_upwards [h, Lp.simpleFunc.toSimpleFunc_eq_toFun f] with a ha₁ ha₂
  filter_upwards [ha₁] with b hb
  exact hb.trans (congrArg (fun v : _root_.MeasureTheory.Lp E p ν => v b) ha₂)

run_cmd do
  let target := ``Submission.MeasureTheory.uncurrySimpleLp_coeFn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.uncurrySimpleLp_coeFn target :: scope.openDecls } }

open _root_.MeasureTheory in
private theorem norm_uncurrySimpleLp (hp : p ≠ (⊤ : ℝ≥0∞))
    (f : Lp.simpleFunc (_root_.MeasureTheory.Lp E p ν) p μ) :
    ‖uncurrySimpleLp hp f‖ = ‖f‖ := by
  rw [uncurrySimpleLp, Lp.norm_toLp, eLpNorm_uncurrySimple _ hp]
  exact (Lp.simpleFunc.norm_toSimpleFunc f).symm

run_cmd do
  let target := ``Submission.MeasureTheory.norm_uncurrySimpleLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.norm_uncurrySimpleLp target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem Lp.exists_subseq_tendsto_eLpNorm_prodMk_left
    {f : ℕ → _root_.MeasureTheory.Lp E p (μ.prod ν)} {g : _root_.MeasureTheory.Lp E p (μ.prod ν)}
    (hp : p ≠ (⊤ : ℝ≥0∞)) (hfg : _root_.Filter.Tendsto f _root_.Filter.atTop (𝓝 g)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ᵐ a ∂μ,
      _root_.Filter.Tendsto (fun k => _root_.MeasureTheory.eLpNorm (fun b => f (s k) (a, b) - g (a, b)) p ν)
        atTop (𝓝 0) := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  let ψ : ℕ → A → ℝ := fun k a =>
    (_root_.MeasureTheory.eLpNorm (fun b => f k (a, b) - g (a, b)) p ν).toReal
  have hmem (k : ℕ) : _root_.MeasureTheory.MemLp (fun z => f k z - g z) p (μ.prod ν) :=
    (Lp.memLp (f k)).sub (Lp.memLp g)
  have hψmem (k : ℕ) : _root_.MeasureTheory.MemLp (ψ k) p μ := (hmem k).eLpNorm_toReal hp
  have hψlim : _root_.Filter.Tendsto (fun k => _root_.MeasureTheory.eLpNorm (ψ k - 0) p μ) _root_.Filter.atTop (𝓝 0) := by
    have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' f g).mp hfg
    apply h.congr'
    filter_upwards [] with k
    rw [sub_zero]
    exact (eLpNorm_eLpNorm_toReal (hmem k) hp).symm
  obtain ⟨s, hs, hslim⟩ := (_root_.MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm hp₀
    (fun k => (hψmem k).aestronglyMeasurable) _root_.MeasureTheory.aestronglyMeasurable_const hψlim).exists_seq_tendsto_ae
  refine ⟨s, hs, ?_⟩
  filter_upwards [hslim, _root_.MeasureTheory.ae_all_iff.mpr (fun k => (hmem k).prodMk_left hp)] with a ha hfinite
  exact (ENNReal.tendsto_toReal_zero_iff (fun k => (hfinite (s k)).2.ne)).mp ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.exists_subseq_tendsto_eLpNorm_prodMk_left then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.exists_subseq_tendsto_eLpNorm_prodMk_left"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.exists_subseq_tendsto_eLpNorm_prodMk_left ``Submission.MeasureTheory.Lp.exists_subseq_tendsto_eLpNorm_prodMk_left

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 E]

attribute [local instance] Lp.simpleFunc.module Lp.simpleFunc.normedSpace

open _root_.MeasureTheory in
private def uncurrySimpleLinear (hp : p ≠ (⊤ : ℝ≥0∞)) :
    Lp.simpleFunc (_root_.MeasureTheory.Lp E p ν) p μ →ₗ[𝕜] _root_.MeasureTheory.Lp E p (μ.prod ν) where
  toFun := uncurrySimpleLp hp
  map_add' f g := by
    apply Lp.ext_curry
    filter_upwards [uncurrySimpleLp_coeFn hp (f + g), uncurrySimpleLp_coeFn hp f,
      uncurrySimpleLp_coeFn hp g,
      Lp.coeFn_add (f : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ) (g : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ),
      Measure.ae_ae_of_ae_prod (Lp.coeFn_add (uncurrySimpleLp hp f) (uncurrySimpleLp hp g))]
      with a hfg hf hg ht hprod
    filter_upwards [hfg, hf, hg, hprod,
      Lp.coeFn_add ((f : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ) a) ((g : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ) a)]
      with b hfg' hf' hg' hprod' hab
    calc
      uncurrySimpleLp hp (f + g) (a, b) = ((f + g : Lp.simpleFunc (_root_.MeasureTheory.Lp E p ν) p μ) :
          Lp (_root_.MeasureTheory.Lp E p ν) p μ) a b := hfg'
      _ = (((f : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ) a) + ((g : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ) a)) b :=
        congrArg (fun v : _root_.MeasureTheory.Lp E p ν => v b) ht
      _ = (f : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ) a b + (g : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ) a b := hab
      _ = uncurrySimpleLp hp f (a, b) + uncurrySimpleLp hp g (a, b) := by rw [hf', hg']
      _ = (uncurrySimpleLp hp f + uncurrySimpleLp hp g) (a, b) := hprod'.symm
  map_smul' c f := by
    apply Lp.ext_curry
    filter_upwards [uncurrySimpleLp_coeFn hp (c • f), uncurrySimpleLp_coeFn hp f,
      Lp.coeFn_smul c (f : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ),
      Measure.ae_ae_of_ae_prod (Lp.coeFn_smul c (uncurrySimpleLp hp f))]
      with a hcf hf ht hprod
    filter_upwards [hcf, hf, hprod, Lp.coeFn_smul c ((f : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ) a)]
      with b hcf' hf' hprod' hcb
    calc
      uncurrySimpleLp hp (c • f) (a, b) = ((c • f : Lp.simpleFunc (_root_.MeasureTheory.Lp E p ν) p μ) :
          Lp (_root_.MeasureTheory.Lp E p ν) p μ) a b := hcf'
      _ = (c • ((f : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ) a)) b := congrArg (fun v : _root_.MeasureTheory.Lp E p ν => v b) ht
      _ = c • (f : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ) a b := hcb
      _ = c • uncurrySimpleLp hp f (a, b) := by rw [hf']
      _ = (c • uncurrySimpleLp hp f) (a, b) := hprod'.symm

run_cmd do
  let target := ``Submission.MeasureTheory.uncurrySimpleLinear
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.uncurrySimpleLinear target :: scope.openDecls } }

open _root_.MeasureTheory in
private def uncurrySimpleIsometry (hp : p ≠ (⊤ : ℝ≥0∞)) :
    Lp.simpleFunc (_root_.MeasureTheory.Lp E p ν) p μ →ₗᵢ[𝕜] _root_.MeasureTheory.Lp E p (μ.prod ν) where
  toLinearMap := uncurrySimpleLinear hp
  norm_map' := norm_uncurrySimpleLp hp

run_cmd do
  let target := ``Submission.MeasureTheory.uncurrySimpleIsometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.uncurrySimpleIsometry target :: scope.openDecls } }

variable [CompleteSpace E]

open _root_.MeasureTheory in
private def uncurryLinear (hp : p ≠ (⊤ : ℝ≥0∞)) :
    Lp (_root_.MeasureTheory.Lp E p ν) p μ →L[𝕜] _root_.MeasureTheory.Lp E p (μ.prod ν) :=
  (uncurrySimpleIsometry (𝕜 := 𝕜) hp).toContinuousLinearMap.extend
    (Lp.simpleFunc.coeToLp A (_root_.MeasureTheory.Lp E p ν) 𝕜)

run_cmd do
  let target := ``Submission.MeasureTheory.uncurryLinear
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.uncurryLinear target :: scope.openDecls } }

open _root_.MeasureTheory in
private theorem uncurryLinear_simple (hp : p ≠ (⊤ : ℝ≥0∞))
    (f : Lp.simpleFunc (_root_.MeasureTheory.Lp E p ν) p μ) :
    uncurryLinear (𝕜 := 𝕜) hp (f : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ) = uncurrySimpleLp hp f := by
  exact ContinuousLinearMap.extend_eq _ (Lp.simpleFunc.denseRange hp)
    Lp.simpleFunc.isUniformInducing f

run_cmd do
  let target := ``Submission.MeasureTheory.uncurryLinear_simple
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.uncurryLinear_simple target :: scope.openDecls } }

variable (𝕜) in
open _root_.MeasureTheory _root_.MeasureTheory.Lp in
def Lp.uncurry (hp : p ≠ (⊤ : ℝ≥0∞)) :
    _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ →ₗᵢ[𝕜] _root_.MeasureTheory.Lp E p (μ.prod ν) where
  toLinearMap := (uncurryLinear hp).toLinearMap
  norm_map' f := by
    change ‖uncurryLinear (𝕜 := 𝕜) hp f‖ = ‖f‖
    refine (Lp.simpleFunc.denseRange (E := _root_.MeasureTheory.Lp E p ν) (μ := μ) hp).induction_on
      (p := fun v => ‖uncurryLinear (𝕜 := 𝕜) hp v‖ = ‖v‖) f ?_ ?_
    · exact isClosed_eq (uncurryLinear (𝕜 := 𝕜) hp).continuous.norm continuous_norm
    · intro s
      change ‖uncurryLinear (𝕜 := 𝕜) hp (s : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ)‖ = _
      rw [uncurryLinear_simple hp]
      exact norm_uncurrySimpleLp hp s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.uncurry then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.uncurry"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.uncurry ``Submission.MeasureTheory.Lp.uncurry

open _root_.MeasureTheory in
private theorem uncurry_simple_coeFn (hp : p ≠ (⊤ : ℝ≥0∞))
    (f : Lp.simpleFunc (_root_.MeasureTheory.Lp E p ν) p μ) :
    ∀ᵐ a ∂μ, (fun b => Lp.uncurry 𝕜 hp (f : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ) (a, b)) =ᵐ[ν]
      ((f : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ) a : B → E) := by
  change ∀ᵐ a ∂μ, (fun b => uncurryLinear (𝕜 := 𝕜) hp
    (f : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ) (a, b)) =ᵐ[ν] _
  rw [uncurryLinear_simple hp]
  exact uncurrySimpleLp_coeFn hp f

run_cmd do
  let target := ``Submission.MeasureTheory.uncurry_simple_coeFn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.uncurry_simple_coeFn target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem Lp.uncurry_coeFn (hp : p ≠ (⊤ : ℝ≥0∞)) (f : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ) :
    ∀ᵐ a ∂μ, (fun b => Lp.uncurry 𝕜 hp f (a, b)) =ᵐ[ν] (f a : B → E) := by
  classical
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp
    ((Lp.simpleFunc.denseRange (E := _root_.MeasureTheory.Lp E p ν) (μ := μ) hp) f)
  choose s hs using hv
  have hslim : _root_.Filter.Tendsto (fun k => (s k : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ)) _root_.Filter.atTop (𝓝 f) := by
    simpa only [hs] using hvlim
  obtain ⟨σ, hσ, hσlim⟩ := (_root_.MeasureTheory.tendstoInMeasure_of_tendsto_Lp hslim).exists_seq_tendsto_ae
  have hprod : _root_.Filter.Tendsto (fun k => Lp.uncurry 𝕜 hp (s (σ k) : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ))
      atTop (𝓝 (Lp.uncurry 𝕜 hp f)) :=
    (Lp.uncurry 𝕜 hp).continuous.continuousAt.tendsto.comp (hslim.comp hσ.tendsto_atTop)
  obtain ⟨τ, hτ, hτlim⟩ := Lp.exists_subseq_tendsto_eLpNorm_prodMk_left hp hprod
  have hslice := (Lp.memLp (Lp.uncurry 𝕜 hp f)).prodMk_left hp
  have heqs := _root_.MeasureTheory.ae_all_iff.mpr (fun k => uncurry_simple_coeFn (𝕜 := 𝕜) hp (s k))
  filter_upwards [hσlim, hτlim, hslice, heqs] with a ha₁ ha₂ ha₃ ha₄
  let w : _root_.MeasureTheory.Lp E p ν := ha₃.toLp (fun b => Lp.uncurry 𝕜 hp f (a, b))
  have hlim₁ : _root_.Filter.Tendsto (fun k => (s (σ (τ k)) : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ) a) _root_.Filter.atTop (𝓝 (f a)) :=
    ha₁.comp hτ.tendsto_atTop
  have hlim₂ : _root_.Filter.Tendsto (fun k => (s (σ (τ k)) : _root_.MeasureTheory.Lp (_root_.MeasureTheory.Lp E p ν) p μ) a) _root_.Filter.atTop (𝓝 w) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ w).mpr
    apply ha₂.congr'
    filter_upwards [] with k
    apply _root_.MeasureTheory.eLpNorm_congr_ae
    filter_upwards [ha₄ (σ (τ k)), MemLp.coeFn_toLp ha₃] with b hb₁ hb₂
    simp only [Pi.sub_apply, hb₁, w, hb₂]
  have heq : f a = w := tendsto_nhds_unique hlim₁ hlim₂
  rw [heq]
  exact (MemLp.coeFn_toLp ha₃).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.uncurry_coeFn then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.uncurry_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.uncurry_coeFn ``Submission.MeasureTheory.Lp.uncurry_coeFn

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem Lp.uncurry_compLpL_coeFn {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (hp : p ≠ ⊤) (L : F →L[𝕜] _root_.MeasureTheory.Lp E p ν) (f : _root_.MeasureTheory.Lp F p μ) :
    ∀ᵐ a ∂μ, (fun b => Lp.uncurry (μ := μ) (ν := ν) (E := E) 𝕜 hp (L.compLpL p μ f) (a, b)) =ᵐ[ν] (L (f a) : B → E) := by
  filter_upwards [Lp.uncurry_coeFn (μ := μ) (ν := ν) (E := E) (𝕜 := 𝕜) hp (L.compLpL p μ f), L.coeFn_compLpL f]
    with a ha₁ ha₂
  rw [ha₂] at ha₁
  exact ha₁

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.uncurry_compLpL_coeFn then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.uncurry_compLpL_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.uncurry_compLpL_coeFn ``Submission.MeasureTheory.Lp.uncurry_compLpL_coeFn

end MeasureTheory
