import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.MeasureTheory _root_.Filter _root_.Set
open scoped _root_.ENNReal

namespace MeasureTheory
open _root_.MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem Lp.integral_add_apply
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L₁ L₂ : _root_.MeasureTheory.Lp (X →L[ℝ] Y) 2 μ) (u : _root_.MeasureTheory.Lp X 2 μ) :
    (∫ t, (L₁ + L₂) t (u t) ∂μ) =
      (∫ t, L₁ t (u t) ∂μ) + ∫ t, L₂ t (u t) ∂μ := by
  have hint (L : _root_.MeasureTheory.Lp (X →L[ℝ] Y) 2 μ) : _root_.MeasureTheory.Integrable (fun t => L t (u t)) μ := by
    apply ((Lp.memLp L).norm.integrable_mul (Lp.memLp u).norm).mono'
    · exact (ContinuousLinearMap.apply ℝ Y).aestronglyMeasurable_comp₂
        (Lp.aestronglyMeasurable u) (Lp.aestronglyMeasurable L)
    · exact Eventually.of_forall fun t => (L t).le_opNorm (u t)
  rw [← _root_.MeasureTheory.integral_add (hint L₁) (hint L₂)]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [Lp.coeFn_add L₁ L₂] with t ht
  exact congrArg (fun L : X →L[ℝ] Y => L (u t)) ht

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MeasureTheory.Lp
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.integral_add_apply then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.integral_add_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.integral_add_apply ``Submission.MeasureTheory.Lp.integral_add_apply

open _root_.MeasureTheory in
theorem continuous_integral_weight_mul_lp (c : α → ℝ) (hc : _root_.MeasureTheory.MemLp c ∞ μ)
    (f : _root_.MeasureTheory.Lp ℝ 2 μ) :
    Continuous (fun g : _root_.MeasureTheory.Lp ℝ 2 μ => ∫ z, f z * c z * g z ∂μ) := by
  have hfc : _root_.MeasureTheory.MemLp (fun z => f z * c z) 2 μ := by
    simpa only [mul_comm] using (Lp.memLp f).mul' hc
  let fc : _root_.MeasureTheory.Lp ℝ 2 μ := hfc.toLp (fun z => f z * c z)
  have heq : (fun g : _root_.MeasureTheory.Lp ℝ 2 μ => ∫ z, f z * c z * g z ∂μ) =
      (fun g : _root_.MeasureTheory.Lp ℝ 2 μ => _root_.Inner.inner ℝ fc g) := by
    funext g
    rw [L2.inner_def]
    refine _root_.MeasureTheory.integral_congr_ae ?_
    filter_upwards [hfc.coeFn_toLp] with z hz
    simp only [Real.inner_apply, fc, hz]
  rw [heq]
  exact continuous_const.inner continuous_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.continuous_integral_weight_mul_lp then
    throwError "Refusing to shadow existing declaration MeasureTheory.continuous_integral_weight_mul_lp"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.continuous_integral_weight_mul_lp ``Submission.MeasureTheory.continuous_integral_weight_mul_lp

open _root_.MeasureTheory in
theorem integrable_weight_mul_lp (c : α → ℝ) (hc : _root_.MeasureTheory.MemLp c ∞ μ)
    (f g : _root_.MeasureTheory.Lp ℝ 2 μ) :
    Integrable (fun z => f z * c z * g z) μ := by
  have hfc : _root_.MeasureTheory.MemLp (fun z => f z * c z) 2 μ := by
    simpa only [mul_comm] using (Lp.memLp f).mul' hc
  exact hfc.integrable_mul (Lp.memLp g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integrable_weight_mul_lp then
    throwError "Refusing to shadow existing declaration MeasureTheory.integrable_weight_mul_lp"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integrable_weight_mul_lp ``Submission.MeasureTheory.integrable_weight_mul_lp

open _root_.MeasureTheory in
private theorem integral_indicatorConstLp_mul
    {A : Type*} [MeasurableSpace A] {μ : _root_.MeasureTheory.Measure A} {s : Set A}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (f : A → ℝ) :
    (∫ t, _root_.MeasureTheory.indicatorConstLp 2 hs hμs (1 : ℝ) t * f t ∂μ) = ∫ t in s, f t ∂μ := by
  rw [← _root_.MeasureTheory.integral_indicator hs]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [_root_.MeasureTheory.indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1 : ℝ))] with t ht
  rw [ht]
  by_cases hts : t ∈ s <;> simp [hts]

run_cmd do
  let target := ``Submission.MeasureTheory.integral_indicatorConstLp_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.integral_indicatorConstLp_mul target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Lp in
theorem Lp.eq_of_integral_mul_dual_eq
    {A X : Type*} [MeasurableSpace A] {μ : _root_.MeasureTheory.Measure A}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L₁ L₂ : _root_.MeasureTheory.Lp (X →L[ℝ] ℝ) 2 μ)
    (h : ∀ (τ : _root_.MeasureTheory.Lp ℝ 2 μ) (x : X),
      (∫ t, τ t * L₁ t x ∂μ) = ∫ t, τ t * L₂ t x ∂μ) : L₁ = L₂ := by
  have hint (L : _root_.MeasureTheory.Lp (X →L[ℝ] ℝ) 2 μ) (s : Set A) (hs : MeasurableSet s) (hμs : μ s < ∞) :
      IntegrableOn (fun t => L t) s μ := by
    let : _root_.MeasureTheory.IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hμs⟩
    exact ((Lp.memLp L).restrict s).integrable (by norm_num)
  apply Lp.ext
  apply Lp.ae_eq_of_forall_setIntegral_eq L₁ L₂ (by norm_num) (by norm_num)
    (hint L₁) (hint L₂)
  intro s hs hμs
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.integral_apply (hint L₁ s hs hμs),
    ContinuousLinearMap.integral_apply (hint L₂ s hs hμs)]
  simpa only [integral_indicatorConstLp_mul hs hμs.ne] using
    h (_root_.MeasureTheory.indicatorConstLp 2 hs hμs.ne (1 : ℝ)) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Lp.eq_of_integral_mul_dual_eq then
    throwError "Refusing to shadow existing declaration MeasureTheory.Lp.eq_of_integral_mul_dual_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Lp.eq_of_integral_mul_dual_eq ``Submission.MeasureTheory.Lp.eq_of_integral_mul_dual_eq


end MeasureTheory
