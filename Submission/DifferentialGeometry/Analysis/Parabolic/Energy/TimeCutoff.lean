import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic.Energy

def timeCutoff (a b t : ℝ) : ℝ :=
  Real.smoothTransition ((t - a) / (b - a))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff

def timeCutoffDeriv (a b t : ℝ) : ℝ :=
  deriv Real.smoothTransition ((t - a) / (b - a)) / (b - a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDeriv ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDeriv

def backwardTimeCutoff (a b t : ℝ) : ℝ :=
  1 - timeCutoff a b t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff

def backwardTimeCutoffDeriv (a b t : ℝ) : ℝ :=
  -timeCutoffDeriv a b t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoffDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoffDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoffDeriv ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoffDeriv

theorem contDiff_timeCutoff (a b : ℝ) :
    ContDiff ℝ ∞ (timeCutoff a b) := by
  have haffine : ContDiff ℝ ∞ (fun t : ℝ => (t - a) / (b - a)) :=
    (contDiff_id.sub contDiff_const).div_const _
  exact (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp haffine

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.contDiff_timeCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.contDiff_timeCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.contDiff_timeCutoff ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.contDiff_timeCutoff

theorem contDiff_timeCutoffDeriv (a b : ℝ) :
    ContDiff ℝ ∞ (timeCutoffDeriv a b) := by
  have hsmooth : ContDiff ℝ ∞ (deriv Real.smoothTransition) := by
    exact (contDiff_infty_iff_deriv.mp
      (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞)))).2
  have haffine : ContDiff ℝ ∞ (fun t : ℝ => (t - a) / (b - a)) :=
    (contDiff_id.sub contDiff_const).div_const _
  simpa only [timeCutoffDeriv, Function.comp_apply] using!
    (hsmooth.comp haffine).div_const (b - a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.contDiff_timeCutoffDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.contDiff_timeCutoffDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.contDiff_timeCutoffDeriv ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.contDiff_timeCutoffDeriv

theorem hasDerivAt_timeCutoff (a b t : ℝ) :
    HasDerivAt (timeCutoff a b) (timeCutoffDeriv a b t) t := by
  have hinner : HasDerivAt (fun s : ℝ => (s - a) / (b - a))
      (1 / (b - a)) t := by
    simpa using ((hasDerivAt_id t).sub_const a).div_const (b - a)
  have houter : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((t - a) / (b - a)))
      ((t - a) / (b - a)) :=
    ((Real.smoothTransition.contDiff (n := (1 : ℕ∞))).differentiable
      (by norm_num) _).hasDerivAt
  simpa only [timeCutoff, timeCutoffDeriv, div_eq_mul_inv, one_mul] using!
    houter.comp t hinner

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.hasDerivAt_timeCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.hasDerivAt_timeCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.hasDerivAt_timeCutoff ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.hasDerivAt_timeCutoff

theorem contDiff_backwardTimeCutoff (a b : ℝ) :
    ContDiff ℝ ∞ (backwardTimeCutoff a b) :=
  contDiff_const.sub (contDiff_timeCutoff a b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.contDiff_backwardTimeCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.contDiff_backwardTimeCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.contDiff_backwardTimeCutoff ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.contDiff_backwardTimeCutoff

theorem contDiff_backwardTimeCutoffDeriv (a b : ℝ) :
    ContDiff ℝ ∞ (backwardTimeCutoffDeriv a b) :=
  (contDiff_timeCutoffDeriv a b).neg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.contDiff_backwardTimeCutoffDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.contDiff_backwardTimeCutoffDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.contDiff_backwardTimeCutoffDeriv ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.contDiff_backwardTimeCutoffDeriv

theorem hasDerivAt_backwardTimeCutoff (a b t : ℝ) :
    HasDerivAt (backwardTimeCutoff a b) (backwardTimeCutoffDeriv a b t) t := by
  simpa only [backwardTimeCutoff, backwardTimeCutoffDeriv, zero_sub] using!
    (hasDerivAt_const t 1).sub (hasDerivAt_timeCutoff a b t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.hasDerivAt_backwardTimeCutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.hasDerivAt_backwardTimeCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.hasDerivAt_backwardTimeCutoff ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.hasDerivAt_backwardTimeCutoff

theorem timeCutoff_mem_Icc (a b t : ℝ) :
    timeCutoff a b t ∈ _root_.Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_mem_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_mem_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_mem_Icc ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_mem_Icc

theorem backwardTimeCutoff_mem_Icc (a b t : ℝ) :
    backwardTimeCutoff a b t ∈ _root_.Set.Icc (0 : ℝ) 1 := by
  have h := timeCutoff_mem_Icc a b t
  change 0 ≤ 1 - timeCutoff a b t ∧ 1 - timeCutoff a b t ≤ 1
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_mem_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_mem_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_mem_Icc ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_mem_Icc

theorem timeCutoff_eq_zero_of_le {a b t : ℝ} (hab : a < b) (ht : t ≤ a) :
    timeCutoff a b t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hab.le)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_eq_zero_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_eq_zero_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_eq_zero_of_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_eq_zero_of_le

theorem timeCutoff_eq_zero (a : ℝ) {b : ℝ} (hab : a < b) :
    timeCutoff a b a = 0 :=
  timeCutoff_eq_zero_of_le hab le_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_eq_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_eq_zero

theorem timeCutoff_eq_one_of_le {a b t : ℝ} (hab : a < b) (ht : b ≤ t) :
    timeCutoff a b t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [one_le_div (sub_pos.mpr hab)]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_eq_one_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_eq_one_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_eq_one_of_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_eq_one_of_le

theorem backwardTimeCutoff_eq_one_of_le
    {a b t : ℝ} (hab : a < b) (ht : t ≤ a) :
    backwardTimeCutoff a b t = 1 := by
  rw [backwardTimeCutoff, timeCutoff_eq_zero_of_le hab ht, sub_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_eq_one_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_eq_one_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_eq_one_of_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_eq_one_of_le

theorem backwardTimeCutoff_eq_zero_of_le
    {a b t : ℝ} (hab : a < b) (ht : b ≤ t) :
    backwardTimeCutoff a b t = 0 := by
  rw [backwardTimeCutoff, timeCutoff_eq_one_of_le hab ht, sub_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_eq_zero_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_eq_zero_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_eq_zero_of_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_eq_zero_of_le

theorem backwardTimeCutoff_eq_zero (b : ℝ) {a : ℝ} (hab : a < b) :
    backwardTimeCutoff a b b = 0 :=
  backwardTimeCutoff_eq_zero_of_le hab le_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_eq_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_eq_zero

theorem timeCutoffDeriv_nonneg {a b : ℝ} (hab : a < b) (t : ℝ) :
    0 ≤ timeCutoffDeriv a b t := by
  exact div_nonneg Real.smoothTransition.monotone.deriv_nonneg (sub_pos.mpr hab).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDeriv_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDeriv_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDeriv_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDeriv_nonneg

theorem backwardTimeCutoffDeriv_nonpos {a b : ℝ} (hab : a < b) (t : ℝ) :
    backwardTimeCutoffDeriv a b t ≤ 0 := by
  exact neg_nonpos.mpr (timeCutoffDeriv_nonneg hab t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoffDeriv_nonpos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoffDeriv_nonpos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoffDeriv_nonpos ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoffDeriv_nonpos

theorem neg_backwardTimeCutoffDeriv_nonneg
    {a b : ℝ} (hab : a < b) (t : ℝ) :
    0 ≤ -backwardTimeCutoffDeriv a b t := by
  exact neg_nonneg.mpr (backwardTimeCutoffDeriv_nonpos hab t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.neg_backwardTimeCutoffDeriv_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.neg_backwardTimeCutoffDeriv_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.neg_backwardTimeCutoffDeriv_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.neg_backwardTimeCutoffDeriv_nonneg

private theorem exists_smoothTransition_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |deriv Real.smoothTransition s| ≤ C := by
  have hsmooth : ContDiff ℝ 1 Real.smoothTransition := by
    simpa using (Real.smoothTransition.contDiff (n := (1 : ℕ∞)))
  have hcont : Continuous (deriv Real.smoothTransition) :=
    hsmooth.continuous_deriv_one
  obtain ⟨sMax, -, hsMax⟩ :=
    (_root_.CompactIccSpace.isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
      (Set.nonempty_Icc.2 (by norm_num)) hcont.norm.continuousOn
  refine ⟨|deriv Real.smoothTransition sMax|, abs_nonneg _, ?_⟩
  intro s
  by_cases hs0 : s < 0
  · have hloc : Real.smoothTransition =ᶠ[nhds s] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hs0] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [hloc.deriv_eq, deriv_const, abs_zero]
    exact abs_nonneg _
  · by_cases hs1 : 1 < s
    · have hloc : Real.smoothTransition =ᶠ[nhds s] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hs1] with y hy
        exact Real.smoothTransition.one_of_one_le hy.le
      rw [hloc.deriv_eq, deriv_const, abs_zero]
      exact abs_nonneg _
    · push Not at hs0 hs1
      simpa [Real.norm_eq_abs] using
        (Filter.eventually_principal.mp hsMax s (Set.mem_Icc.2 ⟨hs0, hs1⟩))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.exists_smoothTransition_deriv_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Energy.exists_smoothTransition_deriv_bound target :: scope.openDecls } }

theorem exists_timeCutoffDeriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b : ℝ}, a < b → ∀ t : ℝ,
      timeCutoffDeriv a b t ≤ C / (b - a) := by
  obtain ⟨C, hC, hbound⟩ := exists_smoothTransition_deriv_bound
  refine ⟨C, hC, ?_⟩
  intro a b hab t
  have hderiv : deriv Real.smoothTransition ((t - a) / (b - a)) ≤ C :=
    le_trans (le_abs_self _) (hbound _)
  exact div_le_div_of_nonneg_right hderiv (sub_pos.mpr hab).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.exists_timeCutoffDeriv_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.exists_timeCutoffDeriv_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.exists_timeCutoffDeriv_bound ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.exists_timeCutoffDeriv_bound

def timeCutoffDerivConstant : ℝ :=
  Classical.choose exists_timeCutoffDeriv_bound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDerivConstant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDerivConstant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDerivConstant ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDerivConstant

theorem timeCutoffDerivConstant_nonneg :
    0 ≤ timeCutoffDerivConstant :=
  (Classical.choose_spec exists_timeCutoffDeriv_bound).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDerivConstant_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDerivConstant_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDerivConstant_nonneg ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDerivConstant_nonneg

theorem timeCutoffDeriv_le
    {a b : ℝ} (hab : a < b) (t : ℝ) :
    timeCutoffDeriv a b t ≤ timeCutoffDerivConstant / (b - a) :=
  (Classical.choose_spec exists_timeCutoffDeriv_bound).2 hab t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDeriv_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDeriv_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDeriv_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoffDeriv_le

theorem neg_backwardTimeCutoffDeriv_le
    {a b : ℝ} (hab : a < b) (t : ℝ) :
    -backwardTimeCutoffDeriv a b t ≤ timeCutoffDerivConstant / (b - a) := by
  simpa only [backwardTimeCutoffDeriv, neg_neg] using timeCutoffDeriv_le hab t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.neg_backwardTimeCutoffDeriv_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.neg_backwardTimeCutoffDeriv_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.neg_backwardTimeCutoffDeriv_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.neg_backwardTimeCutoffDeriv_le

theorem timeCutoff_mass_error_intervalIntegral_le
    {mass error outerMass : ℝ → ℝ}
    {a t₀ t t₁ D K L : ℝ}
    (hat₀ : a < t₀) (ht₀t : t₀ ≤ t) (htt₁ : t ≤ t₁)
    (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hmass : ContinuousOn mass (_root_.Set.Icc a t₁))
    (herror : ContinuousOn error (_root_.Set.Icc a t₁))
    (houterMass : ContinuousOn outerMass (_root_.Set.Icc a t₁))
    (hmass_nonneg : ∀ s ∈ _root_.Set.Icc a t₁, 0 ≤ mass s)
    (herror_nonneg : ∀ s ∈ _root_.Set.Icc a t₁, 0 ≤ error s)
    (houterMass_nonneg : ∀ s ∈ _root_.Set.Icc a t₁, 0 ≤ outerMass s)
    (hmass_le : ∀ s ∈ _root_.Set.Icc a t₁, mass s ≤ outerMass s)
    (herror_le : ∀ s ∈ _root_.Set.Icc a t₁, error s ≤ K * outerMass s)
    (hderiv_le : ∀ s ∈ _root_.Set.Icc a t₁, timeCutoffDeriv a t₀ s ≤ D)
    (houterMass_le : (∫ s in a..t₁, outerMass s) ≤ L) :
    (∫ s in a..t,
      timeCutoffDeriv a t₀ s * mass s +
        timeCutoff a t₀ s * (4 * error s)) ≤
      (D + 4 * K) * L := by
  have hat : a ≤ t := hat₀.le.trans ht₀t
  have hat₁ : a ≤ t₁ := hat.trans htt₁
  let lhs : ℝ → ℝ := fun s =>
    timeCutoffDeriv a t₀ s * mass s + timeCutoff a t₀ s * (4 * error s)
  let rhs : ℝ → ℝ := fun s => (D + 4 * K) * outerMass s
  have hlhs_cont : ContinuousOn lhs (_root_.Set.Icc a t) := by
    have hsubset : _root_.Set.Icc a t ⊆ _root_.Set.Icc a t₁ := fun s hs => ⟨hs.1, hs.2.trans htt₁⟩
    exact ((contDiff_timeCutoffDeriv a t₀).continuous.continuousOn.mul
      (hmass.mono hsubset)).add
        ((contDiff_timeCutoff a t₀).continuous.continuousOn.mul
          (continuousOn_const.mul (herror.mono hsubset)))
  have hrhs_cont : ContinuousOn rhs (_root_.Set.Icc a t) := by
    exact continuousOn_const.mul
      (houterMass.mono (fun s hs => ⟨hs.1, hs.2.trans htt₁⟩))
  have hlhs_int : IntervalIntegrable lhs _root_.MeasureTheory.MeasureSpace.volume a t := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le hat] using hlhs_cont
  have hrhs_int : IntervalIntegrable rhs _root_.MeasureTheory.MeasureSpace.volume a t := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le hat] using hrhs_cont
  have hpoint : ∀ s ∈ _root_.Set.Icc a t, lhs s ≤ rhs s := by
    intro s hs
    have hs' : s ∈ _root_.Set.Icc a t₁ := ⟨hs.1, hs.2.trans htt₁⟩
    have htime := timeCutoff_mem_Icc a t₀ s
    have htime_term :
        timeCutoffDeriv a t₀ s * mass s ≤ D * outerMass s := by
      calc
        timeCutoffDeriv a t₀ s * mass s ≤ D * mass s :=
          mul_le_mul_of_nonneg_right (hderiv_le s hs') (hmass_nonneg s hs')
        _ ≤ D * outerMass s := mul_le_mul_of_nonneg_left (hmass_le s hs') hD
    have herror_term :
        timeCutoff a t₀ s * (4 * error s) ≤ 4 * K * outerMass s := by
      calc
        timeCutoff a t₀ s * (4 * error s) ≤ 1 * (4 * error s) :=
          mul_le_mul_of_nonneg_right htime.2
            (mul_nonneg (by norm_num) (herror_nonneg s hs'))
        _ = 4 * error s := one_mul _
        _ ≤ 4 * (K * outerMass s) :=
          mul_le_mul_of_nonneg_left (herror_le s hs') (by norm_num)
        _ = 4 * K * outerMass s := by ring
    dsimp only [lhs, rhs]
    linarith
  have hmono : (∫ s in a..t, lhs s) ≤ ∫ s in a..t, rhs s :=
    intervalIntegral.integral_mono_on hat hlhs_int hrhs_int hpoint
  have houter_int : IntervalIntegrable outerMass _root_.MeasureTheory.MeasureSpace.volume a t₁ := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le hat₁] using houterMass
  have houter_mono : (∫ s in a..t, outerMass s) ≤ ∫ s in a..t₁, outerMass s := by
    exact intervalIntegral.integral_mono_interval le_rfl hat htt₁
      (by
        filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
        exact houterMass_nonneg s ⟨hs.1.le, hs.2⟩)
      houter_int
  have hcoefficient : 0 ≤ D + 4 * K := add_nonneg hD (mul_nonneg (by norm_num) hK)
  calc
    (∫ s in a..t, timeCutoffDeriv a t₀ s * mass s +
        timeCutoff a t₀ s * (4 * error s)) = ∫ s in a..t, lhs s := rfl
    _ ≤ ∫ s in a..t, rhs s := hmono
    _ = (D + 4 * K) * ∫ s in a..t, outerMass s := by
      simp only [rhs, intervalIntegral.integral_const_mul]
    _ ≤ (D + 4 * K) * ∫ s in a..t₁, outerMass s :=
      mul_le_mul_of_nonneg_left houter_mono hcoefficient
    _ ≤ (D + 4 * K) * L :=
      mul_le_mul_of_nonneg_left houterMass_le hcoefficient

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_mass_error_intervalIntegral_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_mass_error_intervalIntegral_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_mass_error_intervalIntegral_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.timeCutoff_mass_error_intervalIntegral_le

theorem backwardTimeCutoff_mass_error_intervalIntegral_le
    {mass error outerMass : ℝ → ℝ}
    {a t t₁ b C D K L : ℝ}
    (hat : a ≤ t) (htt₁ : t ≤ t₁) (ht₁b : t₁ < b)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hmass : ContinuousOn mass (_root_.Set.Icc a b))
    (herror : ContinuousOn error (_root_.Set.Icc a b))
    (houterMass : ContinuousOn outerMass (_root_.Set.Icc a b))
    (hmass_nonneg : ∀ s ∈ _root_.Set.Icc a b, 0 ≤ mass s)
    (herror_nonneg : ∀ s ∈ _root_.Set.Icc a b, 0 ≤ error s)
    (houterMass_nonneg : ∀ s ∈ _root_.Set.Icc a b, 0 ≤ outerMass s)
    (hmass_le : ∀ s ∈ _root_.Set.Icc a b, mass s ≤ outerMass s)
    (herror_le : ∀ s ∈ _root_.Set.Icc a b, error s ≤ K * outerMass s)
    (hderiv_le : ∀ s ∈ _root_.Set.Icc a b, -backwardTimeCutoffDeriv t₁ b s ≤ D)
    (houterMass_le : (∫ s in a..b, outerMass s) ≤ L) :
    (∫ s in t..b,
      (-backwardTimeCutoffDeriv t₁ b s) * mass s +
        backwardTimeCutoff t₁ b s * (C * error s)) ≤
      (D + C * K) * L := by
  have htb : t ≤ b := htt₁.trans ht₁b.le
  let lhs : ℝ → ℝ := fun s =>
    (-backwardTimeCutoffDeriv t₁ b s) * mass s +
      backwardTimeCutoff t₁ b s * (C * error s)
  let rhs : ℝ → ℝ := fun s => (D + C * K) * outerMass s
  have hsubset : _root_.Set.Icc t b ⊆ _root_.Set.Icc a b := fun s hs => ⟨hat.trans hs.1, hs.2⟩
  have hlhs_cont : ContinuousOn lhs (_root_.Set.Icc t b) := by
    exact ((contDiff_backwardTimeCutoffDeriv t₁ b).neg.continuous.continuousOn.mul
      (hmass.mono hsubset)).add
        ((contDiff_backwardTimeCutoff t₁ b).continuous.continuousOn.mul
          (continuousOn_const.mul (herror.mono hsubset)))
  have hrhs_cont : ContinuousOn rhs (_root_.Set.Icc t b) :=
    continuousOn_const.mul (houterMass.mono hsubset)
  have hlhs_int : IntervalIntegrable lhs _root_.MeasureTheory.MeasureSpace.volume t b := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le htb] using hlhs_cont
  have hrhs_int : IntervalIntegrable rhs _root_.MeasureTheory.MeasureSpace.volume t b := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le htb] using hrhs_cont
  have hpoint : ∀ s ∈ _root_.Set.Icc t b, lhs s ≤ rhs s := by
    intro s hs
    have hs' := hsubset hs
    have htime := backwardTimeCutoff_mem_Icc t₁ b s
    have htime_term :
        (-backwardTimeCutoffDeriv t₁ b s) * mass s ≤ D * outerMass s := by
      calc
        _ ≤ D * mass s :=
          mul_le_mul_of_nonneg_right (hderiv_le s hs') (hmass_nonneg s hs')
        _ ≤ D * outerMass s :=
          mul_le_mul_of_nonneg_left (hmass_le s hs') hD
    have herror_term :
        backwardTimeCutoff t₁ b s * (C * error s) ≤
          C * K * outerMass s := by
      calc
        _ ≤ 1 * (C * error s) :=
          mul_le_mul_of_nonneg_right htime.2
            (mul_nonneg hC (herror_nonneg s hs'))
        _ = C * error s := one_mul _
        _ ≤ C * (K * outerMass s) :=
          mul_le_mul_of_nonneg_left (herror_le s hs') hC
        _ = C * K * outerMass s := by ring
    dsimp only [lhs, rhs]
    linarith
  have hmono : (∫ s in t..b, lhs s) ≤ ∫ s in t..b, rhs s :=
    intervalIntegral.integral_mono_on htb hlhs_int hrhs_int hpoint
  have houter_int : IntervalIntegrable outerMass _root_.MeasureTheory.MeasureSpace.volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le (hat.trans htb)] using houterMass
  have houter_mono : (∫ s in t..b, outerMass s) ≤ ∫ s in a..b, outerMass s := by
    exact intervalIntegral.integral_mono_interval hat htb le_rfl
      (by
        filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
        exact houterMass_nonneg s ⟨hs.1.le, hs.2⟩)
      houter_int
  have hcoefficient : 0 ≤ D + C * K :=
    add_nonneg hD (mul_nonneg hC hK)
  calc
    (∫ s in t..b,
      (-backwardTimeCutoffDeriv t₁ b s) * mass s +
        backwardTimeCutoff t₁ b s * (C * error s)) =
        ∫ s in t..b, lhs s := rfl
    _ ≤ ∫ s in t..b, rhs s := hmono
    _ = (D + C * K) * ∫ s in t..b, outerMass s := by
      simp only [rhs, intervalIntegral.integral_const_mul]
    _ ≤ (D + C * K) * ∫ s in a..b, outerMass s :=
      mul_le_mul_of_nonneg_left houter_mono hcoefficient
    _ ≤ (D + C * K) * L :=
      mul_le_mul_of_nonneg_left houterMass_le hcoefficient

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_mass_error_intervalIntegral_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_mass_error_intervalIntegral_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_mass_error_intervalIntegral_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.backwardTimeCutoff_mass_error_intervalIntegral_le

theorem weight_mul_sub_eq_intervalIntegral
    {weight dweight energy denergy : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (_root_.Set.Icc a b))
    (hweight : ∀ t ∈ _root_.Set.Icc a b, HasDerivAt weight (dweight t) t)
    (hdenergy : ContinuousOn denergy (_root_.Set.Icc a b))
    (henergy : ∀ t ∈ _root_.Set.Icc a b, HasDerivAt energy (denergy t) t) :
    weight b * energy b - weight a * energy a =
      ∫ t in a..b, dweight t * energy t + weight t * denergy t := by
  have hweight_cont : ContinuousOn weight (_root_.Set.Icc a b) :=
    fun t ht => (hweight t ht).continuousAt.continuousWithinAt
  have henergy_cont : ContinuousOn energy (_root_.Set.Icc a b) :=
    fun t ht => (henergy t ht).continuousAt.continuousWithinAt
  have hintegrand : ContinuousOn
      (fun t => dweight t * energy t + weight t * denergy t) (_root_.Set.Icc a b) :=
    (hdweight.mul henergy_cont).add (hweight_cont.mul hdenergy)
  have hintegrand_int : IntervalIntegrable
      (fun t => dweight t * energy t + weight t * denergy t) _root_.MeasureTheory.MeasureSpace.volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le hab] using hintegrand
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun t => weight t * energy t)
    (f' := fun t => dweight t * energy t + weight t * denergy t)
    hab (hweight_cont.mul henergy_cont)
    (fun t ht => (hweight t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).mul
      (henergy t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)) hintegrand_int

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.weight_mul_sub_eq_intervalIntegral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.weight_mul_sub_eq_intervalIntegral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.weight_mul_sub_eq_intervalIntegral ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.weight_mul_sub_eq_intervalIntegral

theorem weight_mul_energy_inequality
    {weight dweight energy denergy dissipation source : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (_root_.Set.Icc a b))
    (hweight : ∀ t ∈ _root_.Set.Icc a b, HasDerivAt weight (dweight t) t)
    (hdenergy : ContinuousOn denergy (_root_.Set.Icc a b))
    (henergyDeriv : ∀ t ∈ _root_.Set.Icc a b, HasDerivAt energy (denergy t) t)
    (hdissipation : ContinuousOn dissipation (_root_.Set.Icc a b))
    (hsource : ContinuousOn source (_root_.Set.Icc a b))
    (henergy : ∀ t ∈ _root_.Set.Icc a b,
      dweight t * energy t + weight t * denergy t + dissipation t ≤ source t) :
    weight b * energy b - weight a * energy a +
        ∫ t in a..b, dissipation t ≤ ∫ t in a..b, source t := by
  have hidentity := weight_mul_sub_eq_intervalIntegral
    hab hdweight hweight hdenergy henergyDeriv
  have hweight_cont : ContinuousOn weight (_root_.Set.Icc a b) :=
    fun t ht => (hweight t ht).continuousAt.continuousWithinAt
  have henergy_cont : ContinuousOn energy (_root_.Set.Icc a b) :=
    fun t ht => (henergyDeriv t ht).continuousAt.continuousWithinAt
  have hderivative : ContinuousOn
      (fun t => dweight t * energy t + weight t * denergy t) (_root_.Set.Icc a b) :=
    (hdweight.mul henergy_cont).add (hweight_cont.mul hdenergy)
  have hleft_int : IntervalIntegrable
      (fun t => dweight t * energy t + weight t * denergy t) _root_.MeasureTheory.MeasureSpace.volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le hab] using hderivative
  have hdiss_int : IntervalIntegrable dissipation _root_.MeasureTheory.MeasureSpace.volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le hab] using hdissipation
  have hsource_int : IntervalIntegrable source _root_.MeasureTheory.MeasureSpace.volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le hab] using hsource
  have hmono :
      (∫ t in a..b,
        (dweight t * energy t + weight t * denergy t) + dissipation t) ≤
          ∫ t in a..b, source t :=
    intervalIntegral.integral_mono_on hab (hleft_int.add hdiss_int) hsource_int henergy
  rw [intervalIntegral.integral_add hleft_int hdiss_int, ← hidentity] at hmono
  exact hmono

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.weight_mul_energy_inequality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.weight_mul_energy_inequality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.weight_mul_energy_inequality ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.weight_mul_energy_inequality

theorem intervalIntegral_le_const_mul_sup_rpow
    {lhs mass energy : ℝ → ℝ} {C S theta a b : ℝ}
    (hab : a ≤ b)
    (hlhs : ContinuousOn lhs (_root_.Set.Icc a b))
    (henergy : ContinuousOn energy (_root_.Set.Icc a b))
    (hC : 0 ≤ C) (htheta : 0 ≤ theta)
    (hmass_nonneg : ∀ t ∈ _root_.Set.Icc a b, 0 ≤ mass t)
    (hmass_le : ∀ t ∈ _root_.Set.Icc a b, mass t ≤ S)
    (henergy_nonneg : ∀ t ∈ _root_.Set.Icc a b, 0 ≤ energy t)
    (hpoint : ∀ t ∈ _root_.Set.Icc a b,
      lhs t ≤ C * mass t ^ theta * energy t) :
    ∫ t in a..b, lhs t ≤
      C * S ^ theta * ∫ t in a..b, energy t := by
  have hlhs_int : IntervalIntegrable lhs _root_.MeasureTheory.MeasureSpace.volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le hab] using hlhs
  have hright_cont : ContinuousOn
      (fun t => (C * S ^ theta) * energy t) (_root_.Set.Icc a b) :=
    continuousOn_const.mul henergy
  have hright_int : IntervalIntegrable
      (fun t => (C * S ^ theta) * energy t) _root_.MeasureTheory.MeasureSpace.volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le hab] using hright_cont
  have hmono : ∀ t ∈ _root_.Set.Icc a b,
      lhs t ≤ (C * S ^ theta) * energy t := by
    intro t ht
    refine (hpoint t ht).trans ?_
    have hrpow : mass t ^ theta ≤ S ^ theta :=
      Real.rpow_le_rpow (hmass_nonneg t ht) (hmass_le t ht) htheta
    calc
      C * mass t ^ theta * energy t ≤
          C * S ^ theta * energy t :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrpow hC) (henergy_nonneg t ht)
      _ = (C * S ^ theta) * energy t := rfl
  have hint := intervalIntegral.integral_mono_on hab hlhs_int hright_int hmono
  simpa only [intervalIntegral.integral_const_mul] using hint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.intervalIntegral_le_const_mul_sup_rpow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.intervalIntegral_le_const_mul_sup_rpow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.intervalIntegral_le_const_mul_sup_rpow ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.intervalIntegral_le_const_mul_sup_rpow

theorem inner_mass_and_dissipation_le
    {weight mass dissipation source : ℝ → ℝ}
    {a t₀ t₁ A : ℝ}
    (hat₀ : a ≤ t₀) (ht₀t₁ : t₀ ≤ t₁)
    (hweight : ContinuousOn weight (_root_.Set.Icc a t₁))
    (hdissipation : ContinuousOn dissipation (_root_.Set.Icc a t₁))
    (hweight_nonneg : ∀ t ∈ _root_.Set.Icc a t₁, 0 ≤ weight t)
    (hdissipation_nonneg : ∀ t ∈ _root_.Set.Icc a t₁, 0 ≤ dissipation t)
    (hweight_a : weight a = 0)
    (hweight_inner : ∀ t ∈ _root_.Set.Icc t₀ t₁, weight t = 1)
    (hmass_nonneg : ∀ t ∈ _root_.Set.Icc t₀ t₁, 0 ≤ mass t)
    (hsource_le : ∀ t ∈ _root_.Set.Icc t₀ t₁, ∫ s in a..t, source s ≤ A)
    (hweighted : ∀ t ∈ _root_.Set.Icc t₀ t₁,
      weight t * mass t - weight a * mass a +
          ∫ s in a..t, weight s * dissipation s ≤
        ∫ s in a..t, source s) :
    (∀ t ∈ _root_.Set.Icc t₀ t₁, mass t ≤ A) ∧
      (∫ t in t₀..t₁, dissipation t) ≤ A := by
  have hat₁ : a ≤ t₁ := hat₀.trans ht₀t₁
  have hweighted_cont : ContinuousOn
      (fun t => weight t * dissipation t) (_root_.Set.Icc a t₁) :=
    hweight.mul hdissipation
  have hmass_le : ∀ t ∈ _root_.Set.Icc t₀ t₁, mass t ≤ A := by
    intro t ht
    have hat : a ≤ t := hat₀.trans ht.1
    have hinterval_nonneg : 0 ≤ ∫ s in a..t, weight s * dissipation s :=
      intervalIntegral.integral_nonneg hat (fun s hs =>
        mul_nonneg
          (hweight_nonneg s ⟨hs.1, hs.2.trans ht.2⟩)
          (hdissipation_nonneg s ⟨hs.1, hs.2.trans ht.2⟩))
    have h := (hweighted t ht).trans (hsource_le t ht)
    rw [hweight_inner t ht, hweight_a] at h
    simpa only [one_mul, _root_.MulZeroClass.zero_mul, zero_add] using h.trans' (by linarith)
  refine ⟨hmass_le, ?_⟩
  have hleft_cont : ContinuousOn
      (fun t => weight t * dissipation t) (_root_.Set.Icc a t₀) :=
    hweighted_cont.mono (fun t ht => ⟨ht.1, ht.2.trans ht₀t₁⟩)
  have hinner_cont : ContinuousOn
      (fun t => weight t * dissipation t) (_root_.Set.Icc t₀ t₁) :=
    hweighted_cont.mono (fun t ht => ⟨hat₀.trans ht.1, ht.2⟩)
  have hleft_int : IntervalIntegrable
      (fun t => weight t * dissipation t) _root_.MeasureTheory.MeasureSpace.volume a t₀ := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le hat₀] using hleft_cont
  have hinner_int : IntervalIntegrable
      (fun t => weight t * dissipation t) _root_.MeasureTheory.MeasureSpace.volume t₀ t₁ := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le ht₀t₁] using hinner_cont
  have hleft_nonneg : 0 ≤ ∫ t in a..t₀, weight t * dissipation t :=
    intervalIntegral.integral_nonneg hat₀ (fun t ht =>
      mul_nonneg
        (hweight_nonneg t ⟨ht.1, ht.2.trans ht₀t₁⟩)
        (hdissipation_nonneg t ⟨ht.1, ht.2.trans ht₀t₁⟩))
  have hinner_eq :
      (∫ t in t₀..t₁, weight t * dissipation t) =
        ∫ t in t₀..t₁, dissipation t := by
    apply intervalIntegral.integral_congr
    intro t ht
    change weight t * dissipation t = dissipation t
    rw [hweight_inner t (by simpa [_root_.Set.uIcc_of_le ht₀t₁] using ht), one_mul]
  have htotal := (hweighted t₁ ⟨ht₀t₁, le_rfl⟩).trans
    (hsource_le t₁ ⟨ht₀t₁, le_rfl⟩)
  rw [hweight_inner t₁ ⟨ht₀t₁, le_rfl⟩, hweight_a] at htotal
  simp only [one_mul, _root_.MulZeroClass.zero_mul, sub_zero] at htotal
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft_int hinner_int,
    hinner_eq] at htotal
  linarith [hmass_nonneg t₁ ⟨ht₀t₁, le_rfl⟩]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.inner_mass_and_dissipation_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.inner_mass_and_dissipation_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.inner_mass_and_dissipation_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.inner_mass_and_dissipation_le

theorem backward_inner_mass_and_dissipation_le
    {weight mass dissipation source : ℝ → ℝ}
    {a t₁ b A : ℝ}
    (hat₁ : a ≤ t₁) (ht₁b : t₁ ≤ b)
    (hweight : ContinuousOn weight (_root_.Set.Icc a b))
    (hdissipation : ContinuousOn dissipation (_root_.Set.Icc a b))
    (hweight_nonneg : ∀ t ∈ _root_.Set.Icc a b, 0 ≤ weight t)
    (hdissipation_nonneg : ∀ t ∈ _root_.Set.Icc a b, 0 ≤ dissipation t)
    (hweight_b : weight b = 0)
    (hweight_inner : ∀ t ∈ _root_.Set.Icc a t₁, weight t = 1)
    (hmass_nonneg : ∀ t ∈ _root_.Set.Icc a t₁, 0 ≤ mass t)
    (hsource_le : ∀ t ∈ _root_.Set.Icc a t₁, ∫ s in t..b, source s ≤ A)
    (hweighted : ∀ t ∈ _root_.Set.Icc a t₁,
      weight t * mass t - weight b * mass b +
          ∫ s in t..b, weight s * dissipation s ≤
        ∫ s in t..b, source s) :
    (∀ t ∈ _root_.Set.Icc a t₁, mass t ≤ A) ∧
      (∫ t in a..t₁, dissipation t) ≤ A := by
  have hab : a ≤ b := hat₁.trans ht₁b
  have hweighted_cont : ContinuousOn
      (fun t => weight t * dissipation t) (_root_.Set.Icc a b) :=
    hweight.mul hdissipation
  have hmass_le : ∀ t ∈ _root_.Set.Icc a t₁, mass t ≤ A := by
    intro t ht
    have htb : t ≤ b := ht.2.trans ht₁b
    have hinterval_nonneg : 0 ≤ ∫ s in t..b, weight s * dissipation s :=
      intervalIntegral.integral_nonneg htb (fun s hs =>
        mul_nonneg
          (hweight_nonneg s ⟨ht.1.trans hs.1, hs.2⟩)
          (hdissipation_nonneg s ⟨ht.1.trans hs.1, hs.2⟩))
    have h := (hweighted t ht).trans (hsource_le t ht)
    rw [hweight_inner t ht, hweight_b] at h
    simp only [one_mul, _root_.MulZeroClass.zero_mul, sub_zero] at h
    linarith
  refine ⟨hmass_le, ?_⟩
  have hinner_cont : ContinuousOn
      (fun t => weight t * dissipation t) (_root_.Set.Icc a t₁) :=
    hweighted_cont.mono (fun t ht => ⟨ht.1, ht.2.trans ht₁b⟩)
  have hright_cont : ContinuousOn
      (fun t => weight t * dissipation t) (_root_.Set.Icc t₁ b) :=
    hweighted_cont.mono (fun t ht => ⟨hat₁.trans ht.1, ht.2⟩)
  have hinner_int : IntervalIntegrable
      (fun t => weight t * dissipation t) _root_.MeasureTheory.MeasureSpace.volume a t₁ := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le hat₁] using hinner_cont
  have hright_int : IntervalIntegrable
      (fun t => weight t * dissipation t) _root_.MeasureTheory.MeasureSpace.volume t₁ b := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le ht₁b] using hright_cont
  have hright_nonneg : 0 ≤ ∫ t in t₁..b, weight t * dissipation t :=
    intervalIntegral.integral_nonneg ht₁b (fun t ht =>
      mul_nonneg
        (hweight_nonneg t ⟨hat₁.trans ht.1, ht.2⟩)
        (hdissipation_nonneg t ⟨hat₁.trans ht.1, ht.2⟩))
  have hinner_eq :
      (∫ t in a..t₁, weight t * dissipation t) =
        ∫ t in a..t₁, dissipation t := by
    apply intervalIntegral.integral_congr
    intro t ht
    change weight t * dissipation t = dissipation t
    rw [hweight_inner t (by simpa [_root_.Set.uIcc_of_le hat₁] using ht), one_mul]
  have htotal := (hweighted a ⟨le_rfl, hat₁⟩).trans
    (hsource_le a ⟨le_rfl, hat₁⟩)
  rw [hweight_inner a ⟨le_rfl, hat₁⟩, hweight_b] at htotal
  simp only [one_mul, _root_.MulZeroClass.zero_mul, sub_zero] at htotal
  rw [← intervalIntegral.integral_add_adjacent_intervals hinner_int hright_int,
    hinner_eq] at htotal
  linarith [hmass_nonneg a ⟨le_rfl, hat₁⟩]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.backward_inner_mass_and_dissipation_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.backward_inner_mass_and_dissipation_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.backward_inner_mass_and_dissipation_le ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.backward_inner_mass_and_dissipation_le

theorem norm_sq_sub_eq_intervalIntegral_inner_deriv
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {u du : ℝ → X} {a b : ℝ}
    (hab : a ≤ b)
    (hdu : ContinuousOn du (_root_.Set.Icc a b))
    (hu : ∀ t ∈ _root_.Set.Icc a b, HasDerivAt u (du t) t) :
    ‖u b‖ ^ 2 - ‖u a‖ ^ 2 =
      ∫ t in a..b, 2 * _root_.Inner.inner ℝ (u t) (du t) := by
  have hu_cont : ContinuousOn u (_root_.Set.Icc a b) :=
    fun t ht => (hu t ht).continuousAt.continuousWithinAt
  have hintegrand : ContinuousOn (fun t => 2 * _root_.Inner.inner ℝ (u t) (du t)) (_root_.Set.Icc a b) :=
    continuousOn_const.mul (hu_cont.inner hdu)
  have hintegrand_int : IntervalIntegrable (fun t => 2 * _root_.Inner.inner ℝ (u t) (du t))
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le hab] using hintegrand
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun t => ‖u t‖ ^ 2) (f' := fun t => 2 * _root_.Inner.inner ℝ (u t) (du t)) hab
    (hu_cont.norm.pow 2)
    (fun t ht => (hu t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).norm_sq) hintegrand_int

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.norm_sq_sub_eq_intervalIntegral_inner_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.norm_sq_sub_eq_intervalIntegral_inner_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.norm_sq_sub_eq_intervalIntegral_inner_deriv ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.norm_sq_sub_eq_intervalIntegral_inner_deriv

theorem weight_mul_norm_sq_sub_eq_intervalIntegral
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {weight dweight : ℝ → ℝ} {u du : ℝ → X} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (_root_.Set.Icc a b))
    (hweight : ∀ t ∈ _root_.Set.Icc a b, HasDerivAt weight (dweight t) t)
    (hdu : ContinuousOn du (_root_.Set.Icc a b))
    (hu : ∀ t ∈ _root_.Set.Icc a b, HasDerivAt u (du t) t) :
    weight b * ‖u b‖ ^ 2 - weight a * ‖u a‖ ^ 2 =
      ∫ t in a..b,
        dweight t * ‖u t‖ ^ 2 + weight t * (2 * _root_.Inner.inner ℝ (u t) (du t)) := by
  have hweight_cont : ContinuousOn weight (_root_.Set.Icc a b) :=
    fun t ht => (hweight t ht).continuousAt.continuousWithinAt
  have hu_cont : ContinuousOn u (_root_.Set.Icc a b) :=
    fun t ht => (hu t ht).continuousAt.continuousWithinAt
  have hintegrand : ContinuousOn
      (fun t => dweight t * ‖u t‖ ^ 2 + weight t * (2 * _root_.Inner.inner ℝ (u t) (du t)))
      (_root_.Set.Icc a b) :=
    (hdweight.mul (hu_cont.norm.pow 2)).add
      (hweight_cont.mul (continuousOn_const.mul (hu_cont.inner hdu)))
  have hintegrand_int : IntervalIntegrable
      (fun t => dweight t * ‖u t‖ ^ 2 + weight t * (2 * _root_.Inner.inner ℝ (u t) (du t)))
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le hab] using hintegrand
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun t => weight t * ‖u t‖ ^ 2)
    (f' := fun t => dweight t * ‖u t‖ ^ 2 + weight t * (2 * _root_.Inner.inner ℝ (u t) (du t)))
    hab _ _ hintegrand_int
  · exact hweight_cont.mul (hu_cont.norm.pow 2)
  · intro t ht
    exact (hweight t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).mul
      ((hu t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).norm_sq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.weight_mul_norm_sq_sub_eq_intervalIntegral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.weight_mul_norm_sq_sub_eq_intervalIntegral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.weight_mul_norm_sq_sub_eq_intervalIntegral ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.weight_mul_norm_sq_sub_eq_intervalIntegral

theorem weight_mul_norm_sq_energy_inequality
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {weight dweight : ℝ → ℝ} {u du : ℝ → X}
    {dissipation source : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (_root_.Set.Icc a b))
    (hweight : ∀ t ∈ _root_.Set.Icc a b, HasDerivAt weight (dweight t) t)
    (hdu : ContinuousOn du (_root_.Set.Icc a b))
    (hu : ∀ t ∈ _root_.Set.Icc a b, HasDerivAt u (du t) t)
    (hdissipation : ContinuousOn dissipation (_root_.Set.Icc a b))
    (hsource : ContinuousOn source (_root_.Set.Icc a b))
    (henergy : ∀ t ∈ _root_.Set.Icc a b,
      dweight t * ‖u t‖ ^ 2 + weight t * (2 * _root_.Inner.inner ℝ (u t) (du t)) +
        dissipation t ≤ source t) :
    weight b * ‖u b‖ ^ 2 - weight a * ‖u a‖ ^ 2 +
        ∫ t in a..b, dissipation t ≤ ∫ t in a..b, source t := by
  have hidentity := weight_mul_norm_sq_sub_eq_intervalIntegral
    hab hdweight hweight hdu hu
  have hweight_cont : ContinuousOn weight (_root_.Set.Icc a b) :=
    fun t ht => (hweight t ht).continuousAt.continuousWithinAt
  have hu_cont : ContinuousOn u (_root_.Set.Icc a b) :=
    fun t ht => (hu t ht).continuousAt.continuousWithinAt
  have hderivative : ContinuousOn
      (fun t => dweight t * ‖u t‖ ^ 2 + weight t * (2 * _root_.Inner.inner ℝ (u t) (du t)))
      (_root_.Set.Icc a b) :=
    (hdweight.mul (hu_cont.norm.pow 2)).add
      (hweight_cont.mul (continuousOn_const.mul (hu_cont.inner hdu)))
  have hleft_int : IntervalIntegrable
      (fun t => dweight t * ‖u t‖ ^ 2 + weight t * (2 * _root_.Inner.inner ℝ (u t) (du t)))
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le hab] using hderivative
  have hdiss_int : IntervalIntegrable dissipation _root_.MeasureTheory.MeasureSpace.volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le hab] using hdissipation
  have hsource_int : IntervalIntegrable source _root_.MeasureTheory.MeasureSpace.volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [_root_.Set.uIcc_of_le hab] using hsource
  have hmono : (∫ t in a..b,
      (dweight t * ‖u t‖ ^ 2 + weight t * (2 * _root_.Inner.inner ℝ (u t) (du t))) +
        dissipation t) ≤ ∫ t in a..b, source t :=
    intervalIntegral.integral_mono_on hab (hleft_int.add hdiss_int) hsource_int henergy
  rw [intervalIntegral.integral_add hleft_int hdiss_int, ← hidentity] at hmono
  exact hmono

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.weight_mul_norm_sq_energy_inequality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.weight_mul_norm_sq_energy_inequality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.weight_mul_norm_sq_energy_inequality ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.weight_mul_norm_sq_energy_inequality


section

open scoped _root_.ENNReal _root_.NNReal

theorem exists_smooth_timeCutoff_eq_one_on_Icc {a b T : ℝ}
    (ha : 0 < a) (hb : b < T) :
    ∃ (ζ : ℝ → ℝ) (K : ℝ≥0),
      ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧
      (∀ t, 0 ≤ ζ t) ∧ (∀ t, ζ t ≤ 1) ∧ LipschitzWith K ζ ∧
      ζ 0 = 0 ∧ ζ T = 0 ∧ ∀ t ∈ _root_.Set.Icc a b, ζ t = 1 := by
  let ζ : ℝ → ℝ := fun t => timeCutoff 0 a t * backwardTimeCutoff b T t
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ :=
    (contDiff_timeCutoff 0 a).mul (contDiff_backwardTimeCutoff b T)
  have hζc : HasCompactSupport ζ := by
    refine HasCompactSupport.intro' (K := _root_.Set.Icc (0 : ℝ) T) _root_.CompactIccSpace.isCompact_Icc isClosed_Icc ?_
    intro t ht
    change timeCutoff 0 a t * backwardTimeCutoff b T t = 0
    by_cases ht0 : t < 0
    · rw [timeCutoff_eq_zero_of_le ha ht0.le, _root_.MulZeroClass.zero_mul]
    · have htT : T < t := by
        by_contra hn
        exact ht ⟨le_of_not_gt ht0, le_of_not_gt hn⟩
      rw [backwardTimeCutoff_eq_zero_of_le hb htT.le, _root_.MulZeroClass.mul_zero]
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hζc hζ (by simp)
  refine ⟨ζ, K, hζ, hζc, ?_, ?_, hK, ?_, ?_, ?_⟩
  · intro t
    exact mul_nonneg (timeCutoff_mem_Icc 0 a t).1 (backwardTimeCutoff_mem_Icc b T t).1
  · intro t
    exact mul_le_one₀ (timeCutoff_mem_Icc 0 a t).2
      (backwardTimeCutoff_mem_Icc b T t).1 (backwardTimeCutoff_mem_Icc b T t).2
  · change timeCutoff 0 a 0 * backwardTimeCutoff b T 0 = 0
    rw [timeCutoff_eq_zero 0 ha, _root_.MulZeroClass.zero_mul]
  · change timeCutoff 0 a T * backwardTimeCutoff b T T = 0
    rw [backwardTimeCutoff_eq_zero T hb, _root_.MulZeroClass.mul_zero]
  · intro t ht
    change timeCutoff 0 a t * backwardTimeCutoff b T t = 1
    rw [timeCutoff_eq_one_of_le ha ht.1, backwardTimeCutoff_eq_one_of_le hb ht.2, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.exists_smooth_timeCutoff_eq_one_on_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.exists_smooth_timeCutoff_eq_one_on_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.exists_smooth_timeCutoff_eq_one_on_Icc ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.exists_smooth_timeCutoff_eq_one_on_Icc

theorem integral_Icc_le_integral_mul_cutoff {a b : ℝ} {μ : _root_.MeasureTheory.Measure ℝ}
    {E ζ : ℝ → ℝ} (hE : _root_.MeasureTheory.Integrable E μ) (hEpos : ∀ t, 0 ≤ E t)
    (hζ : _root_.MeasureTheory.MemLp ζ ∞ μ) (hζpos : ∀ t, 0 ≤ ζ t)
    (hζone : ∀ t ∈ _root_.Set.Icc a b, ζ t = 1) :
    (∫ t in _root_.Set.Icc a b, E t ∂μ) ≤ ∫ t, ζ t * E t ∂μ := by
  have hI : _root_.MeasureTheory.Integrable (fun t => ζ t * E t) μ :=
    (hE.mul_of_top_right hζ).congr (Filter.Eventually.of_forall fun _ => rfl)
  calc
    _ = ∫ t in _root_.Set.Icc a b, ζ t * E t ∂μ := by
      apply _root_.MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro t ht
      change E t = ζ t * E t
      rw [hζone t ht, one_mul]
    _ ≤ _ := _root_.MeasureTheory.setIntegral_le_integral hI
      (Filter.Eventually.of_forall fun t => mul_nonneg (hζpos t) (hEpos t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Energy.integral_Icc_le_integral_mul_cutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Energy.integral_Icc_le_integral_mul_cutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Energy.integral_Icc_le_integral_mul_cutoff ``Submission.DifferentialGeometry.Analysis.Parabolic.Energy.integral_Icc_le_integral_mul_cutoff

end

end DifferentialGeometry.Analysis.Parabolic.Energy
