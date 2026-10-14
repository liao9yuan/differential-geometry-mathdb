import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.Topology

open _root_.TendstoUniformlyOn in
theorem TendstoUniformlyOn.intervalIntegral
    {P E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter A} {J : Set P} {a b : ℝ}
    {f : A → ℝ × P → E} {g : ℝ × P → E}
    (hfg : TendstoUniformlyOn f g l (_root_.Set.uIcc a b ×ˢ J))
    (hf : ∀ᶠ i in l, ∀ t ∈ J, IntervalIntegrable (fun x => f i (x, t)) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hg : ∀ t ∈ J, IntervalIntegrable (fun x => g (x, t)) _root_.MeasureTheory.MeasureSpace.volume a b) :
    TendstoUniformlyOn (fun i t => ∫ x in a..b, f i (x, t))
      (fun t => ∫ x in a..b, g (x, t)) l J := by
  rw [Metric.tendstoUniformlyOn_iff] at hfg ⊢
  intro ε hε
  have hden : 0 < 2 * (|b - a| + 1) := by positivity
  have hδ : 0 < ε / (2 * (|b - a| + 1)) := div_pos hε hden
  filter_upwards [hf, hfg (ε / (2 * (|b - a| + 1))) hδ] with i hi hclose t ht
  rw [dist_eq_norm, norm_sub_rev, ← intervalIntegral.integral_sub (hi t ht) (hg t ht)]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := ε / (2 * (|b - a| + 1))) (fun x hx => ?_)).trans_lt ?_
  · exact (by simpa only [dist_eq_norm, norm_sub_rev] using
      (hclose (x, t) ⟨uIoc_subset_uIcc hx, ht⟩).le)
  · have hmul : ε / (2 * (|b - a| + 1)) * (2 * (|b - a| + 1)) = ε :=
      div_mul_cancel₀ ε hden.ne'
    nlinarith [abs_nonneg (b - a)]

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.TendstoUniformlyOn
  let env ← Lean.getEnv
  if env.contains `TendstoUniformlyOn.intervalIntegral then
    throwError "Refusing to shadow existing declaration TendstoUniformlyOn.intervalIntegral"
  Lean.modifyEnv fun env => Lean.addAlias env `TendstoUniformlyOn.intervalIntegral ``Submission.TendstoUniformlyOn.intervalIntegral

end

section

open _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis

theorem tendsto_integral_mul_of_tendstoUniformlyOn_Icc
    {f : ℕ → ℝ → ℝ} {v g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ n, ContinuousOn (f n) (_root_.Set.Icc a b)) (hg : ContinuousOn g (_root_.Set.Icc a b))
    (hlim : TendstoUniformlyOn f v _root_.Filter.atTop (_root_.Set.Icc a b)) :
    _root_.Filter.Tendsto (fun n => ∫ x in _root_.Set.Ioo a b, f n x * g x) _root_.Filter.atTop
      (𝓝 (∫ x in _root_.Set.Ioo a b, v x * g x)) := by
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  let C := _root_.Max.max D 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hprod : TendstoUniformlyOn (fun n x => f n x * g x) (fun x => v x * g x)
      atTop (_root_.Set.Icc a b) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim (ε / C) (div_pos hε hC)] with n hn
    intro x hx
    rw [Real.dist_eq, ← sub_mul, abs_mul]
    have hfg : |v x - f n x| < ε / C := by simpa only [Real.dist_eq] using hn x hx
    have hgc : |g x| ≤ C := by
      have h := hD x hx
      rw [Real.norm_eq_abs] at h
      exact h.trans (by dsimp [C]; linarith [le_max_left D 0])
    calc
      |v x - f n x| * |g x| ≤ |v x - f n x| * C :=
        mul_le_mul_of_nonneg_left hgc (abs_nonneg _)
      _ < ε := (lt_div_iff₀ hC).mp hfg
  have hprod' : TendstoUniformlyOn (fun n x => f n x * g x) (fun x => v x * g x)
      atTop (_root_.Set.uIcc a b) := by simpa only [_root_.Set.uIcc_of_le hab] using hprod
  have hFG : ∀ n, ContinuousOn (fun x => f n x * g x) (_root_.Set.uIcc a b) := by
    intro n x hx
    rw [_root_.Set.uIcc_of_le hab] at hx ⊢
    exact (hf n x hx).mul (hg x hx)
  have hh := TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    (μ := _root_.MeasureTheory.MeasureSpace.volume) (a := a) (b := b)
    (Eventually.of_forall hFG) hprod'
  simpa only [intervalIntegral.integral_of_le hab, _root_.MeasureTheory.integral_Ioc_eq_integral_Ioo] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendsto_integral_mul_of_tendstoUniformlyOn_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendsto_integral_mul_of_tendstoUniformlyOn_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendsto_integral_mul_of_tendstoUniformlyOn_Icc ``Submission.DifferentialGeometry.Analysis.tendsto_integral_mul_of_tendstoUniformlyOn_Icc

end DifferentialGeometry.Analysis

end
