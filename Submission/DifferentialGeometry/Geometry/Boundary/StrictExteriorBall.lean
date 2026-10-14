import Submission.DifferentialGeometry.Analysis.Calculus.Taylor.QuadraticBound
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Metric
open scoped _root_.RealInnerProductSpace _root_.ContDiff

namespace DifferentialGeometry.Analysis

private theorem dist_sq_lower_bound_of_inner_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {q y G : E} {ρ M c : ℝ} (hρ : 0 ≤ ρ) (hc : 0 < c) (hG : c ≤ ‖G‖)
    (hρM : ρ * M ≤ c / 2)
    (hinner : _root_.Inner.inner ℝ G (y - q) ≤ M / 2 * ‖y - q‖ ^ 2) :
    ρ ^ 2 + _root_.Dist.dist y q ^ 2 / 2 ≤ _root_.Dist.dist y (q + ρ • (‖G‖⁻¹ • G)) ^ 2 := by
  have hGpos : 0 < ‖G‖ := hc.trans_le hG
  let n : E := ‖G‖⁻¹ • G
  have hn : ‖n‖ = 1 := by
    dsimp only [n]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hGpos),
      inv_mul_cancel₀ hGpos.ne']
  have hinnern : ‖G‖ * _root_.Inner.inner ℝ (y - q) n = _root_.Inner.inner ℝ G (y - q) := by
    simp only [n, inner_smul_right, real_inner_comm (y - q) G]
    field_simp [ne_of_gt hGpos]
  have hscaled : ‖G‖ * (2 * ρ * _root_.Inner.inner ℝ (y - q) n) ≤ ‖G‖ * (‖y - q‖ ^ 2 / 2) := by
    calc
      _ = 2 * ρ * (‖G‖ * _root_.Inner.inner ℝ (y - q) n) := by ring
      _ = 2 * ρ * _root_.Inner.inner ℝ G (y - q) := by rw [hinnern]
      _ ≤ 2 * ρ * (M / 2 * ‖y - q‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = ρ * M * ‖y - q‖ ^ 2 := by ring
      _ ≤ (c / 2) * ‖y - q‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hρM (sq_nonneg _)
      _ ≤ (‖G‖ / 2) * ‖y - q‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hG (by norm_num))
          (sq_nonneg _)
      _ = _ := by ring
  have hcross := (mul_le_mul_iff_right₀ hGpos).mp hscaled
  change ρ ^ 2 + _root_.Dist.dist y q ^ 2 / 2 ≤ _root_.Dist.dist y (q + ρ • n) ^ 2
  rw [dist_eq_norm, dist_eq_norm,
    show y - (q + ρ • n) = (y - q) - ρ • n by abel,
    norm_sub_sq_real (y - q) (ρ • n), inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hρ, hn, mul_one]
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.dist_sq_lower_bound_of_inner_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.dist_sq_lower_bound_of_inner_le target :: scope.openDecls } }

theorem dist_sq_lower_bound_of_regular_sublevel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {g : E → ℝ} {U : Set E} {q y : E} {M c ρ : ℝ}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hg : ContDiffOn ℝ 2 g U)
    (hM : ∀ x ∈ U, ‖iteratedFDeriv ℝ 2 g x‖ ≤ M)
    (hq : q ∈ U) (hy : y ∈ U) (hgq : g q = 0) (hgy : g y ≤ 0)
    (hc : 0 < c) (hgrad : c ≤ ‖gradient g q‖) (hρ : 0 ≤ ρ) (hρM : ρ * M ≤ c / 2) :
    ρ ^ 2 + _root_.Dist.dist y q ^ 2 / 2 ≤
      dist y (q + ρ • (‖gradient g q‖⁻¹ • gradient g q)) ^ 2 := by
  have hTaylor := norm_sub_sub_fderiv_le_of_contDiffOn hU hconv hg hM hq hy
  rw [Real.norm_eq_abs, hgq, sub_zero] at hTaylor
  have hinner : _root_.Inner.inner ℝ (gradient g q) (y - q) ≤ M / 2 * ‖y - q‖ ^ 2 := by
    rw [inner_gradient_left]
    have hh := (abs_le.mp hTaylor).1
    linarith
  exact dist_sq_lower_bound_of_inner_le hρ hc hgrad hρM hinner

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.dist_sq_lower_bound_of_regular_sublevel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.dist_sq_lower_bound_of_regular_sublevel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.dist_sq_lower_bound_of_regular_sublevel ``Submission.DifferentialGeometry.Analysis.dist_sq_lower_bound_of_regular_sublevel

theorem exists_uniform_strict_exterior_ball_on_compact_regular_level
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {g : E → ℝ} {U K : Set E} (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hzero : ∀ q ∈ K, g q = 0)
    (hregular : ∀ q ∈ K, gradient g q ≠ 0) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧ ∀ q ∈ K,
      _root_.Dist.dist (q + ρ • (‖gradient g q‖⁻¹ • gradient g q)) q = ρ ∧
      ∀ y ∈ Metric.ball q δ, g y ≤ 0 →
        ρ ^ 2 + _root_.Dist.dist y q ^ 2 / 2 ≤
          dist y (q + ρ • (‖gradient g q‖⁻¹ • gradient g q)) ^ 2 := by
  have hgradc : ContinuousOn (gradient g) U := by
    exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn
      (hg.continuousOn_fderiv_of_isOpen hU (by norm_num))
  have hinv : ContinuousOn (fun q => ‖gradient g q‖⁻¹) K :=
    (hgradc.mono hKU).norm.inv₀ (fun q hq => norm_ne_zero_iff.mpr (hregular q hq))
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hinv
  let c : ℝ := (_root_.Max.max B 1)⁻¹
  have hBpos : 0 < _root_.Max.max B 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hc : 0 < c := inv_pos.mpr hBpos
  have hgrad (q : E) (hq : q ∈ K) : c ≤ ‖gradient g q‖ := by
    have hp : 0 < ‖gradient g q‖ := norm_pos_iff.mpr (hregular q hq)
    have hh : ‖gradient g q‖⁻¹ ≤ _root_.Max.max B 1 := by
      have ht := hB q hq
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)] at ht
      exact ht.trans (le_max_left _ _)
    exact (inv_le_comm₀ hBpos hp).mpr hh
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hH : ContinuousOn (iteratedFDeriv ℝ 2 g) (_root_.Metric.cthickening δ K) :=
    (ContinuousOn.continuousOn_iteratedFDeriv hg hU (by norm_num)).mono hδU
  obtain ⟨M₀, hM₀⟩ := hK.cthickening.exists_bound_of_continuousOn hH
  let M : ℝ := _root_.Max.max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  let ρ : ℝ := c / (2 * (M + 1))
  have hρ : 0 < ρ := div_pos hc (by positivity)
  have hρM : ρ * M ≤ c / 2 := by
    have hden : 0 < 2 * (M + 1) := by positivity
    have hid : ρ * (2 * (M + 1)) = c := div_mul_cancel₀ c (ne_of_gt hden)
    nlinarith
  refine ⟨δ, ρ, hδ, hρ, ?_⟩
  intro q hq
  have hgp : 0 < ‖gradient g q‖ := hc.trans_le (hgrad q hq)
  refine ⟨?_, ?_⟩
  · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hρ, abs_of_pos (inv_pos.mpr hgp),
      inv_mul_cancel₀ hgp.ne', mul_one]
  · intro y hy hgy
    have hball : Metric.ball q δ ⊆ _root_.Metric.cthickening δ K :=
      Metric.ball_subset_closedBall.trans (_root_.Metric.closedBall_subset_cthickening hq δ)
    exact dist_sq_lower_bound_of_regular_sublevel Metric.isOpen_ball (convex_ball q δ)
      (hg.mono (hball.trans hδU))
      (fun x hx => (hM₀ x (hball hx)).trans (le_max_left _ _))
      (Metric.mem_ball_self hδ) hy (hzero q hq) hgy hc (hgrad q hq) hρ.le hρM

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_uniform_strict_exterior_ball_on_compact_regular_level then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_uniform_strict_exterior_ball_on_compact_regular_level"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_uniform_strict_exterior_ball_on_compact_regular_level ``Submission.DifferentialGeometry.Analysis.exists_uniform_strict_exterior_ball_on_compact_regular_level

end DifferentialGeometry.Analysis

end

end
