import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.Lipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter
open scoped _root_.Topology

open _root_.ConvexOn in
theorem ConvexOn.isMinOn_add_norm_sq_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {s : Set E} (hf : ConvexOn ℝ s f)
    {ε : ℝ} (hε : 0 < ε) (x : E) {y : E} (hy : y ∈ s) :
    IsMinOn (fun z => f z + ‖z - x‖ ^ 2 / (2 * ε)) s y ↔
      ∀ z ∈ s, _root_.Inner.inner ℝ (x - y) (z - y) ≤ ε * (f z - f y) := by
  have hnorm (z : E) (t : ℝ) :
      ‖(1 - t) • y + t • z - x‖ ^ 2 = ‖y - x‖ ^ 2 -
        2 * t * _root_.Inner.inner ℝ (x - y) (z - y) + t ^ 2 * ‖z - y‖ ^ 2 := by
    have hv : (1 - t) • y + t • z - x = (y - x) + t • (z - y) := by
      simp only [sub_smul, one_smul, smul_sub]
      abel
    rw [hv, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [show y - x = -(x - y) by abel, inner_neg_left]
    ring
  constructor
  · intro hmin z hz
    have hbound (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
        inner ℝ (x - y) (z - y) ≤ ε * (f z - f y) + t / 2 * ‖z - y‖ ^ 2 := by
      have hmem := hf.1 hy hz (sub_nonneg.mpr ht1) ht.le (by ring : 1 - t + t = 1)
      have hm := hmin hmem
      have hc := hf.2 hy hz (sub_nonneg.mpr ht1) ht.le (by ring : 1 - t + t = 1)
      simp only [smul_eq_mul] at hc
      change f y + ‖y - x‖ ^ 2 / (2 * ε) ≤
        f ((1 - t) • y + t • z) + ‖(1 - t) • y + t • z - x‖ ^ 2 / (2 * ε) at hm
      rw [hnorm] at hm
      have hm' : 2 * ε * (f y - f ((1 - t) • y + t • z)) ≤
          -2 * t * _root_.Inner.inner ℝ (x - y) (z - y) + t ^ 2 * ‖z - y‖ ^ 2 := by
        have hh := (mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2 * ε))
        field_simp at hh
        nlinarith
      have h := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2 * ε)
      nlinarith
    have htend : _root_.Filter.Tendsto (fun t : ℝ => ε * (f z - f y) + t / 2 * ‖z - y‖ ^ 2)
        (𝓝[>] 0) (𝓝 (ε * (f z - f y))) := by
      have hc : Continuous (fun t : ℝ => ε * (f z - f y) + t / 2 * ‖z - y‖ ^ 2) := by fun_prop
      simpa only [zero_div, _root_.MulZeroClass.zero_mul, add_zero] using
        (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto htend
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with t ht ht1
    exact hbound t ht ht1.le
  · intro h z hz
    have hn := hnorm z 1
    simp only [sub_self, zero_smul, one_smul, zero_add, one_pow, one_mul] at hn
    have hs := h z hz
    change f y + ‖y - x‖ ^ 2 / (2 * ε) ≤ f z + ‖z - x‖ ^ 2 / (2 * ε)
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 2 * ε)).mp
    field_simp
    nlinarith [sq_nonneg ‖z - y‖]

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ConvexOn
  let env ← Lean.getEnv
  if env.contains `ConvexOn.isMinOn_add_norm_sq_iff then
    throwError "Refusing to shadow existing declaration ConvexOn.isMinOn_add_norm_sq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `ConvexOn.isMinOn_add_norm_sq_iff ``Submission.ConvexOn.isMinOn_add_norm_sq_iff

open _root_.ConvexOn in
theorem ConvexOn.norm_sub_sq_le_inner_sub_of_isMinOn_add_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {s : Set E} (hf : ConvexOn ℝ s f)
    {ε : ℝ} (hε : 0 < ε) {x y p q : E} (hp : p ∈ s) (hq : q ∈ s)
    (hpx : IsMinOn (fun z => f z + ‖z - x‖ ^ 2 / (2 * ε)) s p)
    (hqy : IsMinOn (fun z => f z + ‖z - y‖ ^ 2 / (2 * ε)) s q) :
    ‖p - q‖ ^ 2 ≤ _root_.Inner.inner ℝ (x - y) (p - q) := by
  have h₁ := (hf.isMinOn_add_norm_sq_iff hε x hp).mp hpx q hq
  have h₂ := (hf.isMinOn_add_norm_sq_iff hε y hq).mp hqy p hp
  have heq : _root_.Inner.inner ℝ (x - p) (q - p) + _root_.Inner.inner ℝ (y - q) (p - q) =
      ‖p - q‖ ^ 2 - _root_.Inner.inner ℝ (x - y) (p - q) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    ring
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ConvexOn.norm_sub_sq_le_inner_sub_of_isMinOn_add_norm_sq then
    throwError "Refusing to shadow existing declaration ConvexOn.norm_sub_sq_le_inner_sub_of_isMinOn_add_norm_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `ConvexOn.norm_sub_sq_le_inner_sub_of_isMinOn_add_norm_sq ``Submission.ConvexOn.norm_sub_sq_le_inner_sub_of_isMinOn_add_norm_sq

open _root_.ConvexOn in
theorem ConvexOn.lipschitzWith_of_isMinOn_add_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {s : Set E} (hf : ConvexOn ℝ s f)
    {ε : ℝ} (hε : 0 < ε) {P : E → E} (hP : ∀ x, P x ∈ s)
    (hmin : ∀ x, IsMinOn (fun z => f z + ‖z - x‖ ^ 2 / (2 * ε)) s (P x)) :
    LipschitzWith 1 P := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (hf.norm_sub_sq_le_inner_sub_of_isMinOn_add_norm_sq hε (hP x) (hP y)
    (hmin x) (hmin y)).trans (real_inner_le_norm _ _)
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  nlinarith [norm_nonneg (P x - P y), norm_nonneg (x - y)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ConvexOn.lipschitzWith_of_isMinOn_add_norm_sq then
    throwError "Refusing to shadow existing declaration ConvexOn.lipschitzWith_of_isMinOn_add_norm_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `ConvexOn.lipschitzWith_of_isMinOn_add_norm_sq ``Submission.ConvexOn.lipschitzWith_of_isMinOn_add_norm_sq
