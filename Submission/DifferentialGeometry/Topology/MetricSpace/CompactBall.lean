import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Set _root_.Filter
open scoped _root_.Topology

open _root_.Isometry in
theorem Isometry.isCompact_closedBall_of_punctured_closedBall
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Isometry f)
    {p : Y} {r : ℝ} (hcompact : IsCompact (Metric.closedBall p r))
    (hcover : Metric.closedBall p r ⊆ _root_.Insert.insert p (_root_.Set.range f))
    {x : X} {R : ℝ} (hR : R < _root_.Dist.dist (f x) p) (hbuffer : _root_.Dist.dist (f x) p + R ≤ r) :
    IsCompact (Metric.closedBall x R) := by
  have hsub : Metric.closedBall (f x) R ⊆ Metric.closedBall p r := by
    intro y hy
    have htriangle := dist_triangle y (f x) p
    change _root_.Dist.dist y (f x) ≤ R at hy
    change _root_.Dist.dist y p ≤ r
    linarith only [htriangle, hy, hbuffer]
  have hK := hcompact.of_isClosed_subset Metric.isClosed_closedBall hsub
  have hrange : Metric.closedBall (f x) R ⊆ _root_.Set.range f := by
    intro y hy
    rcases hcover (hsub hy) with h | h
    · rw [h] at hy
      have hdist : _root_.Dist.dist (f x) p ≤ R := by simpa only [Metric.mem_closedBall, dist_comm] using hy
      exact False.elim (hR.not_ge hdist)
    · exact h
  have hpre : f ⁻¹' Metric.closedBall (f x) R = Metric.closedBall x R := by
    ext y
    simp only [_root_.Set.mem_preimage, Metric.mem_closedBall, hf.dist_eq]
  rw [← hpre]
  exact (hf.isEmbedding.isInducing.isCompact_preimage_iff hrange).mpr hK

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Isometry
  let env ← Lean.getEnv
  if env.contains `Isometry.isCompact_closedBall_of_punctured_closedBall then
    throwError "Refusing to shadow existing declaration Isometry.isCompact_closedBall_of_punctured_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `Isometry.isCompact_closedBall_of_punctured_closedBall ``Submission.Isometry.isCompact_closedBall_of_punctured_closedBall

open _root_.Isometry in
theorem Isometry.eventually_isCompact_scaled_closedBall
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Isometry f)
    {q : Y} {r : ℝ} (hr : 0 < r) (hcompact : IsCompact (Metric.closedBall q r))
    (hcover : Metric.closedBall q r ⊆ _root_.Insert.insert q (_root_.Set.range f))
    {x : ℕ → X} (hx : _root_.Filter.Tendsto (fun n => f (x n)) _root_.Filter.atTop (𝓝 q))
    {Q : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hquant : ∀ᶠ n in _root_.Filter.atTop, (2 * a) ^ 2 < Q n * _root_.Dist.dist (f (x n)) q ^ 2) :
    ∀ᶠ n in _root_.Filter.atTop, 0 < Q n ∧
      IsCompact (Metric.closedBall (x n) (a / Real.sqrt (Q n))) ∧
      ∀ y ∈ Metric.closedBall (x n) (a / Real.sqrt (Q n)),
        _root_.Dist.dist (f (x n)) q / 2 < _root_.Dist.dist (f y) q ∧
          dist (f y) q < 3 * _root_.Dist.dist (f (x n)) q / 2 := by
  have hd : _root_.Filter.Tendsto (fun n => _root_.Dist.dist (f (x n)) q) _root_.Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_iff_dist_tendsto_zero.mp hx
  filter_upwards [hquant, hd.eventually (eventually_lt_nhds (half_pos hr))] with n hn hnear
  have hQ : 0 < Q n := by
    by_contra hQ
    have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hQ) (sq_nonneg (_root_.Dist.dist (f (x n)) q))
    nlinarith only [hn, hh, sq_nonneg (2 * a)]
  have hsqrt : 0 < Real.sqrt (Q n) := Real.sqrt_pos.mpr hQ
  have hroot : 2 * a < Real.sqrt (Q n) * _root_.Dist.dist (f (x n)) q := by
    apply (sq_lt_sq₀ (by positivity) (mul_nonneg hsqrt.le dist_nonneg)).mp
    simpa only [mul_pow, Real.sq_sqrt hQ.le] using hn
  have hsmall : a / Real.sqrt (Q n) < _root_.Dist.dist (f (x n)) q / 2 := by
    apply (div_lt_iff₀ hsqrt).mpr
    nlinarith only [hroot]
  have hdistpos : 0 < _root_.Dist.dist (f (x n)) q := by
    have hh : 0 ≤ a / Real.sqrt (Q n) := by positivity
    linarith only [hh, hsmall]
  refine ⟨hQ, hf.isCompact_closedBall_of_punctured_closedBall hcompact hcover
    (hsmall.trans (half_lt_self hdistpos)) (by linarith only [hsmall, hnear, hr]), ?_⟩
  intro y hy
  have hxy : _root_.Dist.dist (f y) (f (x n)) ≤ a / Real.sqrt (Q n) := by
    rw [hf.dist_eq]
    exact hy
  have htri₁ := dist_triangle (f (x n)) (f y) q
  have htri₂ := dist_triangle (f y) (f (x n)) q
  rw [dist_comm (f (x n)) (f y)] at htri₁
  constructor <;> linarith only [htri₁, htri₂, hxy, hsmall]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Isometry.eventually_isCompact_scaled_closedBall then
    throwError "Refusing to shadow existing declaration Isometry.eventually_isCompact_scaled_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `Isometry.eventually_isCompact_scaled_closedBall ``Submission.Isometry.eventually_isCompact_scaled_closedBall
