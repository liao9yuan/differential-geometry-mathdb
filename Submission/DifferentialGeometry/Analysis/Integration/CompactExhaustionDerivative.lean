import Submission.DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricContinuity
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis

section Measure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

theorem tendsto_integral_sq_mul_of_compactExhaustion
    (K : CompactExhaustion X) {μ : _root_.MeasureTheory.Measure X} {χ : ℕ → X → ℝ} {f : X → ℝ}
    (hχmeas : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (χ n) μ)
    (hχbound : ∀ n, ∀ᵐ x ∂μ, ‖χ n x‖ ≤ 1)
    (hχone : ∀ n, ∀ x ∈ K n, χ n x = 1) (hf : _root_.MeasureTheory.Integrable f μ) :
    Tendsto (fun n => ∫ x, χ n x ^ 2 * f x ∂μ) _root_.Filter.atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hmeas (n : ℕ) : _root_.MeasureTheory.AEStronglyMeasurable (fun x => χ n x ^ 2 * f x) μ :=
    ((hχmeas n).pow 2).mul hf.aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖χ n x ^ 2 * f x‖ ≤ ‖f x‖ := by
    filter_upwards [hχbound n] with x hx
    rw [norm_mul, norm_pow]
    have hpow : ‖χ n x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (χ n x)]
    exact mul_le_of_le_one_left (norm_nonneg _) hpow
  have hpoint (x : X) : _root_.Filter.Tendsto (fun n => χ n x ^ 2 * f x) _root_.Filter.atTop (𝓝 (f x)) := by
    obtain ⟨n₀, hn₀⟩ := K.exists_mem x
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [_root_.Filter.eventually_ge_atTop n₀] with n hn
    simp only [hχone n x (K.subset hn hn₀), one_pow, one_mul]
  exact _root_.MeasureTheory.tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    hmeas hf.norm hbound (Eventually.of_forall hpoint)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendsto_integral_sq_mul_of_compactExhaustion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendsto_integral_sq_mul_of_compactExhaustion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendsto_integral_sq_mul_of_compactExhaustion ``Submission.DifferentialGeometry.Analysis.tendsto_integral_sq_mul_of_compactExhaustion

end Measure

section Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem eventually_mvfderiv_eq_zero_of_compactExhaustion
    (K : CompactExhaustion M) {χ : ℕ → M → ℝ}
    (hχone : ∀ n, ∀ x ∈ K n, χ n x = 1) (x : M) :
    ∀ᶠ n in _root_.Filter.atTop, mvfderiv (I := I) (χ n) x = 0 := by
  obtain ⟨n₀, hn₀⟩ := K.exists_mem x
  have hx : x ∈ interior (K (n₀ + 1)) := K.subset_interior_succ n₀ hn₀
  filter_upwards [_root_.Filter.eventually_ge_atTop (n₀ + 1)] with n hn
  have heq : χ n =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact hχone n y (K.subset hn (interior_subset hy))
  have hd := heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ))
  ext v
  rw [mvfderiv_real_eq_mfderiv (I := I), hd, mfderiv_const]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.eventually_mvfderiv_eq_zero_of_compactExhaustion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.eventually_mvfderiv_eq_zero_of_compactExhaustion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.eventually_mvfderiv_eq_zero_of_compactExhaustion ``Submission.DifferentialGeometry.Analysis.eventually_mvfderiv_eq_zero_of_compactExhaustion

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M]

open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.Geometry.Operator

theorem tendsto_integral_normSq0S_differential_mul_of_compactExhaustion
    (K : CompactExhaustion M) (g : SmoothRiemannianMetric I M)
    (χ : ℕ → C^∞⟮I, M; ℝ⟯) {μ : _root_.MeasureTheory.Measure M} {f : M → ℝ} {C : ℝ}
    (hχone : ∀ n, ∀ x ∈ K n, χ n x = 1)
    (hbound : ∀ n, ∀ᵐ x ∂μ,
      normSq0S (I := I) g x 1 (differential1FormFun (I := I) (χ n) x) ≤ C)
    (hf : _root_.MeasureTheory.Integrable f μ) :
    _root_.Filter.Tendsto (fun n => ∫ x,
      normSq0S (I := I) g x 1 (differential1FormFun (I := I) (χ n) x) * f x ∂μ)
      atTop (𝓝 0) := by
  let q : ℕ → M → ℝ := fun n x =>
    normSq0S (I := I) g x 1 (differential1FormFun (I := I) (χ n) x)
  have hqcont (n : ℕ) : Continuous (q n) :=
    normSq0S_cont (I := I) g (duSec (I := I) (χ n) (χ n).contMDiff)
  have hqnonneg (n : ℕ) (x : M) : 0 ≤ q n x := normSq0S_nonneg (I := I) g x 1 _
  have hmeas (n : ℕ) : _root_.MeasureTheory.AEStronglyMeasurable (fun x => q n x * f x) μ :=
    (hqcont n).aestronglyMeasurable.mul hf.aestronglyMeasurable
  have hdom (n : ℕ) : ∀ᵐ x ∂μ, ‖q n x * f x‖ ≤ |C| * ‖f x‖ := by
    filter_upwards [hbound n] with x hx
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hqnonneg n x)]
    exact mul_le_mul_of_nonneg_right (hx.trans (le_abs_self C)) (norm_nonneg _)
  have hpoint (x : M) : _root_.Filter.Tendsto (fun n => q n x * f x) _root_.Filter.atTop (𝓝 0) := by
    have hzero := eventually_mvfderiv_eq_zero_of_compactExhaustion (I := I) K hχone x
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hzero] with n hn
    have hdf : differential1FormFun (I := I) (χ n) x = 0 := by
      ext v
      simp only [differential1FormFun, hn]
      rfl
    have hnzero := (normSq0S_eq_zero_iff (I := I) g x 1 0).2 rfl
    simp only [q, hdf, hnzero, _root_.MulZeroClass.zero_mul]
  simpa only [_root_.MeasureTheory.integral_zero] using
    _root_.MeasureTheory.tendsto_integral_of_dominated_convergence (fun x => |C| * ‖f x‖)
      hmeas (hf.norm.const_mul |C|) hdom (Eventually.of_forall hpoint)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendsto_integral_normSq0S_differential_mul_of_compactExhaustion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendsto_integral_normSq0S_differential_mul_of_compactExhaustion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendsto_integral_normSq0S_differential_mul_of_compactExhaustion ``Submission.DifferentialGeometry.Analysis.tendsto_integral_normSq0S_differential_mul_of_compactExhaustion

end Manifold

end DifferentialGeometry.Analysis
