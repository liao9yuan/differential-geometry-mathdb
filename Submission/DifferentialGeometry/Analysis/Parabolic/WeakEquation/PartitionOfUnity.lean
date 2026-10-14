import Submission.DifferentialGeometry.Topology.PartitionOfUnity.Derivative
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Set _root_.MeasureTheory
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace SmoothPartitionOfUnity
open _root_.SmoothPartitionOfUnity

variable {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

open _root_.SmoothPartitionOfUnity in
theorem sum_deriv_mul_fintsupportOn
    {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s)
    {K : Set M} (hK : IsCompact K) {f : ℝ × M → ℝ}
    (hfK : ∀ t, Function.support (fun x => f (t, x)) ⊆ K)
    (hfs : ∀ t, Function.support (fun x => f (t, x)) ⊆ s) (t : ℝ) (x : M) :
    (∑ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
      deriv (fun r => ρ i x * f (r, x)) t) = deriv (fun r => f (r, x)) t := by
  have hsupport (T : Set M) (hT : ∀ r, Function.support (fun y => f (r, y)) ⊆ T) :
      Function.support (fun y => deriv (fun r => f (r, y)) t) ⊆ T := by
    intro y hy
    by_contra hyT
    have hzero : (fun r => f (r, y)) = fun _ => (0 : ℝ) := by
      funext r
      exact Function.notMem_support.mp (fun h => hyT (hT r h))
    apply hy
    change deriv (fun r => f (r, y)) t = 0
    rw [hzero, deriv_const]
  have hcoe (i : ι) : ρ.toPartitionOfUnity i x = ρ i x := rfl
  simpa only [smul_eq_mul, deriv_const_mul_field, hcoe] using
    ρ.toPartitionOfUnity.sum_fintsupportOn_smul hK (hsupport K hfK) (hsupport s hfs) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SmoothPartitionOfUnity.sum_deriv_mul_fintsupportOn then
    throwError "Refusing to shadow existing declaration SmoothPartitionOfUnity.sum_deriv_mul_fintsupportOn"
  Lean.modifyEnv fun env => Lean.addAlias env `SmoothPartitionOfUnity.sum_deriv_mul_fintsupportOn ``Submission.SmoothPartitionOfUnity.sum_deriv_mul_fintsupportOn

variable [MeasurableSpace M]

open _root_.SmoothPartitionOfUnity in
theorem integrable_and_integral_time_spatial_derivative_eq_sum_fintsupportOn
    {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) (μ : _root_.MeasureTheory.Measure (ℝ × M))
    {K : Set M} (hK : IsCompact K) {f : ℝ × M → ℝ}
    (hfK : ∀ t, Function.support (fun x => f (t, x)) ⊆ K)
    (hfs : ∀ t, Function.support (fun x => f (t, x)) ⊆ s)
    (hf : ∀ᵐ z ∂μ, MDifferentiableAt I 𝓘(ℝ) (fun y => f (z.1, y)) z.2)
    (w : ℝ × M → ℝ)
    (A : ∀ z : ℝ × M, (TangentSpace I z.2 →L[ℝ] ℝ) →L[ℝ] ℝ)
    (hlocal : ∀ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
      _root_.MeasureTheory.Integrable (fun z => w z * deriv (fun t => ρ i z.2 * f (t, z.2)) z.1 +
        A z (mvfderiv I (fun y => ρ i y * f (z.1, y)) z.2)) μ) :
    _root_.MeasureTheory.Integrable (fun z => w z * deriv (fun t => f (t, z.2)) z.1 +
      A z (mvfderiv I (fun y => f (z.1, y)) z.2)) μ ∧
      (∫ z, w z * deriv (fun t => f (t, z.2)) z.1 +
        A z (mvfderiv I (fun y => f (z.1, y)) z.2) ∂μ) =
        ∑ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
          ∫ z, w z * deriv (fun t => ρ i z.2 * f (t, z.2)) z.1 +
            A z (mvfderiv I (fun y => ρ i y * f (z.1, y)) z.2) ∂μ := by
  have hsum :
      (fun z => ∑ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
        (w z * deriv (fun t => ρ i z.2 * f (t, z.2)) z.1 +
          A z (mvfderiv I (fun y => ρ i y * f (z.1, y)) z.2))) =ᵐ[μ]
      (fun z => w z * deriv (fun t => f (t, z.2)) z.1 +
        A z (mvfderiv I (fun y => f (z.1, y)) z.2)) := by
    filter_upwards [hf] with z hz
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      ρ.sum_deriv_mul_fintsupportOn hK hfK hfs z.1 z.2, ← map_sum,
      ρ.sum_mvfderiv_mul_fintsupportOn hK (hfK z.1) (hfs z.1) hz]
  refine ⟨(_root_.MeasureTheory.integrable_finsetSum _ hlocal).congr hsum, ?_⟩
  rw [← _root_.MeasureTheory.integral_congr_ae hsum, _root_.MeasureTheory.integral_finsetSum _ hlocal]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SmoothPartitionOfUnity.integrable_and_integral_time_spatial_derivative_eq_sum_fintsupportOn then
    throwError "Refusing to shadow existing declaration SmoothPartitionOfUnity.integrable_and_integral_time_spatial_derivative_eq_sum_fintsupportOn"
  Lean.modifyEnv fun env => Lean.addAlias env `SmoothPartitionOfUnity.integrable_and_integral_time_spatial_derivative_eq_sum_fintsupportOn ``Submission.SmoothPartitionOfUnity.integrable_and_integral_time_spatial_derivative_eq_sum_fintsupportOn


open _root_.SmoothPartitionOfUnity in
theorem integrable_and_integral_integral_time_spatial_derivative_eq_sum_fintsupportOn
    {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s)
    (μ : _root_.MeasureTheory.Measure ℝ) (ν : ℝ → _root_.MeasureTheory.Measure M)
    {K : Set M} (hK : IsCompact K) {f : ℝ × M → ℝ}
    (hfK : ∀ t, Function.support (fun x => f (t, x)) ⊆ K)
    (hfs : ∀ t, Function.support (fun x => f (t, x)) ⊆ s)
    (hf : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t, MDifferentiableAt I 𝓘(ℝ) (fun y => f (t, y)) x)
    (w : ℝ × M → ℝ)
    (A : ∀ z : ℝ × M, (TangentSpace I z.2 →L[ℝ] ℝ) →L[ℝ] ℝ)
    (hlocal : ∀ᵐ t ∂μ, ∀ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
      _root_.MeasureTheory.Integrable (fun x => w (t, x) * deriv (fun r => ρ i x * f (r, x)) t +
        A (t, x) (mvfderiv I (fun y => ρ i y * f (t, y)) x)) (ν t))
    (htime : ∀ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
      _root_.MeasureTheory.Integrable (fun t => ∫ x, w (t, x) * deriv (fun r => ρ i x * f (r, x)) t +
        A (t, x) (mvfderiv I (fun y => ρ i y * f (t, y)) x) ∂ν t) μ) :
    _root_.MeasureTheory.Integrable (fun t => ∫ x, w (t, x) * deriv (fun r => f (r, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y)) x) ∂ν t) μ ∧
      (∫ t, ∫ x, w (t, x) * deriv (fun r => f (r, x)) t +
        A (t, x) (mvfderiv I (fun y => f (t, y)) x) ∂ν t ∂μ) =
        ∑ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
          ∫ t, ∫ x, w (t, x) * deriv (fun r => ρ i x * f (r, x)) t +
            A (t, x) (mvfderiv I (fun y => ρ i y * f (t, y)) x) ∂ν t ∂μ := by
  have hsum :
      (fun t => ∑ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
        ∫ x, w (t, x) * deriv (fun r => ρ i x * f (r, x)) t +
          A (t, x) (mvfderiv I (fun y => ρ i y * f (t, y)) x) ∂ν t) =ᵐ[μ]
      (fun t => ∫ x, w (t, x) * deriv (fun r => f (r, x)) t +
        A (t, x) (mvfderiv I (fun y => f (t, y)) x) ∂ν t) := by
    filter_upwards [hf, hlocal] with t hft hlocalt
    rw [← _root_.MeasureTheory.integral_finsetSum _ hlocalt]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hft] with x hx
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      ρ.sum_deriv_mul_fintsupportOn hK hfK hfs t x, ← map_sum,
      ρ.sum_mvfderiv_mul_fintsupportOn hK (hfK t) (hfs t) hx]
  refine ⟨(_root_.MeasureTheory.integrable_finsetSum _ htime).congr hsum, ?_⟩
  rw [← _root_.MeasureTheory.integral_congr_ae hsum, _root_.MeasureTheory.integral_finsetSum _ htime]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SmoothPartitionOfUnity.integrable_and_integral_integral_time_spatial_derivative_eq_sum_fintsupportOn then
    throwError "Refusing to shadow existing declaration SmoothPartitionOfUnity.integrable_and_integral_integral_time_spatial_derivative_eq_sum_fintsupportOn"
  Lean.modifyEnv fun env => Lean.addAlias env `SmoothPartitionOfUnity.integrable_and_integral_integral_time_spatial_derivative_eq_sum_fintsupportOn ``Submission.SmoothPartitionOfUnity.integrable_and_integral_integral_time_spatial_derivative_eq_sum_fintsupportOn

end SmoothPartitionOfUnity
