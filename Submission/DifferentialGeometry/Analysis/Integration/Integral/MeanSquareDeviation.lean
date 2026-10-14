import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.MeasureTheory
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis

theorem integral_norm_sub_average_sq_le_integral_norm_sub_sq
    {X F : Type*} [MeasurableSpace X] {μ : _root_.MeasureTheory.Measure X} [_root_.MeasureTheory.IsFiniteMeasure μ]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : X → F} (hf : _root_.MeasureTheory.MemLp f 2 μ) (c : F) :
    (∫ x, ‖f x - ⨍ y, f y ∂μ‖ ^ 2 ∂μ) ≤ ∫ x, ‖f x - c‖ ^ 2 ∂μ := by
  let m := ⨍ y, f y ∂μ
  have hres : _root_.MeasureTheory.Integrable (fun x => f x - m) μ :=
    (hf.integrable (by norm_num)).sub (_root_.MeasureTheory.integrable_const m)
  have hresSq : _root_.MeasureTheory.Integrable (fun x => ‖f x - m‖ ^ 2) μ :=
    (hf.sub (_root_.MeasureTheory.memLp_const m)).norm.integrable_sq
  have hcross : _root_.MeasureTheory.Integrable (fun x => _root_.Inner.inner ℝ (f x - m) (m - c)) μ :=
    hres.inner_const (m - c)
  have hcrosszero : (∫ x, _root_.Inner.inner ℝ (f x - m) (m - c) ∂μ) = 0 := by
    have hh := integral_inner (𝕜 := ℝ) hres (m - c)
    simp only [real_inner_comm] at hh
    rw [hh, _root_.MeasureTheory.integral_sub_average μ f, inner_zero_right]
  have hpoint (x : X) : ‖f x - c‖ ^ 2 =
      ‖f x - m‖ ^ 2 + 2 * _root_.Inner.inner ℝ (f x - m) (m - c) + ‖m - c‖ ^ 2 := by
    have heq : f x - c = (f x - m) + (m - c) := by abel
    rw [heq, norm_add_sq_real]
  simp_rw [hpoint]
  have hsum : _root_.MeasureTheory.Integrable (fun x => ‖f x - m‖ ^ 2 +
      2 * _root_.Inner.inner ℝ (f x - m) (m - c)) μ := hresSq.add (hcross.const_mul 2)
  rw [_root_.MeasureTheory.integral_add hsum (_root_.MeasureTheory.integrable_const _),
    _root_.MeasureTheory.integral_add hresSq (hcross.const_mul 2), _root_.MeasureTheory.integral_const_mul, hcrosszero, _root_.MulZeroClass.mul_zero, add_zero]
  exact le_add_of_nonneg_right (_root_.MeasureTheory.integral_nonneg fun _ => sq_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_norm_sub_average_sq_le_integral_norm_sub_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_norm_sub_average_sq_le_integral_norm_sub_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_norm_sub_average_sq_le_integral_norm_sub_sq ``Submission.DifferentialGeometry.Analysis.integral_norm_sub_average_sq_le_integral_norm_sub_sq

theorem integral_norm_sub_const_sq_le_two_difference_add
    {X F : Type*} [MeasurableSpace X] {μ : _root_.MeasureTheory.Measure X} [_root_.MeasureTheory.IsFiniteMeasure μ]
    [NormedAddCommGroup F] {f g : X → F}
    (hf : _root_.MeasureTheory.MemLp f 2 μ) (hg : _root_.MeasureTheory.MemLp g 2 μ) (c : F) :
    (∫ x, ‖f x - c‖ ^ 2 ∂μ) ≤
      2 * (∫ x, ‖f x - g x‖ ^ 2 ∂μ) + 2 * ∫ x, ‖g x - c‖ ^ 2 ∂μ := by
  have hdiff : _root_.MeasureTheory.Integrable (fun x => ‖f x - g x‖ ^ 2) μ := (hf.sub hg).norm.integrable_sq
  have hgc : _root_.MeasureTheory.Integrable (fun x => ‖g x - c‖ ^ 2) μ := (hg.sub (_root_.MeasureTheory.memLp_const c)).norm.integrable_sq
  rw [← _root_.MeasureTheory.integral_const_mul, ← _root_.MeasureTheory.integral_const_mul,
    ← _root_.MeasureTheory.integral_add (hdiff.const_mul 2) (hgc.const_mul 2)]
  apply _root_.MeasureTheory.integral_mono_ae (hf.sub (_root_.MeasureTheory.memLp_const c)).norm.integrable_sq
    ((hdiff.const_mul 2).add (hgc.const_mul 2))
  filter_upwards with x
  have hn : ‖f x - c‖ ≤ ‖f x - g x‖ + ‖g x - c‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (f x - g x) (g x - c)
  change ‖f x - c‖ ^ 2 ≤ 2 * ‖f x - g x‖ ^ 2 + 2 * ‖g x - c‖ ^ 2
  nlinarith [sq_nonneg (‖f x - g x‖ - ‖g x - c‖), norm_nonneg (f x - c),
    norm_nonneg (f x - g x), norm_nonneg (g x - c)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_norm_sub_const_sq_le_two_difference_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_norm_sub_const_sq_le_two_difference_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_norm_sub_const_sq_le_two_difference_add ``Submission.DifferentialGeometry.Analysis.integral_norm_sub_const_sq_le_two_difference_add

end DifferentialGeometry.Analysis

end

noncomputable section
open _root_.MeasureTheory
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis

theorem monotoneOn_integral_norm_sub_average_sq_ball
    {X F : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    {μ : _root_.MeasureTheory.Measure X}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : X → F} {c : X} {R : ℝ}
    [_root_.MeasureTheory.IsFiniteMeasure (μ.restrict (Metric.ball c R))]
    (hf : _root_.MeasureTheory.MemLp f 2 (μ.restrict (Metric.ball c R))) :
    MonotoneOn (fun r => ∫ x in Metric.ball c r,
      ‖f x - ⨍ y in Metric.ball c r, f y ∂μ‖ ^ 2 ∂μ) (Set.Ioc (0 : ℝ) R) := by
  intro r hr s hs hrs
  have hrR : Metric.ball c r ⊆ Metric.ball c R := Metric.ball_subset_ball hr.2
  have hsR : Metric.ball c s ⊆ Metric.ball c R := Metric.ball_subset_ball hs.2
  have hrs' : Metric.ball c r ⊆ Metric.ball c s := Metric.ball_subset_ball hrs
  let : _root_.MeasureTheory.IsFiniteMeasure (μ.restrict (Metric.ball c s)) :=
    isFiniteMeasure_restrict.mpr
      ((_root_.MeasureTheory.measure_mono hsR).trans_lt
        (by simpa using _root_.MeasureTheory.measure_lt_top (μ.restrict (Metric.ball c R)) Set.univ)).ne
  let : _root_.MeasureTheory.IsFiniteMeasure (μ.restrict (Metric.ball c r)) :=
    isFiniteMeasure_restrict.mpr
      ((_root_.MeasureTheory.measure_mono hrR).trans_lt
        (by simpa using _root_.MeasureTheory.measure_lt_top (μ.restrict (Metric.ball c R)) Set.univ)).ne
  have hfr := hf.mono_measure (Measure.restrict_mono_set μ hrR)
  have hfs := hf.mono_measure (Measure.restrict_mono_set μ hsR)
  let m := ⨍ y in Metric.ball c s, f y ∂μ
  apply (integral_norm_sub_average_sq_le_integral_norm_sub_sq hfr m).trans
  exact _root_.MeasureTheory.setIntegral_mono_set (hfs.sub (_root_.MeasureTheory.memLp_const m)).norm.integrable_sq
    (Filter.Eventually.of_forall fun x => sq_nonneg _) (Filter.Eventually.of_forall hrs')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.monotoneOn_integral_norm_sub_average_sq_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.monotoneOn_integral_norm_sub_average_sq_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.monotoneOn_integral_norm_sub_average_sq_ball ``Submission.DifferentialGeometry.Analysis.monotoneOn_integral_norm_sub_average_sq_ball


end DifferentialGeometry.Analysis

end

noncomputable section
open _root_.MeasureTheory
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis

theorem integral_component_sub_average_sq_le_vector_variance
    {X ι : Type*} [MeasurableSpace X] [Fintype ι] {μ : _root_.MeasureTheory.Measure X} [_root_.MeasureTheory.IsFiniteMeasure μ]
    {f : X → EuclideanSpace ℝ ι} (hf : _root_.MeasureTheory.MemLp f 2 μ) (i : ι) :
    (∫ x, (f x i - ⨍ y, f y i ∂μ) ^ 2 ∂μ) ≤
      ∫ x, ‖f x - ⨍ y, f y ∂μ‖ ^ 2 ∂μ := by
  let m := ⨍ y, f y ∂μ
  have hfi : _root_.MeasureTheory.MemLp (fun x => f x i) 2 μ :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).comp_memLp' hf
  have hh := integral_norm_sub_average_sq_le_integral_norm_sub_sq hfi (m i)
  simp only [Real.norm_eq_abs, sq_abs] at hh
  apply hh.trans
  apply _root_.MeasureTheory.integral_mono_ae (hfi.sub (_root_.MeasureTheory.memLp_const (m i))).integrable_sq
    (hf.sub (_root_.MeasureTheory.memLp_const m)).norm.integrable_sq
  filter_upwards with x
  change (f x i - m i) ^ 2 ≤ ‖f x - m‖ ^ 2
  have hp := PiLp.norm_apply_le (f x - m) i
  simpa only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs] using
    pow_le_pow_left₀ (norm_nonneg _) hp 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_component_sub_average_sq_le_vector_variance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_component_sub_average_sq_le_vector_variance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_component_sub_average_sq_le_vector_variance ``Submission.DifferentialGeometry.Analysis.integral_component_sub_average_sq_le_vector_variance

end DifferentialGeometry.Analysis

end
