import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
namespace DifferentialGeometry.Geometry.Comparison.Toponogov

noncomputable def hyperbolicComparisonCosine (k a b c : ℝ) : ℝ :=
  (Real.cosh (k * a) * Real.cosh (k * b) - Real.cosh (k * c)) /
    (Real.sinh (k * a) * Real.sinh (k * b))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonCosine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonCosine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonCosine ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonCosine

noncomputable def hyperbolicComparisonAngle (k a b c : ℝ) : ℝ :=
  Real.arccos (hyperbolicComparisonCosine k a b c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonAngle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonAngle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonAngle ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonAngle

theorem hyperbolicComparisonCosine_comm (k a b c : ℝ) :
    hyperbolicComparisonCosine k a b c = hyperbolicComparisonCosine k b a c := by
  unfold hyperbolicComparisonCosine
  rw [mul_comm (Real.cosh _), mul_comm (Real.sinh _)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonCosine_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonCosine_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonCosine_comm ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonCosine_comm

theorem hyperbolicComparisonAngle_comm (k a b c : ℝ) :
    hyperbolicComparisonAngle k a b c = hyperbolicComparisonAngle k b a c := by
  unfold hyperbolicComparisonAngle
  rw [hyperbolicComparisonCosine_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonAngle_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonAngle_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonAngle_comm ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.hyperbolicComparisonAngle_comm

end DifferentialGeometry.Geometry.Comparison.Toponogov

end

section
open _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem sinh_dslope_identity (x : ℝ) :
    x * dslope Real.sinh 0 x = Real.sinh x := by
  simpa only [sub_zero, smul_eq_mul, Real.sinh_zero] using sub_smul_dslope Real.sinh 0 x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.sinh_dslope_identity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Comparison.Toponogov.sinh_dslope_identity target :: scope.openDecls } }

private theorem cosh_sub_eq_two_sinh (x y z : ℝ) :
    Real.cosh z - Real.cosh x * Real.cosh y + Real.sinh x * Real.sinh y =
      2 * Real.sinh ((z + x - y) / 2) * Real.sinh ((z - x + y) / 2) := by
  have hs : (z + x - y) / 2 + (z - x + y) / 2 = z := by ring
  have hd : (z + x - y) / 2 - (z - x + y) / 2 = x - y := by ring
  have hadd := Real.cosh_add ((z + x - y) / 2) ((z - x + y) / 2)
  have hsub := Real.cosh_sub ((z + x - y) / 2) ((z - x + y) / 2)
  rw [hs] at hadd
  rw [hd, Real.cosh_sub] at hsub
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.cosh_sub_eq_two_sinh
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Comparison.Toponogov.cosh_sub_eq_two_sinh target :: scope.openDecls } }

private theorem comparison_cosine_difference_identity {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (Real.cosh x * Real.cosh y - Real.cosh z) / (Real.sinh x * Real.sinh y) -
      (x ^ 2 + y ^ 2 - z ^ 2) / (2 * x * y) =
    ((z ^ 2 - (x - y) ^ 2) / (2 * x * y)) *
      (1 - dslope Real.sinh 0 ((z + x - y) / 2) *
        dslope Real.sinh 0 ((z - x + y) / 2) /
        (dslope Real.sinh 0 x * dslope Real.sinh 0 y)) := by
  have hsx : Real.sinh x ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hx)
  have hsy : Real.sinh y ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hy)
  rw [dslope_of_ne Real.sinh hx.ne', dslope_of_ne Real.sinh hy.ne']
  simp only [slope_def_field, sub_zero, Real.sinh_zero]
  have h := cosh_sub_eq_two_sinh x y z
  have hu := sinh_dslope_identity ((z + x - y) / 2)
  have hv := sinh_dslope_identity ((z - x + y) / 2)
  rw [← hu, ← hv] at h
  field_simp
  nlinarith [h]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.comparison_cosine_difference_identity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Comparison.Toponogov.comparison_cosine_difference_identity target :: scope.openDecls } }

private theorem comparison_cosine_complement_bounds {x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hlower : |x - y| ≤ z) (hupper : z ≤ x + y) :
    0 ≤ (z ^ 2 - (x - y) ^ 2) / (2 * x * y) ∧
      (z ^ 2 - (x - y) ^ 2) / (2 * x * y) ≤ 2 := by
  have hden : 0 < 2 * x * y := by positivity
  have hz : 0 ≤ z := (abs_nonneg _).trans hlower
  constructor
  · apply div_nonneg _ hden.le
    nlinarith [sq_abs (x - y), mul_self_le_mul_self (abs_nonneg _) hlower]
  · rw [div_le_iff₀ hden]
    nlinarith [mul_self_le_mul_self hz hupper]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.comparison_cosine_complement_bounds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Comparison.Toponogov.comparison_cosine_complement_bounds target :: scope.openDecls } }

private theorem tendsto_dimensionless_comparison_difference
    {ι : Type*} {l : Filter ι} {x y z : ι → ℝ}
    (hgood : ∀ᶠ i in l, 0 < x i ∧ 0 < y i ∧ |x i - y i| ≤ z i ∧ z i ≤ x i + y i)
    (hx : _root_.Filter.Tendsto x l (𝓝 0)) (hy : _root_.Filter.Tendsto y l (𝓝 0)) :
    _root_.Filter.Tendsto (fun i =>
      (Real.cosh (x i) * Real.cosh (y i) - Real.cosh (z i)) /
        (Real.sinh (x i) * Real.sinh (y i)) -
      (x i ^ 2 + y i ^ 2 - z i ^ 2) / (2 * x i * y i)) l (𝓝 0) := by
  have hz : _root_.Filter.Tendsto z l (𝓝 0) := squeeze_zero'
    (hgood.mono fun i hi => (abs_nonneg _).trans hi.2.2.1)
    (hgood.mono fun i hi => hi.2.2.2) (by simpa using hx.add hy)
  have hu : _root_.Filter.Tendsto (fun i => (z i + x i - y i) / 2) l (𝓝 0) := by
    simpa using ((hz.add hx).sub hy).div_const 2
  have hv : _root_.Filter.Tendsto (fun i => (z i - x i + y i) / 2) l (𝓝 0) := by
    simpa using ((hz.sub hx).add hy).div_const 2
  have hcont : ContinuousAt (dslope Real.sinh 0) 0 :=
    continuousAt_dslope_same.mpr Real.differentiableAt_sinh
  have hdslope : dslope Real.sinh 0 0 = 1 := by simp [Real.deriv_sinh]
  have hsu : _root_.Filter.Tendsto (fun i => dslope Real.sinh 0 ((z i + x i - y i) / 2)) l (𝓝 1) := by
    simpa only [hdslope, Function.comp_def] using hcont.tendsto.comp hu
  have hsv : _root_.Filter.Tendsto (fun i => dslope Real.sinh 0 ((z i - x i + y i) / 2)) l (𝓝 1) := by
    simpa only [hdslope, Function.comp_def] using hcont.tendsto.comp hv
  have hsx : _root_.Filter.Tendsto (fun i => dslope Real.sinh 0 (x i)) l (𝓝 1) := by
    simpa only [hdslope, Function.comp_def] using hcont.tendsto.comp hx
  have hsy : _root_.Filter.Tendsto (fun i => dslope Real.sinh 0 (y i)) l (𝓝 1) := by
    simpa only [hdslope, Function.comp_def] using hcont.tendsto.comp hy
  let R : ι → ℝ := fun i =>
    dslope Real.sinh 0 ((z i + x i - y i) / 2) *
      dslope Real.sinh 0 ((z i - x i + y i) / 2) /
        (dslope Real.sinh 0 (x i) * dslope Real.sinh 0 (y i))
  have hR : _root_.Filter.Tendsto R l (𝓝 1) := by
    simpa only [R, mul_one, div_one, Pi.div_apply] using! (hsu.mul hsv).div (hsx.mul hsy) (by norm_num)
  have hzero : _root_.Filter.Tendsto (fun i => 2 * ‖1 - R i‖) l (𝓝 0) := by
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).sub hR).norm).const_mul 2
  apply squeeze_zero_norm' _ hzero
  filter_upwards [hgood] with i hi
  rw [comparison_cosine_difference_identity hi.1 hi.2.1, norm_mul]
  have hb := comparison_cosine_complement_bounds hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_dimensionless_comparison_difference
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_dimensionless_comparison_difference target :: scope.openDecls } }

theorem tendsto_hyperbolic_comparison_cosine_sub_euclidean
    {ι : Type*} {l : Filter ι} {k a b c : ι → ℝ}
    (hgood : ∀ᶠ i in l,
      0 < k i ∧ 0 < a i ∧ 0 < b i ∧ |a i - b i| ≤ c i ∧ c i ≤ a i + b i)
    (hsmall : _root_.Filter.Tendsto (fun i => k i * _root_.Max.max (a i) (b i)) l (𝓝 0)) :
    _root_.Filter.Tendsto (fun i =>
      (Real.cosh (k i * a i) * Real.cosh (k i * b i) - Real.cosh (k i * c i)) /
        (Real.sinh (k i * a i) * Real.sinh (k i * b i)) -
      (a i ^ 2 + b i ^ 2 - c i ^ 2) / (2 * a i * b i)) l (𝓝 0) := by
  have hx : _root_.Filter.Tendsto (fun i => k i * a i) l (𝓝 0) := squeeze_zero'
    (hgood.mono fun i hi => mul_nonneg hi.1.le hi.2.1.le)
    (hgood.mono fun i hi => mul_le_mul_of_nonneg_left (le_max_left _ _) hi.1.le) hsmall
  have hy : _root_.Filter.Tendsto (fun i => k i * b i) l (𝓝 0) := squeeze_zero'
    (hgood.mono fun i hi => mul_nonneg hi.1.le hi.2.2.1.le)
    (hgood.mono fun i hi => mul_le_mul_of_nonneg_left (le_max_right _ _) hi.1.le) hsmall
  have hscaled : ∀ᶠ i in l,
      0 < k i * a i ∧ 0 < k i * b i ∧
        |k i * a i - k i * b i| ≤ k i * c i ∧
        k i * c i ≤ k i * a i + k i * b i := by
    filter_upwards [hgood] with i hi
    refine ⟨mul_pos hi.1 hi.2.1, mul_pos hi.1 hi.2.2.1, ?_, ?_⟩
    · rw [← mul_sub, abs_mul, abs_of_pos hi.1]
      exact mul_le_mul_of_nonneg_left hi.2.2.2.1 hi.1.le
    · simpa only [mul_add] using mul_le_mul_of_nonneg_left hi.2.2.2.2 hi.1.le
  have h := tendsto_dimensionless_comparison_difference hscaled hx hy
  apply h.congr'
  filter_upwards [hgood] with i hi
  congr 1
  field_simp [ne_of_gt hi.1, ne_of_gt hi.2.1, ne_of_gt hi.2.2.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_hyperbolic_comparison_cosine_sub_euclidean then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_hyperbolic_comparison_cosine_sub_euclidean"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_hyperbolic_comparison_cosine_sub_euclidean ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_hyperbolic_comparison_cosine_sub_euclidean

private theorem tendsto_arccos_sub_of_tendsto_sub
    {ι : Type*} {l : Filter ι} {x y : ι → ℝ}
    (hy : ∀ᶠ i in l, y i ∈ Set.Icc (-1) 1)
    (hclose : _root_.Filter.Tendsto (fun i => x i - y i) l (𝓝 0)) :
    Tendsto (fun i => Real.arccos (x i) - Real.arccos (y i)) l (𝓝 0) := by
  have hunit : ∀ᶠ i in l, |x i - y i| < 1 := by
    simpa only [Real.dist_eq, sub_zero] using Metric.tendsto_nhds.mp hclose 1 zero_lt_one
  have hbound : ∀ᶠ i in l, x i ∈ Set.Icc (-2) 2 ∧ y i ∈ Set.Icc (-2) 2 := by
    filter_upwards [hy, hunit] with i hi hdist
    have ha := abs_lt.mp hdist
    exact ⟨⟨by linarith [hi.1], by linarith [hi.2]⟩,
      ⟨by linarith [hi.1], by linarith [hi.2]⟩⟩
  have huc : UniformContinuousOn Real.arccos (Set.Icc (-2) 2) :=
    isCompact_Icc.uniformContinuousOn_of_continuous Real.continuous_arccos.continuousOn
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hcontrol⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  filter_upwards [hbound, Metric.tendsto_nhds.mp hclose δ hδ] with i hb hd
  have hxy : _root_.Dist.dist (x i) (y i) < δ := by simpa only [Real.dist_eq, sub_zero] using hd
  simpa only [Real.dist_eq, sub_zero] using hcontrol (x i) hb.1 (y i) hb.2 hxy

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_arccos_sub_of_tendsto_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_arccos_sub_of_tendsto_sub target :: scope.openDecls } }

theorem tendsto_hyperbolic_comparison_angle_sub_euclidean
    {ι : Type*} {l : Filter ι} {k a b c : ι → ℝ}
    (hgood : ∀ᶠ i in l,
      0 < k i ∧ 0 < a i ∧ 0 < b i ∧ |a i - b i| ≤ c i ∧ c i ≤ a i + b i)
    (hsmall : _root_.Filter.Tendsto (fun i => k i * _root_.Max.max (a i) (b i)) l (𝓝 0)) :
    _root_.Filter.Tendsto (fun i =>
      Real.arccos ((Real.cosh (k i * a i) * Real.cosh (k i * b i) - Real.cosh (k i * c i)) /
        (Real.sinh (k i * a i) * Real.sinh (k i * b i))) -
      comparisonAngle (a i) (b i) (c i)) l (𝓝 0) := by
  apply tendsto_arccos_sub_of_tendsto_sub _
    (tendsto_hyperbolic_comparison_cosine_sub_euclidean hgood hsmall)
  filter_upwards [hgood] with i hi
  exact comparison_cosine_mem_Icc hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_hyperbolic_comparison_angle_sub_euclidean then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_hyperbolic_comparison_angle_sub_euclidean"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_hyperbolic_comparison_angle_sub_euclidean ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.tendsto_hyperbolic_comparison_angle_sub_euclidean

theorem eventually_comparisonAngle_ge_half_of_hyperbolic_comparison
    {ι : Type*} {l : Filter ι} {k a b c a' b' c' : ι → ℝ} {θ : ℝ}
    (hθ : 0 < θ)
    (hgood : ∀ᶠ i in l,
      0 < k i ∧ 0 < a i ∧ 0 < b i ∧ |a i - b i| ≤ c i ∧ c i ≤ a i + b i)
    (hgood' : ∀ᶠ i in l,
      0 < k i ∧ 0 < a' i ∧ 0 < b' i ∧ |a' i - b' i| ≤ c' i ∧ c' i ≤ a' i + b' i)
    (hsmall : _root_.Filter.Tendsto (fun i => k i * _root_.Max.max (a i) (b i)) l (𝓝 0))
    (hsmall' : _root_.Filter.Tendsto (fun i => k i * _root_.Max.max (a' i) (b' i)) l (𝓝 0))
    (hlong : ∀ᶠ i in l, θ ≤ comparisonAngle (a i) (b i) (c i))
    (hangle : ∀ᶠ i in l,
      Real.arccos ((Real.cosh (k i * a i) * Real.cosh (k i * b i) - Real.cosh (k i * c i)) /
        (Real.sinh (k i * a i) * Real.sinh (k i * b i))) ≤
      Real.arccos ((Real.cosh (k i * a' i) * Real.cosh (k i * b' i) - Real.cosh (k i * c' i)) /
        (Real.sinh (k i * a' i) * Real.sinh (k i * b' i)))) :
    ∀ᶠ i in l, θ / 2 ≤ comparisonAngle (a' i) (b' i) (c' i) := by
  have hε : 0 < θ / 4 := by positivity
  have h1 := Metric.tendsto_nhds.mp
    (tendsto_hyperbolic_comparison_angle_sub_euclidean hgood hsmall) (θ / 4) hε
  have h2 := Metric.tendsto_nhds.mp
    (tendsto_hyperbolic_comparison_angle_sub_euclidean hgood' hsmall') (θ / 4) hε
  filter_upwards [hlong, hangle, h1, h2] with i hl ha he he'
  simp only [Real.dist_eq, sub_zero] at he he'
  have hb := abs_lt.mp he
  have hb' := abs_lt.mp he'
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.eventually_comparisonAngle_ge_half_of_hyperbolic_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.eventually_comparisonAngle_ge_half_of_hyperbolic_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.eventually_comparisonAngle_ge_half_of_hyperbolic_comparison ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.eventually_comparisonAngle_ge_half_of_hyperbolic_comparison

end DifferentialGeometry.Geometry.Comparison.Toponogov

end
