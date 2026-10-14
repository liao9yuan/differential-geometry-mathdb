import Submission.DifferentialGeometry.Geometry.Curvature.BivectorDifferential
import Submission.DifferentialGeometry.Geometry.Operator.HessianComposition
import Submission.DifferentialGeometry.Geometry.Operator.ParallelPotential
import Submission.DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.ContDiff _root_.InnerProductSpace
namespace DifferentialGeometry.Geometry.Curvature
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.E3 target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
theorem sq_mvfderiv_bivectorNormal_eq_normalize
    (u : M → ℝ) (x : M) (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (c : E3) :
    (mvfderiv I u x (bivectorNormalAt x B c)) ^ 2 =
      ‖bivectorDifferentialAt u x B‖ ^ 2 *
        ⟪NormedSpace.normalize (bivectorDifferentialAt u x B), c⟫_ℝ ^ 2 := by
  rw [← inner_bivectorDifferentialAt]
  have he : ⟪bivectorDifferentialAt u x B, c⟫_ℝ =
      ‖bivectorDifferentialAt u x B‖ *
        ⟪NormedSpace.normalize (bivectorDifferentialAt u x B), c⟫_ℝ := by
    rw [← real_inner_smul_left, NormedSpace.norm_smul_normalize]
  rw [he, mul_pow]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.sq_mvfderiv_bivectorNormal_eq_normalize then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.sq_mvfderiv_bivectorNormal_eq_normalize"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.sq_mvfderiv_bivectorNormal_eq_normalize ``Submission.DifferentialGeometry.Geometry.Curvature.sq_mvfderiv_bivectorNormal_eq_normalize

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem differential_comp (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y => f (u y)) x v = deriv f (u x) * mvfderiv I u x v := by
  have hd := (hf.differentiable (by simp)) (u x)
  have h := mvfderiv_comp_apply (I := 𝓘(ℝ)) (I' := I)
    (f := u) (g := f) x hd.mdifferentiableAt (hu.mdifferentiable (by simp) x) v
  rw [mvfderiv_real_model_eq_fderiv, hd.hasDerivAt.hasFDerivAt.fderiv,
    ← mvfderiv_real_eq_mfderiv I u x v] at h
  simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, mul_comm] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.differential_comp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.differential_comp target :: scope.openDecls } }

variable [I.Boundaryless] [BoundarylessManifold I M]

omit [T2Space M] [BoundarylessManifold I M] in
private theorem laplacian_comp_eq (h : SmoothRiemannianMetric I M)
    (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (x : M) :
    laplacian (LeviCivita h) h (fun y => f (u y)) x =
      deriv (deriv f) (u x) * h.inner x (gradFun h u x) (gradFun h u x) +
        deriv f (u x) * laplacian (LeviCivita h) h u x := by
  have hgrad : MDiffAt (T% fun y : M => gradientFun h u y) x := by
    simpa only [gradient_eq_gradFun] using
      (gradFun_contMDiff_total h hu).mdifferentiable (by simp) x
  have hf' := (contDiff_infty_iff_deriv.mp hf).2
  have hc := laplacian_comp (LeviCivita h) h (hf.differentiable (by simp))
    ((hf'.differentiable (by simp)) (u x)) (hu.mdifferentiable (by simp)) hgrad
  simpa only [gradient_eq_gradFun, add_comm] using hc

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.laplacian_comp_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.laplacian_comp_eq target :: scope.openDecls } }

theorem traceNormalizedCurvatureOperatorAt_comp_increment
    (h : SmoothRiemannianMetric I M) (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (x : M)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (hB : OrthonormalBasisAt h x B)
    (c : E3) :
    let q := bivectorDifferentialAt u x B
    let N := bivectorNormalAt x B c
    let t := Real.exp (-(2 * f (u x)))
    ⟪traceNormalizedCurvatureOperatorAt
      (conformalMetricOfContDiff h (fun y => f (u y)) (hf.contMDiff.comp hu)) x
      (conformalBasisAt (fun y => f (u y)) x B) c, c⟫_ℝ -
      t * ⟪traceNormalizedCurvatureOperatorAt h x B c, c⟫_ℝ =
        2 * t * (-deriv (deriv f) (u x) *
          (‖q‖ ^ 2 * ‖c‖ ^ 2 - (mvfderiv I u x N) ^ 2) +
          deriv f (u x) * (hessFun h u x N N - laplacian (LeviCivita h) h u x * ‖c‖ ^ 2) -
          (deriv f (u x)) ^ 2 * (mvfderiv I u x N) ^ 2) := by
  dsimp only
  rw [traceNormalizedCurvatureOperatorAt_conformal_inner_self h _ _ x B hB c,
    hessFun_comp h hf hu, laplacian_comp_eq h u hu f hf x,
    differential_comp u hu f hf x, ← norm_sq_bivectorDifferentialAt h u x B hB]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.traceNormalizedCurvatureOperatorAt_comp_increment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.traceNormalizedCurvatureOperatorAt_comp_increment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.traceNormalizedCurvatureOperatorAt_comp_increment ``Submission.DifferentialGeometry.Geometry.Curvature.traceNormalizedCurvatureOperatorAt_comp_increment

private theorem remainder_lower (D p s Q z X ε : ℝ)
    (hz : z ≤ 2 * Q) (hX : |X| ≤ 96 * ε * Q) :
    D * (s * Q - z) - (96 * ε * |p| + 2 * p ^ 2) * Q ≤
      D * (s * Q - z) + p * X - p ^ 2 * z := by
  have hp : |p * X| ≤ 96 * ε * |p| * Q := by
    rw [abs_mul]
    calc
      _ ≤ |p| * (96 * ε * Q) := mul_le_mul_of_nonneg_left hX (abs_nonneg p)
      _ = _ := by ring
  have hl := (abs_le.mp hp).1
  have hq := mul_le_mul_of_nonneg_left hz (sq_nonneg p)
  nlinarith only [hl, hq]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.remainder_lower
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.remainder_lower target :: scope.openDecls } }

theorem traceNormalizedCurvatureOperatorAt_comp_increment_lower
    (g h : SmoothRiemannianMetric I M) (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (x : M) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 1 → metricDerivNorm k h g g x ≤ ε)
    (hunit : g.inner x (gradFun g u x) (gradFun g u x) = 1)
    (hparallel : ∀ v w : TangentSpace I x, hessFun g u x v w = 0)
    (B : Module.Basis (Fin 3) ℝ (TangentSpace I x)) (hB : OrthonormalBasisAt h x B)
    (c : E3) :
    let q := bivectorDifferentialAt u x B
    let v := NormedSpace.normalize q
    let s := ‖q‖ ^ 2
    let t := Real.exp (-(2 * f (u x)))
    let D := -deriv (deriv f) (u x)
    let p := deriv f (u x)
    2 * t * D * s * (‖c‖ ^ 2 - ⟪v, c⟫_ℝ ^ 2) -
      2 * t * (96 * ε * |p| + 2 * p ^ 2) * ‖c‖ ^ 2 ≤
      ⟪traceNormalizedCurvatureOperatorAt
        (conformalMetricOfContDiff h (fun y => f (u y)) (hf.contMDiff.comp hu)) x
        (conformalBasisAt (fun y => f (u y)) x B) c, c⟫_ℝ -
        t * ⟪traceNormalizedCurvatureOperatorAt h x B c, c⟫_ℝ := by
  let N := bivectorNormalAt x B c
  let q := bivectorDifferentialAt u x B
  let v := NormedSpace.normalize q
  have hd : Module.finrank ℝ E = 3 := by
    change Module.finrank ℝ (TangentSpace I x) = 3
    simpa using Module.finrank_eq_card_basis B
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hn : h.inner x N N = ‖c‖ ^ 2 := bivectorNormalAt_inner_self h x B hB c
  have hg0 : 0 ≤ g.inner x N N := metric_inner_self_nonneg g x N
  have heq : MetricUniformEquivalentOn {x} g h 2 :=
    metricUniformEquivalentOn_of_metricDerivNorm_le_half {x} g h (by
      simpa using (hsmall 0 (by norm_num)).trans hε)
  have hg : g.inner x N N ≤ 2 * ‖c‖ ^ 2 := by
    simpa only [hn] using ((metricUniformEquivalentOn_symm heq).2 x (Set.mem_singleton x) N).2
  have hH : |hessFun h u x N N| ≤ 24 * ε * ‖c‖ ^ 2 := by
    have hb := abs_hessFun_sub_le_of_small_metric_derivatives g h u hu x ε hε hsmall N N
    rw [hparallel, sub_zero, hunit, Real.sqrt_one, mul_one, mul_assoc,
      Real.mul_self_sqrt hg0] at hb
    have hm := mul_le_mul_of_nonneg_left hg hε0
    nlinarith only [hb, hm]
  have hL : |laplacian (LeviCivita h) h u x| ≤ 72 * ε := by
    have hb := abs_laplacian_le_of_parallel_unit_gradient g h u hu x ε hε hsmall hunit hparallel
    rw [hd] at hb
    norm_num only [Nat.cast_ofNat] at hb
    convert hb using 1
  have hX : |hessFun h u x N N - laplacian (LeviCivita h) h u x * ‖c‖ ^ 2| ≤
      96 * ε * ‖c‖ ^ 2 := by
    have hb := abs_add_le (hessFun h u x N N) (-(laplacian (LeviCivita h) h u x * ‖c‖ ^ 2))
    rw [abs_neg, abs_mul, abs_of_nonneg (sq_nonneg ‖c‖)] at hb
    have hm := mul_le_mul_of_nonneg_right hL (sq_nonneg ‖c‖)
    change |hessFun h u x N N - laplacian (LeviCivita h) h u x * ‖c‖ ^ 2| ≤ _ at hb
    nlinarith only [hb, hH, hm]
  have hv : ‖v‖ = 1 :=
    (normalize_bivectorDifferentialAt_spec g h u x B hB hunit ε hε (hsmall 0 (by norm_num))).1
  have hs : ‖q‖ ^ 2 ≤ 2 := by
    have hb := inner_gradFun_le_two_of_metricDerivNorm_le_half g h u x
      ((hsmall 0 (by norm_num)).trans hε)
    rw [hunit, mul_one, ← norm_sq_bivectorDifferentialAt h u x B hB] at hb
    exact hb
  have hc : ⟪v, c⟫_ℝ ^ 2 ≤ ‖c‖ ^ 2 := by
    have hb := abs_real_inner_le_norm v c
    rw [hv, one_mul] at hb
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hb
  have hz : (mvfderiv I u x N) ^ 2 ≤ 2 * ‖c‖ ^ 2 := by
    rw [sq_mvfderiv_bivectorNormal_eq_normalize]
    exact (mul_le_mul_of_nonneg_left hc (sq_nonneg ‖q‖)).trans
      (mul_le_mul_of_nonneg_right hs (sq_nonneg ‖c‖))
  have hb := remainder_lower (-deriv (deriv f) (u x)) (deriv f (u x))
    (‖q‖ ^ 2) (‖c‖ ^ 2) ((mvfderiv I u x N) ^ 2)
    (hessFun h u x N N - laplacian (LeviCivita h) h u x * ‖c‖ ^ 2) ε hz hX
  have ht : 0 ≤ 2 * Real.exp (-(2 * f (u x))) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hb ht
  dsimp only
  rw [traceNormalizedCurvatureOperatorAt_comp_increment h u hu f hf x B hB c]
  have hnormal := sq_mvfderiv_bivectorNormal_eq_normalize u x B c
  change (mvfderiv I u x N) ^ 2 = ‖q‖ ^ 2 * ⟪v, c⟫_ℝ ^ 2 at hnormal
  rw [hnormal] at hscaled
  rw [sq_mvfderiv_bivectorNormal_eq_normalize]
  dsimp only [N, q, v] at hscaled
  nlinarith only [hscaled]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.traceNormalizedCurvatureOperatorAt_comp_increment_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.traceNormalizedCurvatureOperatorAt_comp_increment_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.traceNormalizedCurvatureOperatorAt_comp_increment_lower ``Submission.DifferentialGeometry.Geometry.Curvature.traceNormalizedCurvatureOperatorAt_comp_increment_lower

end DifferentialGeometry.Geometry.Curvature
