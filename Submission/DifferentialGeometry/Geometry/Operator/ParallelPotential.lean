import Submission.DifferentialGeometry.Geometry.Operator.JetComparison
import Submission.DifferentialGeometry.Geometry.Operator.GradientPerturbation
import Submission.DifferentialGeometry.Geometry.Operator.OrthonormalTrace
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open scoped _root_.Manifold _root_.ContDiff
namespace DifferentialGeometry.Geometry.Operator
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [I.Boundaryless] [BoundarylessManifold I M]
private local instance _root_.Submission.DifferentialGeometry.Geometry.Operator.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

theorem abs_laplacian_le_of_parallel_unit_gradient
    (g h : SmoothRiemannianMetric I M) (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (x : M) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 1 → metricDerivNorm k h g g x ≤ ε)
    (hunit : g.inner x (gradFun g u x) (gradFun g u x) = 1)
    (hparallel : ∀ v w : TangentSpace I x, hessFun g u x v w = 0) :
    |laplacian (LeviCivita h) h u x| ≤ 24 * (Module.finrank ℝ E : ℝ) * ε := by
  classical
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  obtain ⟨B, hB⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis h x
  have heq : MetricUniformEquivalentOn {x} g h 2 :=
    metricUniformEquivalentOn_of_metricDerivNorm_le_half {x} g h (by
      simpa using (hsmall 0 (by norm_num)).trans hε)
  have hb (i : Fin (Module.finrank ℝ E)) : |hessFun h u x (B i) (B i)| ≤ 24 * ε := by
    have hi : g.inner x (B i) (B i) ≤ 2 := by
      have ht := ((metricUniformEquivalentOn_symm heq).2 x (Set.mem_singleton x) (B i)).2
      have hBi : h.inner x (B i) (B i) = 1 := (hB i i).trans (if_pos rfl)
      simpa only [hBi, mul_one] using ht
    have ht := abs_hessFun_sub_le_of_small_metric_derivatives g h u hu x ε hε hsmall (B i) (B i)
    rw [hparallel, sub_zero, hunit, Real.sqrt_one, mul_one, mul_assoc,
      Real.mul_self_sqrt (metric_inner_self_nonneg g x (B i))] at ht
    exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_left hi hε0])
  rw [laplacian_eq_sum_hessFun h u hu x B hB]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i : Fin (Module.finrank ℝ E), 24 * ε := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.abs_laplacian_le_of_parallel_unit_gradient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.abs_laplacian_le_of_parallel_unit_gradient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.abs_laplacian_le_of_parallel_unit_gradient ``Submission.DifferentialGeometry.Geometry.Operator.abs_laplacian_le_of_parallel_unit_gradient

theorem abs_laplacian_comp_sub_le_of_parallel_unit_gradient
    (g h : SmoothRiemannianMetric I M) (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (x : M) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 1 → metricDerivNorm k h g g x ≤ ε)
    (hunit : g.inner x (gradFun g u x) (gradFun g u x) = 1)
    (hparallel : ∀ v w : TangentSpace I x, hessFun g u x v w = 0) :
    |laplacian (LeviCivita h) h (fun y => f (u y)) x - deriv (deriv f) (u x)| ≤
      2 * ε * |deriv (deriv f) (u x)| +
        24 * (Module.finrank ℝ E : ℝ) * ε * |deriv f (u x)| := by
  have hε0 : 0 ≤ ε := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have hε1 : ε < 1 := hε.trans_lt (by norm_num)
  have hd : 0 < 1 - ε := by linarith
  have hq : |h.inner x (gradFun h u x) (gradFun h u x) - 1| ≤ 2 * ε := by
    have hh := abs_inner_gradFun_sub_le_of_metricDerivNorm g h u x ε hε1
      (hsmall 0 (by norm_num))
    rw [hunit, mul_one] at hh
    apply hh.trans
    rw [div_le_iff₀ hd]
    nlinarith [mul_le_mul_of_nonneg_left hε hε0]
  have hL := abs_laplacian_le_of_parallel_unit_gradient g h u hu x ε hε hsmall hunit hparallel
  have hgrad : MDiffAt (T% fun y : M => gradientFun h u y) x := by
    simpa only [gradient_eq_gradFun] using
      (gradFun_contMDiff_total h hu).mdifferentiable (by simp) x
  have hf' := (contDiff_infty_iff_deriv.mp hf).2
  have hc := laplacian_comp (LeviCivita h) h (hf.differentiable (by simp))
    ((hf'.differentiable (by simp)) (u x)) (hu.mdifferentiable (by simp)) hgrad
  simp only [gradient_eq_gradFun] at hc
  have heq : laplacian (LeviCivita h) h (fun y => f (u y)) x - deriv (deriv f) (u x) =
      deriv (deriv f) (u x) * (h.inner x (gradFun h u x) (gradFun h u x) - 1) +
        deriv f (u x) * laplacian (LeviCivita h) h u x := by
    rw [hc]
    ring
  rw [heq]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul]
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left hq (abs_nonneg (deriv (deriv f) (u x))))
    (mul_le_mul_of_nonneg_left hL (abs_nonneg (deriv f (u x))))
  convert hh using 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.abs_laplacian_comp_sub_le_of_parallel_unit_gradient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.abs_laplacian_comp_sub_le_of_parallel_unit_gradient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.abs_laplacian_comp_sub_le_of_parallel_unit_gradient ``Submission.DifferentialGeometry.Geometry.Operator.abs_laplacian_comp_sub_le_of_parallel_unit_gradient

end DifferentialGeometry.Geometry.Operator
