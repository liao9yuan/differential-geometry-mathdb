import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.InverseMetric
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Bounds
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open scoped _root_.Manifold _root_.ContDiff
namespace DifferentialGeometry.Geometry.Operator

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem inner_gradFun_le_of_metric_lower_bound
    (g h : SmoothRiemannianMetric I M) (F : M → ℝ) (x : M) (C : ℝ)
    (hbound : ∀ v : TangentSpace I x, g.inner x v v ≤ C * h.inner x v v) :
    h.inner x (gradFun h F x) (gradFun h F x) ≤
      C * g.inner x (gradFun g F x) (gradFun g F x) := by
  let u := gradFun h F x
  let v := gradFun g F x
  have hpair : g.inner x v u = h.inner x u u :=
    (inner_gradFun g F x u).trans (inner_gradFun h F x u).symm
  have hcs := metric_inner_cauchy_schwarz_sq g x v u
  rw [hpair] at hcs
  have hbound' := mul_le_mul_of_nonneg_left (hbound u) (metric_inner_self_nonneg g x v)
  have htotal := hcs.trans hbound'
  have hq := metric_inner_self_nonneg h x u
  change h.inner x u u ≤ C * g.inner x v v
  rcases eq_or_lt_of_le hq with hzero | hpos
  · have hu : u = 0 := by
      by_contra hne
      have h := h.pos x u hne
      linarith
    have hpzero : g.inner x v v = 0 := by
      have hd := (inner_gradFun g F x v).trans (inner_gradFun h F x v).symm
      change g.inner x v v = h.inner x u v at hd
      simpa only [hu, map_zero, zero_apply] using hd
    rw [← hzero, hpzero, _root_.MulZeroClass.mul_zero]
  · nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.inner_gradFun_le_of_metric_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.inner_gradFun_le_of_metric_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.inner_gradFun_le_of_metric_lower_bound ``Submission.DifferentialGeometry.Geometry.Operator.inner_gradFun_le_of_metric_lower_bound

theorem inner_gradFun_le_of_metricUniformEquivalentOn
    {K : Set M} (g h : SmoothRiemannianMetric I M) {C : ℝ}
    (heq : MetricUniformEquivalentOn K g h C) (F : M → ℝ) {x : M} (hx : x ∈ K) :
    h.inner x (gradFun h F x) (gradFun h F x) ≤
      C * g.inner x (gradFun g F x) (gradFun g F x) := by
  apply inner_gradFun_le_of_metric_lower_bound
  exact fun v => ((metricUniformEquivalentOn_symm heq).2 x hx v).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.inner_gradFun_le_of_metricUniformEquivalentOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.inner_gradFun_le_of_metricUniformEquivalentOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.inner_gradFun_le_of_metricUniformEquivalentOn ``Submission.DifferentialGeometry.Geometry.Operator.inner_gradFun_le_of_metricUniformEquivalentOn

variable [T2Space M] [I.Boundaryless] [BoundarylessManifold I M]

theorem hessFun_sub_eq_connectionDifference
    (g h : SmoothRiemannianMetric I M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (x : M) (v w : TangentSpace I x) :
    hessFun h F x v w - hessFun g F x v w =
      -mvfderiv I F x (PDE.DeTurck.connectionDifference h g x w v) := by
  rw [hessFun_eq_abstract h hF x v w, hessFun_eq_abstract g hF x v w]
  exact cotangentCov_leviCivita_connectionDifference g h
    (((cotangentCov_mvfderiv_smooth hF) x).mdifferentiableAt (by simp)) v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.hessFun_sub_eq_connectionDifference then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.hessFun_sub_eq_connectionDifference"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.hessFun_sub_eq_connectionDifference ``Submission.DifferentialGeometry.Geometry.Operator.hessFun_sub_eq_connectionDifference

theorem abs_hessFun_sub_le_of_connectionDifference_bound
    (g h : SmoothRiemannianMetric I M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (x : M) (v w : TangentSpace I x) (C : ℝ)
    (hbound : let A := PDE.DeTurck.connectionDifference h g x w v
      Real.sqrt (g.inner x A A) ≤
        C * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w)) :
    |hessFun h F x v w - hessFun g F x v w| ≤
      C * Real.sqrt (g.inner x (gradFun g F x) (gradFun g F x)) *
        Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
  have hdual : g.inner x (gradFun g F x)
      (PDE.DeTurck.connectionDifference h g x w v) =
      mvfderiv I F x (PDE.DeTurck.connectionDifference h g x w v) :=
    inner_gradFun g F x _
  rw [hessFun_sub_eq_connectionDifference g h F hF x v w, abs_neg, ← hdual]
  apply (abs_metric_inner_le_sqrt_metric_quadratic g x _ _).trans
  have hh := mul_le_mul_of_nonneg_left hbound
    (Real.sqrt_nonneg (g.inner x (gradFun g F x) (gradFun g F x)))
  convert hh using 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.abs_hessFun_sub_le_of_connectionDifference_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.abs_hessFun_sub_le_of_connectionDifference_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.abs_hessFun_sub_le_of_connectionDifference_bound ``Submission.DifferentialGeometry.Geometry.Operator.abs_hessFun_sub_le_of_connectionDifference_bound

end DifferentialGeometry.Geometry.Operator
