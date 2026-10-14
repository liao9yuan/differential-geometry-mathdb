import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Analysis.Real.Sqrt

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Manifold _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Integral
namespace L2


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def covariantTensorInnerPointwise :
    (s : ℕ) → SmoothRiemannianMetric I M → (x : M) →
      ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ →
      ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ → ℝ
  | 0, _g, _x, S, T =>
      S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i)
  | s + 1, g, x, S, T =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          covariantTensorInnerPointwise s g x
            (S.curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
            (T.curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.covariantTensorInnerPointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.covariantTensorInnerPointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.covariantTensorInnerPointwise ``Submission.DifferentialGeometry.Integral.L2.covariantTensorInnerPointwise

lemma tensorInnerPointwise_0s_zero_arity
    (g : SmoothRiemannianMetric I M) (x : M)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) 0 g x S T =
      S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorInnerPointwise_0s_zero_arity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorInnerPointwise_0s_zero_arity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorInnerPointwise_0s_zero_arity ``Submission.DifferentialGeometry.Integral.L2.tensorInnerPointwise_0s_zero_arity

lemma tensorInnerPointwise_0s_succ
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) (s + 1) g x S T =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          covariantTensorInnerPointwise (I := I) (M := M) s g x
            (S.curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
            (T.curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorInnerPointwise_0s_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorInnerPointwise_0s_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorInnerPointwise_0s_succ ``Submission.DifferentialGeometry.Integral.L2.tensorInnerPointwise_0s_succ

noncomputable def tensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S T : TensorRSModel r s ℝ E) : ℝ :=
  covariantTensorInnerPointwise (I := I) (M := M) (r + s) g x
    (lowerAllUpperIndices (I := I) (M := M) g r s x S)
    (lowerAllUpperIndices (I := I) (M := M) g r s x T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorInnerPointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorInnerPointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorInnerPointwise ``Submission.DifferentialGeometry.Integral.L2.tensorInnerPointwise

noncomputable def tensorPointwiseNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (S : TensorRSModel r s ℝ E) : ℝ :=
  Real.sqrt (tensorInnerPointwise (I := I) (M := M) g r s x S S)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorPointwiseNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorPointwiseNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorPointwiseNorm ``Submission.DifferentialGeometry.Integral.L2.tensorPointwiseNorm

end L2
end Integral
end DifferentialGeometry

end
