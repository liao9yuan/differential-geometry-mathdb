import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Basic
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.InverseMetric
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry.Geometry.Connection

open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem chartInvGram_inverse
    (g : SmoothRiemannianMetric I M) (alpha : M) {x : M}
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) alpha).baseSet) :
    MetricInverseInBasis (I := I) g x
      (DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) alpha hx)
      (fun i j => chartInvGramMatrix (I := I) g alpha x i j) := by
  classical
  have hgram : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) alpha hx i)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) alpha hx j) =
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g alpha x i j := by
    intro i j
    rw [DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_apply, DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_apply]
    exact (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply (I := I) g alpha x i j).symm
  intro i j
  refine ⟨?_, ?_⟩
  · simp only [hgram]
    rw [← Matrix.mul_apply,
      chartInvGramMatrix_mul_chartGramMatrix (I := I) g alpha hx,
      Matrix.one_apply]
  · simp only [hgram]
    rw [← Matrix.mul_apply,
      chartGramMatrix_mul_chartInvGramMatrix (I := I) g alpha hx,
      Matrix.one_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartInvGram_inverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartInvGram_inverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartInvGram_inverse ``Submission.DifferentialGeometry.Geometry.Connection.chartInvGram_inverse

end DifferentialGeometry.Geometry.Connection
