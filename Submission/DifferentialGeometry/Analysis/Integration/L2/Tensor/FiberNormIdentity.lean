import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Inner
import Submission.DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem tensorL2Norm_sq_eq_integral_riemannianFiberNormSq
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : ∀ x, TensorRSSpace r s I x) :
    tensorL2Norm (I := I) (M := M) g r s
          (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
            (r := r) (s := s) (x := x) (T x)) ^ 2
      = ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (T x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [tensorL2Norm_def, Real.sq_sqrt (by
        unfold tensorL2Inner
        refine _root_.MeasureTheory.integral_nonneg (fun x => ?_)
        exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s x _)]
  unfold tensorL2Inner
  refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  exact (riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (T x)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.tensorL2Norm_sq_eq_integral_riemannianFiberNormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.tensorL2Norm_sq_eq_integral_riemannianFiberNormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.tensorL2Norm_sq_eq_integral_riemannianFiberNormSq ``Submission.DifferentialGeometry.Analysis.Elliptic.tensorL2Norm_sq_eq_integral_riemannianFiberNormSq

end Elliptic
end Analysis
end DifferentialGeometry

end
