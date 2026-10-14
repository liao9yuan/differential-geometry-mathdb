import Submission.DifferentialGeometry.Analysis.Convex.Tensor04SectionalNonnegativeCone
import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.SectionalCone
import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Analysis.Convex
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem tensor04SectionalEval_metricRm04At
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    tensor04SectionalEval (I := I) (M := M)
        (metricRm04At (I := I) (M := M) g x) v w =
      metricRm04StandardAt (I := I) (M := M) g x v w w v := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor04SectionalEval_metricRm04At then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor04SectionalEval_metricRm04At"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor04SectionalEval_metricRm04At ``Submission.DifferentialGeometry.Geometry.Curvature.tensor04SectionalEval_metricRm04At

omit [SigmaCompactSpace M] [T2Space M] in
theorem metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm04At (I := I) (M := M) g x ∈
        tensor04SectionalNonnegativeCone (I := I) (M := M) ↔
      ∀ v w : TangentSpace I x,
        0 ≤ metricRm04StandardAt (I := I) (M := M) g x v w w v := by
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricRm04At_mem_tensor04SectionalNonnegativeCone_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricRm04At_mem_tensor04SectionalNonnegativeCone_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricRm04At_mem_tensor04SectionalNonnegativeCone_iff ``Submission.DifferentialGeometry.Geometry.Curvature.metricRm04At_mem_tensor04SectionalNonnegativeCone_iff

omit [SigmaCompactSpace M] in
theorem metricRm04_mem_tensor04SectionalNonnegativeCone_iff
    (g : SmoothRiemannianMetric I M) :
    (∀ x : M, metricRm04 (I := I) (M := M) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) ↔
      ∀ x : M, ∀ v w : TangentSpace I x,
        0 ≤ metricRm04StandardAt (I := I) (M := M) g x v w w v := by
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricRm04_mem_tensor04SectionalNonnegativeCone_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricRm04_mem_tensor04SectionalNonnegativeCone_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricRm04_mem_tensor04SectionalNonnegativeCone_iff ``Submission.DifferentialGeometry.Geometry.Curvature.metricRm04_mem_tensor04SectionalNonnegativeCone_iff

omit [SigmaCompactSpace M] in
theorem metricAlgebraicCurvatureTensorAt_mem_algebraicSectionalNonnegativeCone_iff
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
        algebraicSectionalNonnegativeCone (I := I) (M := M) ↔
      ∀ v w : TangentSpace I x,
        0 ≤ metricRm04StandardAt (I := I) (M := M) g x v w w v := by
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_mem_algebraicSectionalNonnegativeCone_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_mem_algebraicSectionalNonnegativeCone_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_mem_algebraicSectionalNonnegativeCone_iff ``Submission.DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_mem_algebraicSectionalNonnegativeCone_iff

end DifferentialGeometry.Geometry.Curvature
