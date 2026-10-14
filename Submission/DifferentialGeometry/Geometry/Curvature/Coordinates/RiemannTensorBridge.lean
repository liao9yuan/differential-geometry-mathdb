import Submission.DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisIdentity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

open _root_.CovariantDerivative _root_.Submission.CovariantDerivative _root_.Submission.DifferentialGeometry.Geometry.Curvature.CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricRm04StandardAt_eq_chartRiemannCLM
    (g : SmoothRiemannianMetric I M) (x : M) (X Y Z W : TangentSpace I x) :
    metricRm04StandardAt (I := I) g x X Y Z W
      = g.inner x W (chartRiemannCLM (I := I) g x X Y Z) := by
  rw [metricRm04StandardAt_apply,
    show metricRm04At (I := I) g x
        = riemannCurvature04At g (metricCov (I := I) g) (metricCov_smooth (I := I) g) x from rfl,
    riemannCurvature04At_apply_const]
  have : _root_.CovariantDerivative.ContMDiffCovariantDerivative (metricCov (I := I) g) ∞ := LeviCivita_isContMDiff g
  rw [connectionRiemannCurvatureField_tangentConst_eq_riemannOp (metricCov (I := I) g)
      (metricCov_smooth (I := I) g) x X Y Z,
    show riemannOp (cov := metricCov (I := I) g) x X Y Z
        = riemannOp (cov := LeviCivita (I := I) g) x X Y Z from rfl,
    riemannOp_eq_chartRiemannCLM_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.metricRm04StandardAt_eq_chartRiemannCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.metricRm04StandardAt_eq_chartRiemannCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.metricRm04StandardAt_eq_chartRiemannCLM ``Submission.DifferentialGeometry.metricRm04StandardAt_eq_chartRiemannCLM

omit [InnerProductSpace ℝ E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem rm04_eq_inner_riem
    (g : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    metricRm04StandardAt (I := I) g x X Y Z W =
      g.inner x W (riemannOp (cov := LeviCivita (I := I) g) x X Y Z) := by
  rw [metricRm04StandardAt_eq_chartRiemannCLM,
    riemannOp_eq_chartRiemannCLM_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.rm04_eq_inner_riem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.rm04_eq_inner_riem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.rm04_eq_inner_riem ``Submission.DifferentialGeometry.rm04_eq_inner_riem

end DifferentialGeometry

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem metricScalarAt_eq_zero_of_metricRm04At_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (hRm : metricRm04At (I := I) g x = 0) :
    metricScalarAt (I := I) g x = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  have hOp (u v w : TangentSpace I x) :
      riemannOp (LeviCivita (I := I) g) x u v w = 0 := by
    let R := riemannOp (LeviCivita (I := I) g) x u v w
    have hinner : g.inner x R R = 0 := by
      rw [← DifferentialGeometry.rm04_eq_inner_riem (I := I) g x u v w R]
      rw [metricRm04StandardAt_apply, hRm]
      rfl
    by_contra hR
    exact (ne_of_gt (g.pos x R hR)) hinner
  apply metricScalarAt_eq_zero_of_ricciTensor_eq_zero (I := I) g x
  intro v w
  have hEndo : ricciEndo (I := I) g x v w = 0 := by
    ext u
    exact hOp u v w
  rw [ricciTensor_apply, hEndo, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricScalarAt_eq_zero_of_metricRm04At_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricScalarAt_eq_zero_of_metricRm04At_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricScalarAt_eq_zero_of_metricRm04At_eq_zero ``Submission.DifferentialGeometry.Geometry.Curvature.metricScalarAt_eq_zero_of_metricRm04At_eq_zero

end DifferentialGeometry.Geometry.Curvature
