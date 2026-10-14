import Submission.DifferentialGeometry.Geometry.Geodesic.Maximal.Interval

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

section Homogeneity

variable [I.Boundaryless] [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem maximalGeodesic_smul_zero_time
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (c : ℝ) :
    maximalGeodesic (I := I) g p (c • v) 0 = p :=
  maximalGeodesic_zero (I := I) g p (c • v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_smul_zero_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_smul_zero_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_smul_zero_time ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_smul_zero_time

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E] in
theorem maximalGeodesic_one_velocity
    (g : SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) (t : ℝ) :
    maximalGeodesic (I := I) g p ((1 : ℝ) • v) t =
      maximalGeodesic (I := I) g p v t := by
  rw [one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_one_velocity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_one_velocity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_one_velocity ``Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic.maximalGeodesic_one_velocity

end Homogeneity

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

end
