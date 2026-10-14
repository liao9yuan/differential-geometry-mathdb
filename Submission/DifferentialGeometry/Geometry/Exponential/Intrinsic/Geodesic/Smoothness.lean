import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.NormDiamond
import Submission.DifferentialGeometry.Geometry.Geodesic.Chart.Regularity
import Submission.DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [ConnectedSpace M] in
theorem intrinsicGeodesic_contMDiffOn_infty
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (intrinsicGeodesic (I := I) g hEnorm p v)
      Set.univ := by
  refine isGeodesicOn_contMDiffOn_infty (I := I) g isOpen_univ ?_ ?_
  · exact (intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v).isGeodesicOn
      Set.univ
  · exact (intrinsicGeodesic_continuous (I := I) g hEnorm p v).continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_contMDiffOn_infty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_contMDiffOn_infty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_contMDiffOn_infty ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_contMDiffOn_infty

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [ConnectedSpace M] in
theorem intrinsicGeodesic_contMDiff
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ (intrinsicGeodesic (I := I) g hEnorm p v) :=
  contMDiffOn_univ.mp
    (intrinsicGeodesic_contMDiffOn_infty (I := I) g hEnorm p v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_contMDiff ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.intrinsicGeodesic_contMDiff

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
