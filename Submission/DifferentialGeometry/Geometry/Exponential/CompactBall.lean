import Submission.DifferentialGeometry.Geometry.Comparison.HopfRinow.CompactBall
import Submission.DifferentialGeometry.Geometry.Geodesic.Flow.VelocityLift
import Submission.DifferentialGeometry.Geometry.Exponential.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem mem_expDomain_of_isCompact_closedEBall
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (v : TangentSpace I x) {r : ℝ}
    (hv : Real.sqrt (g.inner x v v) < r)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall x (ENNReal.ofReal r))) :
    v ∈ expDomain (I := I) g x := by
  obtain ⟨gamma, J, hJ_open, hJ_conn, h0, h1, hgeo, hcont, hgamma0, hvel⟩ :=
    exists_isGeodesicOn_of_isCompact_closedEBall (I := I) g hEnorm x v hv hcpt
  have hlift0 :
      velocityLift (I := I) gamma 0 =
        (⟨x, v⟩ : TangentBundle I M) := by
    apply TotalSpace.ext hgamma0
    exact heq_of_eq hvel
  have hinit : IsGeodesicOnWithInitial (I := I) g gamma J x v :=
    ⟨velocityLift (I := I) gamma, DifferentialGeometry.velocityLift_proj (I := I) gamma,
      hlift0, isMIntegralCurveOn_velocityLift (I := I) g hJ_open hgeo hcont⟩
  rw [mem_expDomain_iff]
  exact ⟨gamma, J, hJ_open, hJ_conn, h0, h1, hinit⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.mem_expDomain_of_isCompact_closedEBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.mem_expDomain_of_isCompact_closedEBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.mem_expDomain_of_isCompact_closedEBall ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.mem_expDomain_of_isCompact_closedEBall

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
