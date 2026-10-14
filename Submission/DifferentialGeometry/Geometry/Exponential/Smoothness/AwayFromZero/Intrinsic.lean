import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.NormDiamond
import Submission.DifferentialGeometry.Geometry.Exponential.Intrinsic.Velocity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Function _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E]
  [T2Space (TangentBundle I M)] in
theorem expChart_contDiffAt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : E) (y₀ : M)
    (hy : expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from v)
      ∈ (chartAt H y₀).source) :
    ContDiffAt ℝ ∞
      (fun b : E => extChartAt I y₀
        (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from b))) v := by
  have hexp : ContMDiffAt 𝓘(ℝ, E) I ∞
      (fun b : E => expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from b)) v :=
    (intrinsicFiber_smooth (I := I) g hEnorm p).contMDiffAt
  have hchart : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I y₀)
      (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from v)) :=
    (contMDiffOn_extChartAt (I := I) (n := ∞) (x := y₀)).contMDiffAt
      ((chartAt H y₀).open_source.mem_nhds hy)
  have hcomp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun b : E => extChartAt I y₀
        (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from b))) v :=
    hchart.comp v hexp
  exact contMDiffAt_iff_contDiffAt.mp hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.expChart_contDiffAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.expChart_contDiffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.expChart_contDiffAt ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.expChart_contDiffAt

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
