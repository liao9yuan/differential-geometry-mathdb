import Submission.DifferentialGeometry.Geometry.Metric.FamilySectionPairing
import Submission.DifferentialGeometry.Geometry.Metric.ParameterDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



theorem contMDiffAt_metricFamilyQuadratic
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    (p : TangentBundle 𝓘(ℝ, E) M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M => (G q.1).inner q.2.proj q.2.2 q.2.2) (t, p) := by
  have hbase : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) 𝓘(ℝ, E) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M => q.2.proj) (t, p) :=
    (_root_.Bundle.contMDiffAt_proj (IB := 𝓘(ℝ, E)) (TangentSpace 𝓘(ℝ, E))).comp (t, p) contMDiffAt_snd
  have hV : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E)))
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M => TotalSpace.mk' E q.2.proj q.2.2) (t, p) := by
    exact contMDiffAt_snd
  exact contMDiffAt_metricFamilySectionPairing hG contMDiffAt_fst hbase ht hV hV

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.contMDiffAt_metricFamilyQuadratic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.contMDiffAt_metricFamilyQuadratic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.contMDiffAt_metricFamilyQuadratic ``Submission.DifferentialGeometry.Geometry.contMDiffAt_metricFamilyQuadratic



theorem continuousAt_metricFamilyQuadratic_deriv
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    (p : TangentBundle 𝓘(ℝ, E) M) :
    ContinuousAt (fun q : ℝ × TangentBundle 𝓘(ℝ, E) M =>
      deriv (fun r => (G r).inner q.2.proj q.2.2 q.2.2) q.1) (t, p) :=
  (contMDiffAt_deriv_fst (contMDiffAt_metricFamilyQuadratic hG ht p)).continuousAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.continuousAt_metricFamilyQuadratic_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.continuousAt_metricFamilyQuadratic_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.continuousAt_metricFamilyQuadratic_deriv ``Submission.DifferentialGeometry.Geometry.continuousAt_metricFamilyQuadratic_deriv

end DifferentialGeometry.Geometry
