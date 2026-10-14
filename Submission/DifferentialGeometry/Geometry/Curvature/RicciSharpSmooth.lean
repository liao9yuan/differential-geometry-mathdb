import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.MetricSharpSmoothness
import Submission.DifferentialGeometry.Bundle.ContinuousLinearMapSection.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry.Geometry.Curvature

theorem ricciSharp_contMDiff
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M] (g : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x (ricciSharp g x)) := by
  apply DifferentialGeometry.contMDiff_continuousLinearMap_section_of_apply (φ := ricciSharp g)
  intro Y
  change ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
    (fun x : M ↦ TotalSpace.mk' E x (metricSharp g x (ricciTensor g x (Y x)).toLinearMap))
  apply metricSharp_contMDiff_total g
  intro α j
  have hb := DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) α j
  rw [TangentBundle.trivializationAt_baseSet] at hb
  have ht : ContMDiffOn I (I.prod 𝓘(ℝ)) ∞
      (fun x : M ↦ TotalSpace.mk' ℝ (E := fun _ : M ↦ ℝ) x
        (ricciTensor g x (Y x)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x)))
        (chartAt H α).source :=
    ContMDiffOn.clm_bundle_apply₂ (E₁ := TangentSpace I) (E₂ := TangentSpace I)
      (E₃ := fun _ : M ↦ ℝ) (b := id) (ψ := ricciTensor g)
      (v := fun x ↦ Y x)
      (w := DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j)
      (ricciTensor_contMDiff g).contMDiffOn Y.contMDiff.contMDiffOn hb
  intro x hx
  exact (contMDiffWithinAt_totalSpace.mp (ht x hx)).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciSharp_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciSharp_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciSharp_contMDiff ``Submission.DifferentialGeometry.Geometry.Curvature.ricciSharp_contMDiff

end DifferentialGeometry.Geometry.Curvature
