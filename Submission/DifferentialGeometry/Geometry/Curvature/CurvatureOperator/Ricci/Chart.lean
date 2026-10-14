import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.MetricSharpSmoothness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem ricciSharp_chart
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)
    (v : TangentSpace I x) :
    trivToE (I := I) α x (ricciSharp (I := I) g x v) =
      ∑ i : Fin (Module.finrank ℝ E),
        (∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g α x i j *
            ∑ k : Fin (Module.finrank ℝ E),
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (trivToE (I := I) α x v)) k *
                ricciTensor (I := I) g x
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x)
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x)) •
          DifferentialGeometry.Tensor.Coordinates.chartModelBasis E i := by
  classical
  let cv : ∀ y : M, TangentSpace I y →ₗ[ℝ] ℝ := fun y ↦
    (ricciTensor (I := I) g y
      (trivFromE (I := I) α y (trivToE (I := I) α x v))).toLinearMap
  have hsharp := trivToE_metricSharp (I := I) g α cv hx
  rw [ricciSharp_apply]
  change trivToE (I := I) α x
      (metricSharp (I := I) g x ((ricciTensor (I := I) g x v).toLinearMap)) = _
  have hv : trivFromE (I := I) α x (trivToE (I := I) α x v) = v :=
    trivFromE_trivToE (I := I) α hx v
  have hcvx : cv x = (ricciTensor (I := I) g x v).toLinearMap := by
    simp only [cv, hv]
  rw [← hcvx]
  rw [hsharp]
  have hrec := chartBasisVecFiber_recompose (I := I) α hx v
  have hcomponent (j : Fin (Module.finrank ℝ E)) :
      ricciTensor (I := I) g x v (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x) =
        ∑ k : Fin (Module.finrank ℝ E),
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (trivToE (I := I) α x v)) k *
            ricciTensor (I := I) g x
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x)
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x) := by
    conv_lhs => rw [hrec]
    rw [map_sum, sum_apply]
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    rw [map_smul, smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  congr 1
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  congr 1
  rw [hcvx]
  exact hcomponent j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciSharp_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciSharp_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciSharp_chart ``Submission.DifferentialGeometry.Geometry.Curvature.ricciSharp_chart

end Curvature
end Geometry
end DifferentialGeometry
