import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisIdentity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.Topology _root_.Manifold _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]



theorem sectionalCurvatureNumerator_eq_inner_chartRiemann
    (g : SmoothRiemannianMetric I M) (p : M) (v w : TangentSpace I p) :
    sectionalCurvatureNumerator g p v w = g.inner p v (chartRiemannCLM g p v w w) := by
  classical
  let b := DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) p
  have hrepr (X : TangentSpace I p) : b.repr X =
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr X := by
    simp [b, tangentSpaceModelContinuousLinearEquiv_apply]
  have hgram (l m : Fin (Module.finrank ℝ E)) :
      chartGramOnE g p l m (extChartAt I p p) = g.inner p (b l) (b m) := by
    rw [chartGramOnE_def, (extChartAt I p).left_inv (mem_extChartAt_source p),
      DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply,
      chartBasisVecFiber_self, chartBasisVecFiber_self]
  have hin (m : Fin (Module.finrank ℝ E)) :
      g.inner p v (b m) = ∑ l, b.repr v l * g.inner p (b l) (b m) := by
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, _root_.sum_apply, map_smul, _root_.smul_apply, smul_eq_mul]
  rw [chartRiemannCLM_apply]
  change sectionalCurvatureNumerator g p v w = g.inner p v
    (∑ i, ∑ j, ∑ k, ∑ m, (b.repr w i * b.repr v j * b.repr w k *
      chartRiemannTensor g p i j k m (extChartAt I p p)) • b m)
  simp only [map_sum, map_smul, smul_eq_mul]
  simp_rw [hin, Finset.mul_sum]
  rw [sectionalCurvatureNumerator_def]
  simp only [chartRiemannLower, Finset.mul_sum, hrepr]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  rw [hgram]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sectionalCurvatureNumerator_eq_inner_chartRiemann then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sectionalCurvatureNumerator_eq_inner_chartRiemann"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sectionalCurvatureNumerator_eq_inner_chartRiemann ``Submission.DifferentialGeometry.Geometry.sectionalCurvatureNumerator_eq_inner_chartRiemann




theorem sectionalCurvature_eq_riemann [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) (p : M) (v w : TangentSpace I p) :
    sectionalCurvature g p v w =
      g.inner p v (riemannOp (LeviCivita g) p v w w) /
        (g.inner p v v * g.inner p w w - (g.inner p v w) ^ 2) := by
  rw [sectionalCurvature_def, sectionalCurvatureNumerator_eq_inner_chartRiemann,
    sectionalCurvatureDenominator_def, riemannOp_eq_chartRiemannCLM_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sectionalCurvature_eq_riemann then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sectionalCurvature_eq_riemann"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sectionalCurvature_eq_riemann ``Submission.DifferentialGeometry.Geometry.sectionalCurvature_eq_riemann

end DifferentialGeometry.Geometry
