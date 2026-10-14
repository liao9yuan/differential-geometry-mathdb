import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import Mathlib.Data.Real.Pointwise

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators _root_.Pointwise
namespace DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private theorem actual_curvature_quadratic_scale
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (x : M)
    {n : ℕ} (a : Fin n → ℝ) (v w : Fin n → TangentSpace I x) :
    algebraicCurvatureOperatorQuadraticEval
        (metricAlgebraicCurvatureTensorAt (scaleMetric c hc g) x) a v w =
      c * algebraicCurvatureOperatorQuadraticEval (metricAlgebraicCurvatureTensorAt g x) a v w := by
  change (∑ i, ∑ j, a i * a j * metricRm04StandardAt (scaleMetric c hc g) x
      (v i) (w i) (w j) (v j)) =
    c * ∑ i, ∑ j, a i * a j * metricRm04StandardAt g x (v i) (w i) (w j) (v j)
  simp_rw [metricRmStandard_scale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.actual_curvature_quadratic_scale
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.actual_curvature_quadratic_scale target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem actual_identity_quadratic_scale
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (x : M)
    {n : ℕ} (a : Fin n → ℝ) (v w : Fin n → TangentSpace I x) :
    algebraicCurvatureIdentityQuadraticEval (scaleMetric c hc g) a v w =
      c ^ 2 * algebraicCurvatureIdentityQuadraticEval g a v w := by
  unfold algebraicCurvatureIdentityQuadraticEval
  simp_rw [scaleMetric_inner]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.actual_identity_quadratic_scale
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.actual_identity_quadratic_scale target :: scope.openDecls } }

theorem curvatureOperatorLowerBoundAt_scaleMetric_iff
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (x : M) (K : ℝ) :
    curvatureOperatorLowerBoundAt (scaleMetric c hc g) x
        (metricAlgebraicCurvatureTensorAt (scaleMetric c hc g) x) K ↔
      curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) (c * K) := by
  have hquad (n : ℕ) (a : Fin n → ℝ) (v w : Fin n → TangentSpace I x) :
      algebraicCurvatureOperatorQuadraticEval
          (metricAlgebraicCurvatureTensorAt (scaleMetric c hc g) x) a v w +
        K * algebraicCurvatureIdentityQuadraticEval (scaleMetric c hc g) a v w =
      c * (algebraicCurvatureOperatorQuadraticEval (metricAlgebraicCurvatureTensorAt g x) a v w +
        (c * K) * algebraicCurvatureIdentityQuadraticEval g a v w) := by
    rw [actual_curvature_quadratic_scale, actual_identity_quadratic_scale]
    ring
  constructor
  · intro h n a v w
    have hh := h n a v w
    rw [hquad] at hh
    exact nonneg_of_mul_nonneg_right hh hc
  · intro h n a v w
    rw [hquad]
    exact mul_nonneg hc.le (h n a v w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_scaleMetric_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_scaleMetric_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_scaleMetric_iff ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_scaleMetric_iff

theorem leastCurvatureOperatorEigenvalueAt_scaleMetric
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (x : M) :
    leastCurvatureOperatorEigenvalueAt (scaleMetric c hc g) x
        (metricAlgebraicCurvatureTensorAt (scaleMetric c hc g) x) =
      leastCurvatureOperatorEigenvalueAt g x (metricAlgebraicCurvatureTensorAt g x) / c := by
  have hsets : {K : ℝ | curvatureOperatorLowerBoundAt (scaleMetric c hc g) x
        (metricAlgebraicCurvatureTensorAt (scaleMetric c hc g) x) K} =
      c⁻¹ • {K : ℝ | curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) K} := by
    ext K
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hc.ne')]
    simp only [inv_inv, smul_eq_mul, Set.mem_ofPred_eq]
    exact curvatureOperatorLowerBoundAt_scaleMetric_iff g c hc x K
  unfold leastCurvatureOperatorEigenvalueAt
  rw [hsets, Real.sInf_smul_of_nonneg (inv_nonneg.mpr hc.le)]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_scaleMetric ``Submission.DifferentialGeometry.Geometry.Curvature.leastCurvatureOperatorEigenvalueAt_scaleMetric

end DifferentialGeometry.Geometry.Curvature
