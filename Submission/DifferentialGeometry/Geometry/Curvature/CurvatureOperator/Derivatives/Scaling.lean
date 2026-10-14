import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Covariant
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
namespace DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealOfNatWithTopENat_differentialGeometry : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealOfNatWithTopENat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealOfNatWithTopENat_differentialGeometry target :: scope.openDecls } }

private theorem curvCovDerivStep_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (a : ℕ) (A : Tensor0SField (I := I) (M := M) (n := ∞) (a + 4)) :
    curvCovDerivStep (scaleMetric c hc g) a A = curvCovDerivStep g a A := by
  rw [curvStep_eq_covStep, curvStep_eq_covStep]
  apply DFunLike.ext
  intro x
  rw [covStep_apply, covStep_apply, lcConn_scaleMetric]

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.curvCovDerivStep_scaleMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.curvCovDerivStep_scaleMetric target :: scope.openDecls } }

theorem curvCovDeriv_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (a : ℕ) :
    curvCovDeriv (scaleMetric c hc g) a = c • curvCovDeriv g a := by
  induction a with
  | zero =>
    apply DFunLike.ext
    intro x
    exact metricRm_scale c hc g x
  | succ a ih =>
    rw [curvCovDeriv_succ, curvCovDeriv_succ, ih, curvCovDerivStep_scaleMetric,
      curvStep_eq_covStep, curvStep_eq_covStep, covStep_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.curvCovDeriv_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.curvCovDeriv_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.curvCovDeriv_scaleMetric ``Submission.DifferentialGeometry.CheegerGromovCompactness.curvCovDeriv_scaleMetric

theorem curvDerivNormSq_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (a : ℕ) (x : M) :
    curvDerivNormSq a (scaleMetric c hc g) x = c⁻¹ ^ (a + 2) * curvDerivNormSq a g x := by
  unfold curvDerivNormSq
  rw [curvCovDeriv_scaleMetric]
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply]
  rw [normSq0S_scale, normSq0S_smul]
  have hw : c⁻¹ ^ (a + 4) * c ^ 2 = c⁻¹ ^ (a + 2) := by
    rw [show a + 4 = (a + 2) + 2 by omega, pow_add, mul_assoc, ← mul_pow,
      inv_mul_cancel₀ hc.ne', one_pow, mul_one]
  rw [← mul_assoc, hw]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.curvDerivNormSq_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.curvDerivNormSq_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.curvDerivNormSq_scaleMetric ``Submission.DifferentialGeometry.CheegerGromovCompactness.curvDerivNormSq_scaleMetric

theorem curvDerivNorm_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (a : ℕ) (x : M) :
    curvDerivNorm a (scaleMetric c hc g) x = curvDerivNorm a g x / (c * Real.sqrt c ^ a) := by
  unfold curvDerivNorm
  rw [curvDerivNormSq_scaleMetric, Real.sqrt_mul (by positivity)]
  have hw : Real.sqrt (c⁻¹ ^ (a + 2)) = (c * Real.sqrt c ^ a)⁻¹ := by
    have heq : c⁻¹ = ((Real.sqrt c)⁻¹) ^ 2 := by
      rw [inv_pow, Real.sq_sqrt hc.le]
    rw [heq, pow_right_comm, Real.sqrt_sq (by positivity), pow_add]
    simp only [inv_pow, Real.sq_sqrt hc.le]
    ring
  rw [hw, div_eq_mul_inv, mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.curvDerivNorm_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.curvDerivNorm_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.curvDerivNorm_scaleMetric ``Submission.DifferentialGeometry.CheegerGromovCompactness.curvDerivNorm_scaleMetric
end DifferentialGeometry.CheegerGromovCompactness
