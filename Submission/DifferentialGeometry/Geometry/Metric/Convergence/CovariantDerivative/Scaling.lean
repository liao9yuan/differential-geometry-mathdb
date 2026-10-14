import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.CovariantTwoTensor
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance scalingComplete : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.scalingComplete
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.scalingComplete target :: scope.openDecls } }

private local instance scalingC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.scalingC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.scalingC1 target :: scope.openDecls } }

theorem metricCovDerivStep_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (a : ℕ)
    (A : Tensor0SField (I := I) (M := M) (n := ∞) (a + 2)) :
    metricCovDerivStep (scaleMetric c hc g) a A = metricCovDerivStep g a A := by
  apply DFunLike.ext
  intro x
  rw [metricCovDerivStep_apply, metricCovDerivStep_apply, lcConn_scaleMetric]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricCovDerivStep_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricCovDerivStep_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricCovDerivStep_scaleMetric ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricCovDerivStep_scaleMetric

theorem tensor02CovDeriv_scaleMetric (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (n := ∞) 2) (a : ℕ) :
    tensor02CovDeriv A (scaleMetric c hc g) a = tensor02CovDeriv A g a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    change metricCovDerivStep (scaleMetric c hc g) a
      (tensor02CovDeriv A (scaleMetric c hc g) a) =
      metricCovDerivStep g a (tensor02CovDeriv A g a)
    rw [ih, metricCovDerivStep_scaleMetric]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.tensor02CovDeriv_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.tensor02CovDeriv_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.tensor02CovDeriv_scaleMetric ``Submission.DifferentialGeometry.CheegerGromovCompactness.tensor02CovDeriv_scaleMetric

theorem tensor02CovDerivNormWith_smul (gcov gnorm : SmoothRiemannianMetric I M)
    (c : ℝ) (A : Tensor0SField (I := I) (M := M) (n := ∞) 2) (a : ℕ) (x : M) :
    tensor02CovDerivNormWith a (c • A) gcov gnorm x =
      |c| * tensor02CovDerivNormWith a A gcov gnorm x := by
  simp only [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field,
    covDerivOfField_smul, ContMDiffSection.coe_smul, Pi.smul_apply]
  exact sqrt_normSq0S_smul gnorm x (a + 2) c _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.tensor02CovDerivNormWith_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.tensor02CovDerivNormWith_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.tensor02CovDerivNormWith_smul ``Submission.DifferentialGeometry.CheegerGromovCompactness.tensor02CovDerivNormWith_smul

theorem tensor02CovDerivNormWith_scaleMetric (gcov gnorm : SmoothRiemannianMetric I M)
    (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (A : Tensor0SField (I := I) (M := M) (n := ∞) 2) (a : ℕ) (x : M) :
    tensor02CovDerivNormWith a A (scaleMetric c hc gcov) (scaleMetric d hd gnorm) x =
      (Real.sqrt d)⁻¹ ^ (a + 2) * tensor02CovDerivNormWith a A gcov gnorm x := by
  unfold tensor02CovDerivNormWith
  rw [tensor02CovDeriv_scaleMetric, normSq0S_scale,
    Real.sqrt_mul (pow_nonneg (inv_nonneg.mpr hd.le) _)]
  congr 1
  have heq : d⁻¹ = ((Real.sqrt d)⁻¹) ^ 2 := by
    rw [inv_pow, Real.sq_sqrt hd.le]
  rw [heq, pow_right_comm, Real.sqrt_sq (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg d)) _)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.tensor02CovDerivNormWith_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.tensor02CovDerivNormWith_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.tensor02CovDerivNormWith_scaleMetric ``Submission.DifferentialGeometry.CheegerGromovCompactness.tensor02CovDerivNormWith_scaleMetric

end DifferentialGeometry.CheegerGromovCompactness
