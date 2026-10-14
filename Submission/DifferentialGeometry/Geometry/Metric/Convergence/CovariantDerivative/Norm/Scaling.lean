import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

theorem tensor02CovDerivNormWith_smul_scaleMetric (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric I N)
    (A : Tensor0SField (I := I) (M := N) (n := ∞) 2)
    (w : ℝ) (a : ℕ) (y : N) :
    tensor02CovDerivNormWith a (w • A) (scaleMetric c hc g) (scaleMetric c hc g) y =
      (Real.sqrt ((c⁻¹) ^ (a + 2)) * |w|) * tensor02CovDerivNormWith a A g g y := by
  unfold tensor02CovDerivNormWith
  rw [tensor02CovDeriv_scaleMetric, tensor02_cov_deriv_eq_cov_deriv_of_field,
    covDerivOfField_smul]
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply]
  rw [normSq0S_scale, Real.sqrt_mul (pow_nonneg (inv_nonneg.mpr hc.le) _),
    sqrt_normSq0S_smul, ← mul_assoc, ← tensor02_cov_deriv_eq_cov_deriv_of_field]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.tensor02CovDerivNormWith_smul_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.tensor02CovDerivNormWith_smul_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.tensor02CovDerivNormWith_smul_scaleMetric ``Submission.DifferentialGeometry.CheegerGromovCompactness.tensor02CovDerivNormWith_smul_scaleMetric


end DifferentialGeometry.CheegerGromovCompactness
