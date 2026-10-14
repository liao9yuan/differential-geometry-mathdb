import Submission.DifferentialGeometry.Analysis.Elliptic.MetricExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold
open scoped _root_.ContDiff _root_.Matrix

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem densityOnEuclid_eq_sqrt_det
    (g : SmoothRiemannianMetric I M) (α : M) (y : EuclN) :
    densityOnEuclid g α y = Real.sqrt (Matrix.of (fun i j => gramOnEuclid g α i j y)).det := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_eq_sqrt_det then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_eq_sqrt_det"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_eq_sqrt_det ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.densityOnEuclid_eq_sqrt_det

theorem invGramOnEuclid_eq_matrix_inv
    (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E))
    (y : EuclN) :
    invGramOnEuclid g α i j y = (Matrix.of (fun k l => gramOnEuclid g α k l y))⁻¹ i j := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_eq_matrix_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_eq_matrix_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_eq_matrix_inv ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid_eq_matrix_inv

theorem weightedInvGramOnEuclid_eq_sqrt_det_mul_inv
    (g : SmoothRiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E))
    (y : EuclN) :
    weightedInvGramOnEuclid g α i j y =
      Real.sqrt (Matrix.of (fun k l => gramOnEuclid g α k l y)).det *
        (Matrix.of (fun k l => gramOnEuclid g α k l y))⁻¹ i j := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_eq_sqrt_det_mul_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_eq_sqrt_det_mul_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_eq_sqrt_det_mul_inv ``Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension.weightedInvGramOnEuclid_eq_sqrt_det_mul_inv

end DifferentialGeometry.Analysis.Laplacian.MetricExtension
