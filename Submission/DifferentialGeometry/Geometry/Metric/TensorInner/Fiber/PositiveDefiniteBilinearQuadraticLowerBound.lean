import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.PositiveDefiniteBilinearBoundedUnitBall

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry

theorem posDef_bilin_quadratic_lower_bound
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hPD : ∀ v : F, v ≠ 0 → 0 < B v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : F, c * ‖v‖ ^ 2 ≤ B v v := by
  simpa only [IsCoercive, pow_two, mul_assoc] using B.isCoercive_of_posDef hPD

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.posDef_bilin_quadratic_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.posDef_bilin_quadratic_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.posDef_bilin_quadratic_lower_bound ``Submission.DifferentialGeometry.posDef_bilin_quadratic_lower_bound

end DifferentialGeometry
