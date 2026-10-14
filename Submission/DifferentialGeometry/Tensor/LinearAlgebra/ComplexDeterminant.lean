import Mathlib.LinearAlgebra.Complex.Determinant

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Geometry

theorem complex_linearMap_det (A : ℂ →ₗ[ℝ] ℂ) :
    A.det = (A 1).re * (A Complex.I).im - (A Complex.I).re * (A 1).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.complex_linearMap_det then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.complex_linearMap_det"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.complex_linearMap_det ``Submission.DifferentialGeometry.Geometry.complex_linearMap_det

end DifferentialGeometry.Geometry
