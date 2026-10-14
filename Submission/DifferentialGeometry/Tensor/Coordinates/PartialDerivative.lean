import Submission.DifferentialGeometry.Tensor.Coordinates.ModelBasis
import Mathlib.Analysis.Calculus.FDeriv.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

def partialDeriv (i : Fin (Module.finrank ℝ E)) (u : E → ℝ) (y : E) : ℝ :=
  fderiv ℝ u y ((chartModelBasis E) i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.partialDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.partialDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.partialDeriv ``Submission.DifferentialGeometry.Tensor.Coordinates.partialDeriv

end DifferentialGeometry.Tensor.Coordinates
