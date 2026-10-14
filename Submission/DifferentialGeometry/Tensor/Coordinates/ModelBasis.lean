import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Free

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

@[irreducible] def chartModelBasis (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
  (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.map
    (toEuclidean (E := E)).symm.toLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartModelBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartModelBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartModelBasis ``Submission.DifferentialGeometry.Tensor.Coordinates.chartModelBasis

@[simp] lemma chartModelBasis_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (i : Fin (Module.finrank ℝ E)) :
    chartModelBasis E i =
      (toEuclidean (E := E)).symm (EuclideanSpace.single i (1 : ℝ)) := by
  classical
  with_unfolding_all
    change (toEuclidean (E := E)).symm.toLinearEquiv
        ((EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis i) =
      (toEuclidean (E := E)).symm (EuclideanSpace.single i (1 : ℝ))
  simp [OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply (𝕜 := ℝ) (ι := Fin (Module.finrank ℝ E))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartModelBasis_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartModelBasis_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartModelBasis_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.chartModelBasis_apply

end DifferentialGeometry.Tensor.Coordinates
