import Submission.DifferentialGeometry.Tensor.LinearAlgebra.RankOneBilinear
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Data.Fin.VecNotation
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.BigOperators

namespace ContinuousLinearMap
open _root_.ContinuousLinearMap

open _root_.ContinuousLinearMap in
theorem sum_mul_apply_diagonal_eq_sum_coordinates
    {𝕜 E ι κ : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Fintype ι]
    (H : E →L[𝕜] E →L[𝕜] 𝕜) (e : Module.Basis ι 𝕜 E)
    (s : Finset κ) (a : κ → 𝕜) (v : κ → E) (C : ι → ι → 𝕜)
    (hC : ∀ i j, C i j = ∑ k ∈ s, a k * e.repr (v k) i * e.repr (v k) j) :
    (∑ k ∈ s, a k * H (v k) (v k)) = ∑ i, ∑ j, C i j * H (e i) (e j) := by
  simpa only [smul_eq_mul, _root_.ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply] using
    H.toLinearMap₁₂.sum_smul_apply_eq_sum_coordinates e e s a v v C hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousLinearMap.sum_mul_apply_diagonal_eq_sum_coordinates then
    throwError "Refusing to shadow existing declaration ContinuousLinearMap.sum_mul_apply_diagonal_eq_sum_coordinates"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousLinearMap.sum_mul_apply_diagonal_eq_sum_coordinates ``Submission.ContinuousLinearMap.sum_mul_apply_diagonal_eq_sum_coordinates

end ContinuousLinearMap

namespace DifferentialGeometry.Analysis.Calculus

theorem sum_mul_iteratedFDeriv_two_diagonal_eq_sum_coordinates
    {𝕜 E ι κ : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Fintype ι]
    (u : E → 𝕜) (x : E) (e : Module.Basis ι 𝕜 E)
    (s : Finset κ) (a : κ → 𝕜) (v : κ → E) (C : ι → ι → 𝕜)
    (hC : ∀ i j, C i j = ∑ k ∈ s, a k * e.repr (v k) i * e.repr (v k) j) :
    (∑ k ∈ s, a k * iteratedFDeriv 𝕜 2 u x ![v k, v k]) =
      ∑ i, ∑ j, C i j * iteratedFDeriv 𝕜 2 u x ![e i, e j] := by
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using
    ContinuousLinearMap.sum_mul_apply_diagonal_eq_sum_coordinates
      (fderiv 𝕜 (fderiv 𝕜 u) x) e s a v C hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.sum_mul_iteratedFDeriv_two_diagonal_eq_sum_coordinates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.sum_mul_iteratedFDeriv_two_diagonal_eq_sum_coordinates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.sum_mul_iteratedFDeriv_two_diagonal_eq_sum_coordinates ``Submission.DifferentialGeometry.Analysis.Calculus.sum_mul_iteratedFDeriv_two_diagonal_eq_sum_coordinates

end DifferentialGeometry.Analysis.Calculus
