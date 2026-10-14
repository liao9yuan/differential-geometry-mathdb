import Mathlib.Geometry.Manifold.DerivationBundle
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Dual
import Submission.DifferentialGeometry.Bundle.Section
import Submission.DifferentialGeometry.Tensor.RSTensor.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Geometry.Connection.Realization


noncomputable section

open scoped _root_.Manifold _root_.ContDiff
open _root_.Bundle _root_.Submission.Bundle

section SmoothRicciFlowContext

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

instance smoothSectionScalarTower :
    IsScalarTower ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  smul_assoc r f s := by ext x; exact _root_.SemigroupAction.mul_smul (r : ℝ) (f x : ℝ) (s x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.Realization.smoothSectionScalarTower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.Realization.smoothSectionScalarTower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.Realization.smoothSectionScalarTower ``Submission.DifferentialGeometry.Geometry.Connection.Realization.smoothSectionScalarTower

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
private theorem two_smooth_eval (x : M) : (2 : C^∞⟮I, M; ℝ⟯) x = (2 : ℝ) := by
  have h2a : (2 : C^∞⟮I, M; ℝ⟯) * (1 : C^∞⟮I, M; ℝ⟯) = (2 : C^∞⟮I, M; ℝ⟯) := mul_one _
  have h_two_eq : (2 : C^∞⟮I, M; ℝ⟯) = (1 : C^∞⟮I, M; ℝ⟯) + (1 : C^∞⟮I, M; ℝ⟯) := by norm_num
  have := DFunLike.congr_fun h_two_eq x
  simp only [ContMDiffMap.coe_add, Pi.add_apply, ContMDiffMap.coe_one, Pi.one_apply] at this
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.Realization.two_smooth_eval
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.Realization.two_smooth_eval target :: scope.openDecls } }

noncomputable instance invertible2SmoothFunctions :
    Invertible (2 : C^∞⟮I, M; ℝ⟯) where
  invOf := _root_.Algebra.algebraMap ℝ C^∞⟮I, M; ℝ⟯ (1/2 : ℝ)
  invOf_mul_self := by
    apply ContMDiffMap.ext; intro x
    have : (_root_.Algebra.algebraMap ℝ C^∞⟮I, M; ℝ⟯ (1/2 : ℝ) * (2 : C^∞⟮I, M; ℝ⟯)) x =
        (1/2 : ℝ) * (2 : C^∞⟮I, M; ℝ⟯) x := by
      simp only [ContMDiffMap.coe_mul, Pi.mul_apply, Algebra.algebraMap_eq_smul_one,
        ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, ContMDiffMap.coe_one,
        Pi.one_apply, mul_one]
    rw [this, two_smooth_eval, ContMDiffMap.coe_one, Pi.one_apply]; norm_num
  mul_invOf_self := by
    apply ContMDiffMap.ext; intro x
    have : ((2 : C^∞⟮I, M; ℝ⟯) * _root_.Algebra.algebraMap ℝ C^∞⟮I, M; ℝ⟯ (1/2 : ℝ)) x =
        (2 : C^∞⟮I, M; ℝ⟯) x * (1/2 : ℝ) := by
      simp only [ContMDiffMap.coe_mul, Pi.mul_apply, Algebra.algebraMap_eq_smul_one,
        ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, ContMDiffMap.coe_one,
        Pi.one_apply, mul_one]
    rw [this, two_smooth_eval, ContMDiffMap.coe_one, Pi.one_apply]; norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.Realization.invertible2SmoothFunctions then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.Realization.invertible2SmoothFunctions"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.Realization.invertible2SmoothFunctions ``Submission.DifferentialGeometry.Geometry.Connection.Realization.invertible2SmoothFunctions

end SmoothRicciFlowContext

end

end DifferentialGeometry.Geometry.Connection.Realization
