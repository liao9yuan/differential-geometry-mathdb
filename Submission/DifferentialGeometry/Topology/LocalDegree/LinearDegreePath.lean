import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Path

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.InnerProductSpace _root_.Module
namespace DifferentialGeometry.LocalDegree
variable {n : ℕ}

private theorem gs_diag (f : Fin n → EuclideanSpace ℝ (Fin n))
    (hf : LinearIndependent ℝ f) (i : Fin n) :
    0 < _root_.Inner.inner ℝ (_root_.InnerProductSpace.gramSchmidtOrthonormalBasis (𝕜 := ℝ) (by simp) f i) (f i) := by
  have hn : 0 < ‖gramSchmidt ℝ f i‖ := norm_pos_iff.mpr (_root_.InnerProductSpace.gramSchmidt_ne_zero i hf)
  have hnorm : _root_.InnerProductSpace.gramSchmidtNormed ℝ f i ≠ 0 := by
    intro h
    have := _root_.InnerProductSpace.gramSchmidtNormed_unit_length i hf
    rw [h, norm_zero] at this
    norm_num at this
  have hi : _root_.Inner.inner ℝ (_root_.InnerProductSpace.gramSchmidt ℝ f i) (f i) = ‖gramSchmidt ℝ f i‖ ^ 2 := by
    conv_lhs => rhs; rw [_root_.InnerProductSpace.gramSchmidt_def'' ℝ f i]
    rw [inner_add_right, inner_sum]
    simp only [inner_smul_right, real_inner_self_eq_norm_sq, add_eq_left]
    apply Finset.sum_eq_zero
    intro j hj
    rw [_root_.InnerProductSpace.gramSchmidt_orthogonal ℝ f (Finset.mem_Iio.mp hj).ne', _root_.MulZeroClass.mul_zero]
  rw [_root_.InnerProductSpace.gramSchmidtOrthonormalBasis_apply _ hnorm, _root_.InnerProductSpace.gramSchmidtNormed,
    real_inner_smul_left, hi]
  exact mul_pos (inv_pos.mpr hn) (sq_pos_of_pos hn)

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.gs_diag
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.gs_diag target :: scope.openDecls } }

private def reductionBasis
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  gramSchmidtOrthonormalBasis (𝕜 := ℝ) (by simp)
    (fun i => A (EuclideanSpace.basisFun (Fin n) ℝ i))

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.reductionBasis
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.reductionBasis target :: scope.openDecls } }


def orthogonalReduction
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).equiv (reductionBasis A) (Equiv.refl _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.orthogonalReduction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.orthogonalReduction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.orthogonalReduction ``Submission.DifferentialGeometry.LocalDegree.orthogonalReduction

private theorem ortho_repr
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.repr ((orthogonalReduction A).symm x) i =
      (reductionBasis A).repr x i := by
  simp [orthogonalReduction, OrthonormalBasis.equiv]

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.ortho_repr
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.ortho_repr target :: scope.openDecls } }

def orthogonalReductionPath
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    Path A.toContinuousLinearMap
      (orthogonalReduction A).toContinuousLinearEquiv.toContinuousLinearMap where
  toFun t := (1 - (t : ℝ)) • A.toContinuousLinearMap +
    (t : ℝ) • (orthogonalReduction A).toContinuousLinearEquiv.toContinuousLinearMap
  continuous_toFun := ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
    (continuous_subtype_val.smul continuous_const)
  source' := by simp
  target' := by
    apply ContinuousLinearMap.ext
    intro x
    change (1 - (1 : ℝ)) • A x + (1 : ℝ) • orthogonalReduction A x = _
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.orthogonalReductionPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.orthogonalReductionPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.orthogonalReductionPath ``Submission.DifferentialGeometry.LocalDegree.orthogonalReductionPath


theorem orthogonalReductionPath_apply
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (t : unitInterval) (x : EuclideanSpace ℝ (Fin n)) :
    orthogonalReductionPath A t x =
      (1 - (t : ℝ)) • A x + (t : ℝ) • orthogonalReduction A x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.orthogonalReductionPath_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.orthogonalReductionPath_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.orthogonalReductionPath_apply ``Submission.DifferentialGeometry.LocalDegree.orthogonalReductionPath_apply

private def triangularPart
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (t : unitInterval) :=
  (orthogonalReduction A).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (orthogonalReductionPath A t)

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.triangularPart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.triangularPart target :: scope.openDecls } }

private theorem triangularPart_matrix
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (t : unitInterval) (i j : Fin n) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (triangularPart A t).toLinearMap i j =
      (1 - (t : ℝ)) * (reductionBasis A).repr (A (EuclideanSpace.basisFun (Fin n) ℝ j)) i +
        (t : ℝ) * (if i = j then 1 else 0) := by
  classical
  rw [LinearMap.toMatrix_apply]
  change (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.repr
    ((orthogonalReduction A).symm (orthogonalReductionPath A t
      (EuclideanSpace.basisFun (Fin n) ℝ j))) i = _
  rw [ortho_repr, orthogonalReductionPath_apply,
    show orthogonalReduction A (EuclideanSpace.basisFun (Fin n) ℝ j) = reductionBasis A j from
      (EuclideanSpace.basisFun (Fin n) ℝ).equiv_apply_basis (reductionBasis A) (Equiv.refl _) j]
  simp [OrthonormalBasis.repr_self, PiLp.single_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.triangularPart_matrix
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.triangularPart_matrix target :: scope.openDecls } }

private theorem triangularPart_pos
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (t : unitInterval) :
    0 < LinearMap.det (triangularPart A t).toLinearMap := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have htri : (LinearMap.toMatrix b b (triangularPart A t).toLinearMap).IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    rw [triangularPart_matrix]
    have hz := _root_.InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular' (𝕜 := ℝ) (by simp)
      (fun k => A (EuclideanSpace.basisFun (Fin n) ℝ k)) hij
    change (1 - (t : ℝ)) * (reductionBasis A).repr
      (A (EuclideanSpace.basisFun (Fin n) ℝ j)) i + _ = 0
    rw [show (reductionBasis A).repr (A (EuclideanSpace.basisFun (Fin n) ℝ j)) i = 0 from hz]
    simp [ne_of_gt hij]
  rw [← LinearMap.det_toMatrix b, Matrix.det_of_isUpperTriangular htri]
  apply Finset.prod_pos
  intro i _
  rw [triangularPart_matrix, if_pos rfl, mul_one]
  have hli : LinearIndependent ℝ
      (fun k => A (EuclideanSpace.basisFun (Fin n) ℝ k)) :=
    ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map A.toLinearEquiv).linearIndependent
  have hd := gs_diag _ hli i
  change 0 < _root_.Inner.inner ℝ (reductionBasis A i) (A (EuclideanSpace.basisFun (Fin n) ℝ i)) at hd
  rw [OrthonormalBasis.repr_apply_apply]
  have hnonneg := mul_nonneg (sub_nonneg.mpr t.property.2) hd.le
  by_cases ht : (t : ℝ) = 0
  · simpa [ht] using hd
  · exact add_pos_of_nonneg_of_pos hnonneg (lt_of_le_of_ne t.property.1 (Ne.symm ht))

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.triangularPart_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.triangularPart_pos target :: scope.openDecls } }

private theorem reductionPath_det_factor
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (t : unitInterval) :
    LinearMap.det (orthogonalReductionPath A t).toLinearMap =
      LinearMap.det (orthogonalReduction A).toLinearMap *
        LinearMap.det (triangularPart A t).toLinearMap := by
  rw [← LinearMap.det_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact ((orthogonalReduction A).apply_symm_apply _).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.reductionPath_det_factor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.reductionPath_det_factor target :: scope.openDecls } }


theorem orthogonalReductionPath_det_ne_zero
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (t : unitInterval) :
    LinearMap.det (orthogonalReductionPath A t).toLinearMap ≠ 0 := by
  rw [reductionPath_det_factor]
  exact mul_ne_zero ((orthogonalReduction A).toLinearEquiv.isUnit_det'.ne_zero)
    (triangularPart_pos A t).ne'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.orthogonalReductionPath_det_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.orthogonalReductionPath_det_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.orthogonalReductionPath_det_ne_zero ``Submission.DifferentialGeometry.LocalDegree.orthogonalReductionPath_det_ne_zero


theorem orthogonalReductionPath_det_sign
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (t : unitInterval) :
    SignType.sign (LinearMap.det (orthogonalReductionPath A t).toLinearMap) =
      SignType.sign (LinearMap.det A.toLinearMap) := by
  have h (s : unitInterval) :
      SignType.sign (LinearMap.det (orthogonalReductionPath A s).toLinearMap) =
        SignType.sign (LinearMap.det (orthogonalReduction A).toLinearMap) := by
    rw [reductionPath_det_factor, sign_mul, sign_pos (triangularPart_pos A s), mul_one]
  exact (h t).trans (by simpa using (h 0).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.orthogonalReductionPath_det_sign then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.orthogonalReductionPath_det_sign"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.orthogonalReductionPath_det_sign ``Submission.DifferentialGeometry.LocalDegree.orthogonalReductionPath_det_sign


theorem orthogonalReduction_det_sign
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    SignType.sign (LinearMap.det (orthogonalReduction A).toLinearMap) =
      SignType.sign (LinearMap.det A.toLinearMap) := by
  have hQ : (orthogonalReductionPath A 1).toLinearMap =
      (orthogonalReduction A).toLinearMap := by
    apply LinearMap.ext
    intro x
    simp
  simpa only [hQ] using orthogonalReductionPath_det_sign A 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.orthogonalReduction_det_sign then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.orthogonalReduction_det_sign"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.orthogonalReduction_det_sign ``Submission.DifferentialGeometry.LocalDegree.orthogonalReduction_det_sign


def orthogonalReductionPathEquiv
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (t : unitInterval) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (orthogonalReductionPath A t).toContinuousLinearEquivOfDetNeZero
    (orthogonalReductionPath_det_ne_zero A t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.orthogonalReductionPathEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.orthogonalReductionPathEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.orthogonalReductionPathEquiv ``Submission.DifferentialGeometry.LocalDegree.orthogonalReductionPathEquiv


@[simp]
theorem orthogonalReductionPathEquiv_apply
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (t : unitInterval) (x : EuclideanSpace ℝ (Fin n)) :
    orthogonalReductionPathEquiv A t x = orthogonalReductionPath A t x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.orthogonalReductionPathEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.orthogonalReductionPathEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.orthogonalReductionPathEquiv_apply ``Submission.DifferentialGeometry.LocalDegree.orthogonalReductionPathEquiv_apply


theorem orthogonalReductionPath_bijective
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (t : unitInterval) :
    Function.Bijective (orthogonalReductionPath A t) :=
  (orthogonalReductionPathEquiv A t).bijective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.orthogonalReductionPath_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.orthogonalReductionPath_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.orthogonalReductionPath_bijective ``Submission.DifferentialGeometry.LocalDegree.orthogonalReductionPath_bijective


theorem orthogonalReductionPath_nonzero
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (t : unitInterval)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    orthogonalReductionPath A t x ≠ 0 :=
  mt (orthogonalReductionPathEquiv A t).map_eq_zero_iff.mp hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.orthogonalReductionPath_nonzero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.orthogonalReductionPath_nonzero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.orthogonalReductionPath_nonzero ``Submission.DifferentialGeometry.LocalDegree.orthogonalReductionPath_nonzero

end DifferentialGeometry.LocalDegree
