import Submission.DifferentialGeometry.Geometry.Metric.ExteriorEndomorphism
import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.Form

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace exteriorPower
open _root_.exteriorPower

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
open _root_.exteriorPower in
private theorem append_two_eq (v w : Fin 2 → E) :
    Fin.append v w = ![v 0, v 1, w 0, w 1] := by
  ext i
  fin_cases i <;> rfl

run_cmd do
  let target := ``Submission.exteriorPower.append_two_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `exteriorPower.append_two_eq target :: scope.openDecls } }

open _root_.exteriorPower in
theorem curvatureTensor_left_alternating
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun x y z w => T ![x, y, z, w]))
    (v w : Fin 2 → E) (i j : Fin 2) (hij : i ≠ j) (hv : v i = v j) :
    T (Fin.append v w) = 0 := by
  have h01 : v 0 = v 1 := by
    fin_cases i <;> fin_cases j <;> simp_all
  rw [append_two_eq, h01]
  have h := hT.anti_first (v 1) (v 1) (w 0) (w 1)
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.curvatureTensor_left_alternating then
    throwError "Refusing to shadow existing declaration exteriorPower.curvatureTensor_left_alternating"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.curvatureTensor_left_alternating ``Submission.exteriorPower.curvatureTensor_left_alternating

open _root_.exteriorPower in
theorem curvatureTensor_right_alternating
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun x y z w => T ![x, y, z, w]))
    (v w : Fin 2 → E) (i j : Fin 2) (hij : i ≠ j) (hw : w i = w j) :
    T (Fin.append v w) = 0 := by
  have h01 : w 0 = w 1 := by
    fin_cases i <;> fin_cases j <;> simp_all
  rw [append_two_eq, h01]
  have h := hT.anti_last (v 0) (v 1) (w 1) (w 1)
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.curvatureTensor_right_alternating then
    throwError "Refusing to shadow existing declaration exteriorPower.curvatureTensor_right_alternating"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.curvatureTensor_right_alternating ``Submission.exteriorPower.curvatureTensor_right_alternating

end exteriorPower

namespace exteriorPower
open _root_.exteriorPower

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

open _root_.exteriorPower in
def traceNormalizedCurvatureEndomorphism
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun x y z w => T ![x, y, z, w])) :
    (⋀[ℝ]^2 E) →L[ℝ] ⋀[ℝ]^2 E :=
  (-2 : ℝ) • multilinearEndomorphism 2 T (curvatureTensor_left_alternating T hT)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.traceNormalizedCurvatureEndomorphism then
    throwError "Refusing to shadow existing declaration exteriorPower.traceNormalizedCurvatureEndomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.traceNormalizedCurvatureEndomorphism ``Submission.exteriorPower.traceNormalizedCurvatureEndomorphism

open _root_.exteriorPower in
theorem endomorphismTensor_traceNormalizedCurvatureEndomorphism
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun x y z w => T ![x, y, z, w])) :
    endomorphismTensor 2 (traceNormalizedCurvatureEndomorphism T hT) = (-2 : ℝ) • T := by
  change endomorphismTensorLinear 2 ((-2 : ℝ) • _) = _
  rw [map_smul]
  congr 1
  exact endomorphismTensor_multilinearEndomorphism 2 T
    (curvatureTensor_left_alternating T hT) (curvatureTensor_right_alternating T hT)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.endomorphismTensor_traceNormalizedCurvatureEndomorphism then
    throwError "Refusing to shadow existing declaration exteriorPower.endomorphismTensor_traceNormalizedCurvatureEndomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.endomorphismTensor_traceNormalizedCurvatureEndomorphism ``Submission.exteriorPower.endomorphismTensor_traceNormalizedCurvatureEndomorphism

open _root_.exteriorPower in
theorem traceNormalizedCurvatureEndomorphism_isSymmetric
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun x y z w => T ![x, y, z, w])) :
    (traceNormalizedCurvatureEndomorphism T hT).toLinearMap.IsSymmetric := by
  rw [isSymmetric_iff_endomorphismTensor, endomorphismTensor_traceNormalizedCurvatureEndomorphism]
  intro v w
  rw [smul_apply, smul_apply, append_two_eq, append_two_eq]
  exact congrArg (fun a : ℝ => (-2 : ℝ) • a) (hT.pair_swap (v 0) (v 1) (w 0) (w 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.traceNormalizedCurvatureEndomorphism_isSymmetric then
    throwError "Refusing to shadow existing declaration exteriorPower.traceNormalizedCurvatureEndomorphism_isSymmetric"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.traceNormalizedCurvatureEndomorphism_isSymmetric ``Submission.exteriorPower.traceNormalizedCurvatureEndomorphism_isSymmetric

open _root_.exteriorPower in
theorem inner_traceNormalizedCurvatureEndomorphism_ιMulti
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun x y z w => T ![x, y, z, w])) (v w : Fin 2 → E) :
    ⟪traceNormalizedCurvatureEndomorphism T hT (_root_.exteriorPower.ιMulti ℝ 2 v), _root_.exteriorPower.ιMulti ℝ 2 w⟫ =
      2 * T ![v 0, v 1, w 1, w 0] := by
  rw [← endomorphismTensor_apply_append, endomorphismTensor_traceNormalizedCurvatureEndomorphism,
    smul_apply, append_two_eq, smul_eq_mul]
  have h := hT.anti_last (v 0) (v 1) (w 0) (w 1)
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.inner_traceNormalizedCurvatureEndomorphism_ιMulti then
    throwError "Refusing to shadow existing declaration exteriorPower.inner_traceNormalizedCurvatureEndomorphism_ιMulti"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.inner_traceNormalizedCurvatureEndomorphism_ιMulti ``Submission.exteriorPower.inner_traceNormalizedCurvatureEndomorphism_ιMulti

open _root_.exteriorPower in
def traceNormalizedCurvatureSelfAdjoint
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d])) :
    selfAdjoint ((⋀[ℝ]^2 E) →L[ℝ] ⋀[ℝ]^2 E) :=
  ⟨traceNormalizedCurvatureEndomorphism T hT,
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (traceNormalizedCurvatureEndomorphism_isSymmetric T hT)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.traceNormalizedCurvatureSelfAdjoint then
    throwError "Refusing to shadow existing declaration exteriorPower.traceNormalizedCurvatureSelfAdjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.traceNormalizedCurvatureSelfAdjoint ``Submission.exteriorPower.traceNormalizedCurvatureSelfAdjoint

open _root_.exteriorPower in
theorem traceNormalizedCurvatureSelfAdjoint_coe
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d])) :
    (traceNormalizedCurvatureSelfAdjoint T hT : (⋀[ℝ]^2 E) →L[ℝ] ⋀[ℝ]^2 E) =
      traceNormalizedCurvatureEndomorphism T hT := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.traceNormalizedCurvatureSelfAdjoint_coe then
    throwError "Refusing to shadow existing declaration exteriorPower.traceNormalizedCurvatureSelfAdjoint_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.traceNormalizedCurvatureSelfAdjoint_coe ``Submission.exteriorPower.traceNormalizedCurvatureSelfAdjoint_coe

open _root_.exteriorPower in
theorem eq_traceNormalizedCurvatureEndomorphism_iff
    (A : (⋀[ℝ]^2 E) →L[ℝ] ⋀[ℝ]^2 E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d])) :
    A = traceNormalizedCurvatureEndomorphism T hT ↔
      ∀ a b c d : E, ⟪A (_root_.exteriorPower.ιMulti ℝ 2 ![a, b]), _root_.exteriorPower.ιMulti ℝ 2 ![c, d]⟫ =
        2 * T ![a, b, d, c] := by
  constructor
  · rintro rfl a b c d
    exact inner_traceNormalizedCurvatureEndomorphism_ιMulti T hT ![a, b] ![c, d]
  · intro h
    apply endomorphismTensor_injective 2
    ext v
    have hv : v = Fin.append ![v 0, v 1] ![v 2, v 3] := by
      ext i
      fin_cases i <;> rfl
    rw [hv, endomorphismTensor_apply_append, endomorphismTensor_apply_append,
      inner_traceNormalizedCurvatureEndomorphism_ιMulti]
    exact h _ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.eq_traceNormalizedCurvatureEndomorphism_iff then
    throwError "Refusing to shadow existing declaration exteriorPower.eq_traceNormalizedCurvatureEndomorphism_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.eq_traceNormalizedCurvatureEndomorphism_iff ``Submission.exteriorPower.eq_traceNormalizedCurvatureEndomorphism_iff

open _root_.exteriorPower in
theorem existsUnique_traceNormalizedCurvatureSelfAdjoint
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d])) :
    ∃! A : selfAdjoint ((⋀[ℝ]^2 E) →L[ℝ] ⋀[ℝ]^2 E),
      ∀ a b c d : E, ⟪(A : (⋀[ℝ]^2 E) →L[ℝ] ⋀[ℝ]^2 E) (_root_.exteriorPower.ιMulti ℝ 2 ![a, b]),
        ιMulti ℝ 2 ![c, d]⟫ = 2 * T ![a, b, d, c] := by
  refine ⟨traceNormalizedCurvatureSelfAdjoint T hT, ?_, ?_⟩
  · exact (eq_traceNormalizedCurvatureEndomorphism_iff _ T hT).mp rfl
  · intro A hA
    apply Subtype.ext
    exact (eq_traceNormalizedCurvatureEndomorphism_iff _ T hT).mpr hA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.existsUnique_traceNormalizedCurvatureSelfAdjoint then
    throwError "Refusing to shadow existing declaration exteriorPower.existsUnique_traceNormalizedCurvatureSelfAdjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.existsUnique_traceNormalizedCurvatureSelfAdjoint ``Submission.exteriorPower.existsUnique_traceNormalizedCurvatureSelfAdjoint

open _root_.exteriorPower in
theorem traceNormalizedCurvatureEndomorphism_eq_smul_id_of_constant_curvature
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun x y z w => T ![x, y, z, w])) (k : ℝ)
    (hk : ∀ a b c d, T ![a, b, c, d] =
      k * (⟪a, d⟫ * ⟪b, c⟫ - ⟪a, c⟫ * ⟪b, d⟫)) :
    traceNormalizedCurvatureEndomorphism T hT = (2 * k) • ContinuousLinearMap.id ℝ (⋀[ℝ]^2 E) := by
  apply endomorphismTensor_injective 2
  ext v
  rw [endomorphismTensor_traceNormalizedCurvatureEndomorphism]
  have hv : v = ![v 0, v 1, v 2, v 3] := by
    ext i
    fin_cases i <;> rfl
  have happ : v = Fin.append ![v 0, v 1] ![v 2, v 3] := by
    ext i
    fin_cases i <;> rfl
  rw [smul_apply, smul_eq_mul]
  conv_lhs => rw [hv, hk]
  conv_rhs => rw [happ]
  rw [endomorphismTensor_apply_append, smul_apply,
    ContinuousLinearMap.id_apply, real_inner_smul_left, _root_.exteriorPower.inner_ιMulti_ιMulti, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `exteriorPower.traceNormalizedCurvatureEndomorphism_eq_smul_id_of_constant_curvature then
    throwError "Refusing to shadow existing declaration exteriorPower.traceNormalizedCurvatureEndomorphism_eq_smul_id_of_constant_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `exteriorPower.traceNormalizedCurvatureEndomorphism_eq_smul_id_of_constant_curvature ``Submission.exteriorPower.traceNormalizedCurvatureEndomorphism_eq_smul_id_of_constant_curvature

end exteriorPower
