import Submission.DifferentialGeometry.Tensor.Alternating.Coordinates.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Multilinear.Basis

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open scoped _root_.BigOperators

namespace ContinuousAlternatingMap
open _root_.ContinuousAlternatingMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.ContinuousAlternatingMap in
private theorem elementaryCovector_pair_basis_apply {n : ℕ}
    (B : Module.Basis (Fin n) ℝ E) (i j p q : Fin n) :
    elementaryCovector B.cDualBasis ![i,j] ![B p,B q] =
      (if i = p then 1 else 0) * (if j = q then 1 else 0) -
        (if i = q then 1 else 0) * (if j = p then 1 else 0) := by
  rw [elementaryCovector_apply, Matrix.det_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Module.Basis.cDualBasis_apply_self]

run_cmd do
  let target := ``Submission.ContinuousAlternatingMap.elementaryCovector_pair_basis_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `ContinuousAlternatingMap.elementaryCovector_pair_basis_apply target :: scope.openDecls } }

open _root_.ContinuousAlternatingMap in
private theorem sum_pair_elementaryCovector {n : ℕ}
    (B : Module.Basis (Fin n) ℝ E) (a : E [⋀^Fin 2]→L[ℝ] ℝ) :
    (2 : ℝ) • a = ∑ i, ∑ j, a ![B i,B j] • elementaryCovector B.cDualBasis ![i,j] := by
  apply _root_.ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ => B)
  intro v
  change ((2 : ℝ) • a) (fun k => B (v k)) =
    (∑ i, ∑ j, a ![B i,B j] • elementaryCovector B.cDualBasis ![i,j]) (fun k => B (v k))
  have hv : (fun k => B (v k)) = ![B (v 0), B (v 1)] := by
    funext k
    fin_cases k <;> rfl
  rw [hv]
  simp only [_root_.ContinuousAlternatingMap.smul_apply, _root_.ContinuousAlternatingMap.sum_apply, smul_eq_mul, elementaryCovector_pair_basis_apply]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, _root_.MulZeroClass.mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hswap : a ![B (v 1),B (v 0)] = -a ![B (v 0),B (v 1)] := by
    simpa using a.map_swap (v := ![B (v 0),B (v 1)]) (i := 0) (j := 1) (by decide)
  rw [hswap]
  ring

run_cmd do
  let target := ``Submission.ContinuousAlternatingMap.sum_pair_elementaryCovector
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `ContinuousAlternatingMap.sum_pair_elementaryCovector target :: scope.openDecls } }

open _root_.ContinuousAlternatingMap in
theorem trace_eq_half_sum_pair {n : ℕ}
    (B : Module.Basis (Fin n) ℝ E)
    (A : (E [⋀^Fin 2]→L[ℝ] ℝ) →ₗ[ℝ] (E [⋀^Fin 2]→L[ℝ] ℝ)) :
    LinearMap.trace ℝ _ A = (1 / 2 : ℝ) *
      ∑ i, ∑ j, A (elementaryCovector B.cDualBasis ![i,j]) ![B i,B j] := by
  let _ : FiniteDimensional ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) :=
    (elementaryCovectorBasis (k := 2) B).finiteDimensional_of_finite
  let ev (i j : Fin n) : (E [⋀^Fin 2]→L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun a => a ![B i,B j]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have heq : (2 : ℝ) • A =
      ∑ i, ∑ j, (ev i j).smulRight (A (elementaryCovector B.cDualBasis ![i,j])) := by
    apply LinearMap.ext
    intro a
    have h := congrArg A (sum_pair_elementaryCovector B a)
    simpa [ev, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.smul_apply] using h
  have htrace := congrArg (LinearMap.trace ℝ (E [⋀^Fin 2]→L[ℝ] ℝ)) heq
  simp only [_root_.map_smul, _root_.map_sum, smul_eq_mul, LinearMap.trace_smulRight] at htrace
  change 2 * LinearMap.trace ℝ _ A =
    ∑ i, ∑ j, A (elementaryCovector B.cDualBasis ![i,j]) ![B i,B j] at htrace
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.trace_eq_half_sum_pair then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.trace_eq_half_sum_pair"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.trace_eq_half_sum_pair ``Submission.ContinuousAlternatingMap.trace_eq_half_sum_pair

end ContinuousAlternatingMap
