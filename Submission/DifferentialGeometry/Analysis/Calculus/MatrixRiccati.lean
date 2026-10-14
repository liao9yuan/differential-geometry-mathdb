import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Matrix
open scoped _root_.Matrix.Norms.Operator

namespace DifferentialGeometry
namespace Analysis

variable {n : Type*} [DecidableEq n]

omit [DecidableEq n] in
theorem hasDerivAt_matrix
    [Finite n]
    (A : ℝ → Matrix n n ℝ) (A' : Matrix n n ℝ) (t : ℝ)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t) :
    HasDerivAt A A' t := by
  let : Fintype n := Fintype.ofFinite n
  exact hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => hA i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasDerivAt_matrix then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasDerivAt_matrix"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasDerivAt_matrix ``Submission.DifferentialGeometry.Analysis.hasDerivAt_matrix

variable [Fintype n]

omit [DecidableEq n] in
theorem hasDerivAt_trace
    (A : ℝ → Matrix n n ℝ) (A' : Matrix n n ℝ) (t : ℝ)
    (hA : HasDerivAt A A' t) :
    HasDerivAt (fun s => _root_.Matrix.trace (A s)) (_root_.Matrix.trace A') t := by
  simpa only [_root_.Matrix.trace, Matrix.diag_apply] using
    (HasDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) =>
      hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasDerivAt_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasDerivAt_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasDerivAt_trace ``Submission.DifferentialGeometry.Analysis.hasDerivAt_trace

theorem hasDerivAt_inv_mul
    (G B : ℝ → Matrix n n ℝ) (G' B' : Matrix n n ℝ) (t : ℝ)
    (hG : HasDerivAt G G' t) (hB : HasDerivAt B B' t)
    (hunit : IsUnit (G t)) :
    HasDerivAt (fun s => (G s)⁻¹ * B s)
      (-((G t)⁻¹ * G' * (G t)⁻¹) * B t + (G t)⁻¹ * B') t := by
  obtain ⟨u, hu⟩ := hunit
  have hinvF :
      HasFDerivAt (Ring.inverse : Matrix n n ℝ → Matrix n n ℝ)
        (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℝ)
          (↑u⁻¹ : Matrix n n ℝ) (↑u⁻¹ : Matrix n n ℝ)) (G t) := by
    rw [← hu]
    exact hasFDerivAt_ringInverse u
  have hinv :
      HasDerivAt (fun s => Ring.inverse (G s))
        (-((G t)⁻¹ * G' * (G t)⁻¹)) t := by
    simpa [Function.comp_def, hu, ContinuousLinearMap.mulLeftRight_apply,
      Matrix.nonsing_inv_eq_ringInverse] using! hinvF.comp_hasDerivAt t hG
  simpa [Matrix.nonsing_inv_eq_ringInverse, Matrix.mul_assoc] using! hinv.mul hB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasDerivAt_inv_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasDerivAt_inv_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasDerivAt_inv_mul ``Submission.DifferentialGeometry.Analysis.hasDerivAt_inv_mul

theorem trace_inv_mul_conj
    (G A : Matrix n n ℝ) (hdet : IsUnit G.det) :
    trace (G⁻¹ * (A * G)) = _root_.Matrix.trace A := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle,
    Matrix.mul_nonsing_inv G hdet, Matrix.one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.trace_inv_mul_conj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.trace_inv_mul_conj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.trace_inv_mul_conj ``Submission.DifferentialGeometry.Analysis.trace_inv_mul_conj

theorem trace_sq_le_mul
    (A : Matrix n n ℝ) (hA : A.IsSymm) :
    (_root_.Matrix.trace A) ^ 2 ≤ (Fintype.card n : ℝ) * _root_.Matrix.trace (A ^ 2) := by
  have hdiag :
      (∑ i : n, A i i) ^ 2 ≤
        (Fintype.card n : ℝ) * ∑ i : n, (A i i) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (α := ℝ)
      (s := (Finset.univ : Finset n)) (f := fun i => A i i)
    simpa [Finset.card_univ] using h
  have hrow (i : n) : (A i i) ^ 2 ≤ ∑ j : n, (A i j) ^ 2 := by
    exact Finset.single_le_sum (fun j _ => sq_nonneg (A i j)) (Finset.mem_univ i)
  have hsum : ∑ i : n, (A i i) ^ 2 ≤ ∑ i : n, ∑ j : n, (A i j) ^ 2 :=
    Finset.sum_le_sum fun i _ => hrow i
  have hcard : (0 : ℝ) ≤ Fintype.card n := by positivity
  have htraceSq : _root_.Matrix.trace (A ^ 2) = ∑ i : n, ∑ j : n, (A i j) ^ 2 := by
    simp only [_root_.Matrix.trace, Matrix.diag_apply, pow_two, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hA.apply i j]
  rw [_root_.Matrix.trace, htraceSq]
  exact hdiag.trans (mul_le_mul_of_nonneg_left hsum hcard)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.trace_sq_le_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.trace_sq_le_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.trace_sq_le_mul ``Submission.DifferentialGeometry.Analysis.trace_sq_le_mul

theorem trace_sq_eq_iff
    [Nonempty n] (A : Matrix n n ℝ) (hA : A.IsSymm) :
    (_root_.Matrix.trace A) ^ 2 = (Fintype.card n : ℝ) * _root_.Matrix.trace (A ^ 2) ↔
      A = (_root_.Matrix.trace A / (Fintype.card n : ℝ)) • (1 : Matrix n n ℝ) := by
  let N : ℝ := Fintype.card n
  have hNpos : 0 < N := by positivity
  have hdiag :
      (∑ i : n, A i i) ^ 2 ≤ N * ∑ i : n, (A i i) ^ 2 := by
    simpa [N, Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq (α := ℝ)
        (s := (Finset.univ : Finset n)) (f := fun i => A i i))
  have hrow (i : n) : (A i i) ^ 2 ≤ ∑ j : n, (A i j) ^ 2 := by
    exact Finset.single_le_sum (fun j _ => sq_nonneg (A i j)) (Finset.mem_univ i)
  have hsum : ∑ i : n, (A i i) ^ 2 ≤ ∑ i : n, ∑ j : n, (A i j) ^ 2 :=
    Finset.sum_le_sum fun i _ => hrow i
  have htraceSq : _root_.Matrix.trace (A ^ 2) = ∑ i : n, ∑ j : n, (A i j) ^ 2 := by
    simp only [_root_.Matrix.trace, Matrix.diag_apply, pow_two, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hA.apply i j]
  constructor
  · intro heq
    have heq' :
        (∑ i : n, A i i) ^ 2 = N * ∑ i : n, ∑ j : n, (A i j) ^ 2 := by
      rw [htraceSq] at heq
      simpa only [_root_.Matrix.trace, Matrix.diag_apply, N] using heq
    have hdiag_eq :
        (∑ i : n, A i i) ^ 2 = N * ∑ i : n, (A i i) ^ 2 := by
      apply le_antisymm hdiag
      calc
        N * ∑ i : n, (A i i) ^ 2 ≤ N * ∑ i : n, ∑ j : n, (A i j) ^ 2 :=
          mul_le_mul_of_nonneg_left hsum hNpos.le
        _ = (∑ i : n, A i i) ^ 2 := heq'.symm
    have hsum_eq :
        ∑ i : n, (A i i) ^ 2 = ∑ i : n, ∑ j : n, (A i j) ^ 2 := by
      apply (mul_left_cancel₀ hNpos.ne')
      rw [← hdiag_eq, heq']
    have hrow_eq (i : n) : (A i i) ^ 2 = ∑ j : n, (A i j) ^ 2 :=
      (Finset.sum_eq_sum_iff_of_le fun i _ => hrow i).mp hsum_eq i (Finset.mem_univ i)
    let μ : ℝ := _root_.Matrix.trace A / N
    have hvar : ∑ i : n, (A i i - μ) ^ 2 = 0 := by
      have hdiag_eq' : (_root_.Matrix.trace A) ^ 2 = N * ∑ i : n, (A i i) ^ 2 := by
        simpa only [_root_.Matrix.trace, Matrix.diag_apply] using hdiag_eq
      simp_rw [show ∀ i : n, (A i i - μ) ^ 2 =
          (A i i) ^ 2 - (2 * μ) * A i i + μ ^ 2 by intro i; ring]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp only [μ]
      rw [show ∑ i : n, A i i = _root_.Matrix.trace A by rfl]
      field_simp
      nlinarith
    have hdiag_val (i : n) : A i i = μ := by
      have hi : (A i i - μ) ^ 2 = 0 := by
        simpa using congr_fun ((Fintype.sum_eq_zero_iff_of_nonneg
          (fun j => sq_nonneg (A j j - μ))).mp hvar) i
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
    have hoff (i j : n) (hij : i ≠ j) : A i j = 0 := by
      have hle : ∀ k ∈ (Finset.univ : Finset n),
          (if k = i then (A i i) ^ 2 else 0) ≤ (A i k) ^ 2 := by
        intro k _
        by_cases hki : k = i
        · subst k
          simp
        · simp [hki, sq_nonneg]
      have hpoint := (Finset.sum_eq_sum_iff_of_le hle).mp (by
        simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true] using hrow_eq i) j
        (Finset.mem_univ j)
      have hsquare : (A i j) ^ 2 = 0 := by simpa [hij.symm] using hpoint.symm
      exact sq_eq_zero_iff.mp hsquare
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hdiag_val i, μ, N]
    · simp [hij, hoff i j hij]
  · intro hscalar
    rw [hscalar]
    simp only [Matrix.trace_smul, Matrix.trace_one, pow_two, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, smul_eq_mul]
    field_simp [show (Fintype.card n : ℝ) ≠ 0 by positivity]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.trace_sq_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.trace_sq_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.trace_sq_eq_iff ``Submission.DifferentialGeometry.Analysis.trace_sq_eq_iff

theorem hasDerivAt_riccati
    (G M : ℝ → Matrix n n ℝ) (Q : Matrix n n ℝ) (t : ℝ)
    (hG : HasDerivAt G ((2 : ℝ) • M t) t)
    (hM : HasDerivAt M (Q + M t * (G t)⁻¹ * M t) t)
    (hunit : IsUnit (G t)) :
    HasDerivAt (fun s => _root_.Matrix.trace ((G s)⁻¹ * M s))
      (_root_.Matrix.trace ((G t)⁻¹ * Q) - _root_.Matrix.trace (((G t)⁻¹ * M t) ^ 2)) t := by
  have hprod := hasDerivAt_inv_mul G M ((2 : ℝ) • M t)
    (Q + M t * (G t)⁻¹ * M t) t hG hM hunit
  refine (hasDerivAt_trace _ _ t hprod).congr_deriv ?_
  simp only [Matrix.mul_smul, Matrix.trace_add, Matrix.mul_add, pow_two,
    smul_mul_assoc, neg_mul, Matrix.trace_neg, Matrix.trace_smul]
  simp only [Matrix.mul_assoc]
  simp only [smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasDerivAt_riccati then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasDerivAt_riccati"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasDerivAt_riccati ``Submission.DifferentialGeometry.Analysis.hasDerivAt_riccati

end Analysis
end DifferentialGeometry

end
