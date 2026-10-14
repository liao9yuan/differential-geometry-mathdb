import Submission.DifferentialGeometry.Analysis.Sobolev.AntidiagonalTupleProductGrid

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.BigOperators

namespace DifferentialGeometry.Combinatorics

def antidiagonalTupleGridPartialSum (b : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, Combinatorics.antidiagonalTupleGrid b k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Combinatorics.antidiagonalTupleGridPartialSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Combinatorics.antidiagonalTupleGridPartialSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Combinatorics.antidiagonalTupleGridPartialSum ``Submission.DifferentialGeometry.Combinatorics.antidiagonalTupleGridPartialSum

lemma antidiagonalTupleGridPartialSum_nonneg (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (m : ℕ) :
    0 ≤ antidiagonalTupleGridPartialSum b m :=
  Finset.sum_nonneg fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Combinatorics.antidiagonalTupleGridPartialSum_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Combinatorics.antidiagonalTupleGridPartialSum_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Combinatorics.antidiagonalTupleGridPartialSum_nonneg ``Submission.DifferentialGeometry.Combinatorics.antidiagonalTupleGridPartialSum_nonneg

private lemma antidiagonalTupleGridPartialSum_mono (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {m m' : ℕ} (h : m ≤ m') :
    antidiagonalTupleGridPartialSum b m ≤ antidiagonalTupleGridPartialSum b m' :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    (fun k _ _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Combinatorics.antidiagonalTupleGridPartialSum_mono
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Combinatorics.antidiagonalTupleGridPartialSum_mono target :: scope.openDecls } }

lemma one_le_antidiagonalTupleGridPartialSum (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {m : ℕ} (hm : 1 ≤ m) :
    1 ≤ antidiagonalTupleGridPartialSum b m := by
  have h1 : Combinatorics.antidiagonalTupleGrid b 0 = 1 :=
    Combinatorics.antidiagonalTupleGrid_zero b
  calc (1 : ℝ) = antidiagonalTupleGridPartialSum b 1 := by
        rw [antidiagonalTupleGridPartialSum, Finset.sum_range_one, h1]
    _ ≤ antidiagonalTupleGridPartialSum b m := antidiagonalTupleGridPartialSum_mono b hb hm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Combinatorics.one_le_antidiagonalTupleGridPartialSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Combinatorics.one_le_antidiagonalTupleGridPartialSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Combinatorics.one_le_antidiagonalTupleGridPartialSum ``Submission.DifferentialGeometry.Combinatorics.one_le_antidiagonalTupleGridPartialSum

lemma antidiagonalTupleGrid_le_partialSum (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {k m : ℕ} (h : k < m) :
    Combinatorics.antidiagonalTupleGrid b k ≤ antidiagonalTupleGridPartialSum b m :=
  Finset.single_le_sum
    (f := fun k' => Combinatorics.antidiagonalTupleGrid b k')
    (fun k' _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k')
    (Finset.mem_range.mpr h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Combinatorics.antidiagonalTupleGrid_le_partialSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Combinatorics.antidiagonalTupleGrid_le_partialSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Combinatorics.antidiagonalTupleGrid_le_partialSum ``Submission.DifferentialGeometry.Combinatorics.antidiagonalTupleGrid_le_partialSum

lemma single_le_antidiagonalTupleGridPartialSum (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j : ℕ) (hj : 1 ≤ j) :
    b j ≤ Combinatorics.antidiagonalTupleGrid b j := by
  classical
  have hmem : (fun _ : Fin 1 => j) ∈ Finset.Nat.antidiagonalTuple 1 j := by
    rw [Finset.Nat.mem_antidiagonalTuple]
    simp
  have hprod : b j = ∏ m : Fin 1, b ((fun _ : Fin 1 => j) m) := by
    rw [Fin.prod_univ_one]
  rw [hprod, Combinatorics.antidiagonalTupleGrid]
  have h1 : (∏ m : Fin 1, b ((fun _ : Fin 1 => j) m)) ≤
      ∑ e ∈ Finset.Nat.antidiagonalTuple 1 j, ∏ m : Fin 1, b (e m) :=
    Finset.single_le_sum (f := fun e : Fin 1 → ℕ => ∏ m : Fin 1, b (e m))
      (fun e _ => Finset.prod_nonneg fun m _ => hb _) hmem
  refine le_trans h1 ?_
  exact Finset.single_le_sum
    (f := fun n : ℕ => ∑ e ∈ Finset.Nat.antidiagonalTuple n j, ∏ m : Fin n, b (e m))
    (fun n _ => Finset.sum_nonneg fun e _ => Finset.prod_nonneg fun m _ => hb _)
    (Finset.mem_range.mpr (by omega : (1 : ℕ) < j + 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Combinatorics.single_le_antidiagonalTupleGridPartialSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Combinatorics.single_le_antidiagonalTupleGridPartialSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Combinatorics.single_le_antidiagonalTupleGridPartialSum ``Submission.DifferentialGeometry.Combinatorics.single_le_antidiagonalTupleGridPartialSum

def antidiagonalTuplePairCount (m1 m2 : ℕ) : ℝ :=
  ∑ k1 ∈ Finset.range m1, ∑ k2 ∈ Finset.range m2, antidiagonalTupleGridCount k1 *
    antidiagonalTupleGridCount k2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Combinatorics.antidiagonalTuplePairCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Combinatorics.antidiagonalTuplePairCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Combinatorics.antidiagonalTuplePairCount ``Submission.DifferentialGeometry.Combinatorics.antidiagonalTuplePairCount

lemma antidiagonalTuplePairCount_nonneg (m1 m2 : ℕ) : 0 ≤ antidiagonalTuplePairCount m1 m2 :=
  Finset.sum_nonneg fun k1 _ => Finset.sum_nonneg fun k2 _ =>
    mul_nonneg (antidiagonalTupleGridCount_nonneg k1) (antidiagonalTupleGridCount_nonneg k2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Combinatorics.antidiagonalTuplePairCount_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Combinatorics.antidiagonalTuplePairCount_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Combinatorics.antidiagonalTuplePairCount_nonneg ``Submission.DifferentialGeometry.Combinatorics.antidiagonalTuplePairCount_nonneg

lemma antidiagonalTupleGridPartialSum_mul_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (m1 m2 m3 : ℕ)
    (h3 : m1 + m2 ≤ m3 + 1) :
    antidiagonalTupleGridPartialSum b m1 * antidiagonalTupleGridPartialSum b m2 ≤
      antidiagonalTuplePairCount m1 m2 * antidiagonalTupleGridPartialSum b m3 := by
  classical
  have hG_nn : ∀ k, 0 ≤ Combinatorics.antidiagonalTupleGrid b k :=
    fun k => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  rw [antidiagonalTupleGridPartialSum, antidiagonalTupleGridPartialSum, Finset.sum_mul]
  rw [antidiagonalTuplePairCount, Finset.sum_mul]
  refine Finset.sum_le_sum fun k1 hk1 => ?_
  calc Combinatorics.antidiagonalTupleGrid b k1 *
        ∑ k ∈ Finset.range m2, Combinatorics.antidiagonalTupleGrid b k
      = ∑ k2 ∈ Finset.range m2, Combinatorics.antidiagonalTupleGrid b k1 *
          Combinatorics.antidiagonalTupleGrid b k2 := by rw [Finset.mul_sum]
    _ ≤ ∑ k2 ∈ Finset.range m2, (antidiagonalTupleGridCount k1 * antidiagonalTupleGridCount k2) *
          antidiagonalTupleGridPartialSum b m3 := by
        refine Finset.sum_le_sum fun k2 hk2 => ?_
        refine le_trans (antidiagonalTupleGrid_mul_le b hb k1 k2) ?_
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (antidiagonalTupleGridCount_nonneg k1) (antidiagonalTupleGridCount_nonneg k2))
        refine antidiagonalTupleGrid_le_partialSum b hb ?_
        rw [Finset.mem_range] at hk1 hk2
        omega
    _ = (∑ k2 ∈ Finset.range m2, antidiagonalTupleGridCount k1 * antidiagonalTupleGridCount k2) *
          antidiagonalTupleGridPartialSum b m3 := by
        rw [Finset.sum_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Combinatorics.antidiagonalTupleGridPartialSum_mul_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Combinatorics.antidiagonalTupleGridPartialSum_mul_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Combinatorics.antidiagonalTupleGridPartialSum_mul_le ``Submission.DifferentialGeometry.Combinatorics.antidiagonalTupleGridPartialSum_mul_le

end DifferentialGeometry.Combinatorics

end
