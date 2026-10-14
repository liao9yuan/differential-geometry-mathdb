import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharP.Two

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Finset

namespace DifferentialGeometry.Topology.PiecewiseLinear

def sidePartialSum {n : ℕ} (τ : Fin n → ZMod 2) : ℕ → ZMod 2
  | 0 => 0
  | k + 1 => sidePartialSum τ k + (if h : k < n then τ ⟨k, h⟩ else 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.sidePartialSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.sidePartialSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.sidePartialSum ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.sidePartialSum

theorem exists_sideChoice_of_chain {n : ℕ} (τ : Fin n → ZMod 2) :
    ∃ ε : Fin (n + 1) → ZMod 2, ∀ i : Fin n, ε i.succ = ε i.castSucc + τ i := by
  refine ⟨fun i => sidePartialSum τ i.val, ?_⟩
  intro i
  change sidePartialSum τ (i.val + 1) = sidePartialSum τ i.val + τ i
  simp only [sidePartialSum, dif_pos i.isLt]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_sideChoice_of_chain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_sideChoice_of_chain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_sideChoice_of_chain ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_sideChoice_of_chain

theorem sum_sideJump_eq_zero_of_cycle {n : ℕ} [NeZero n] (τ ε : Fin n → ZMod 2)
    (hcyc : ∀ i : Fin n, τ i = ε i + ε (i + 1)) :
    ∑ i, τ i = 0 := by
  have h1 : ∑ i, τ i = (∑ i, ε i) + ∑ i : Fin n, ε (i + 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hcyc i
  have h2 : ∑ i : Fin n, ε (i + 1) = ∑ i, ε i :=
    Fintype.sum_equiv (Equiv.addRight (1 : Fin n)) _ _ fun i => rfl
  rw [h1, h2, CharTwo.add_self_eq_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.sum_sideJump_eq_zero_of_cycle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.sum_sideJump_eq_zero_of_cycle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.sum_sideJump_eq_zero_of_cycle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.sum_sideJump_eq_zero_of_cycle

theorem not_exists_sideChoice_of_cycle {n : ℕ} [NeZero n] (τ : Fin n → ZMod 2)
    (hsum : ∑ i, τ i ≠ 0) :
    ¬∃ ε : Fin n → ZMod 2, ∀ i : Fin n, τ i = ε i + ε (i + 1) := by
  rintro ⟨ε, hε⟩
  exact hsum (sum_sideJump_eq_zero_of_cycle τ ε hε)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.not_exists_sideChoice_of_cycle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.not_exists_sideChoice_of_cycle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.not_exists_sideChoice_of_cycle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.not_exists_sideChoice_of_cycle

end DifferentialGeometry.Topology.PiecewiseLinear
