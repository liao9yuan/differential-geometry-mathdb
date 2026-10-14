import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Order.Lattice
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission







noncomputable section

open _root_.Set _root_.Function
open scoped _root_.Topology

namespace DifferentialGeometry.Topology


def cubeRadius (n : ℕ) (v : Fin (n + 1) → unitInterval) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |2 * (v i).val - 1|)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeRadius ``Submission.DifferentialGeometry.Topology.cubeRadius


theorem cubeRadius_coordinate_le (n : ℕ) (v : Fin (n + 1) → unitInterval) (i : Fin (n + 1)) :
    |2 * (v i).val - 1| ≤ cubeRadius n v :=
  Finset.le_sup' (fun i => |2 * (v i).val - 1|) (Finset.mem_univ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeRadius_coordinate_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeRadius_coordinate_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeRadius_coordinate_le ``Submission.DifferentialGeometry.Topology.cubeRadius_coordinate_le

theorem cubeRadius_nonneg (n : ℕ) (v : Fin (n + 1) → unitInterval) : 0 ≤ cubeRadius n v :=
  (abs_nonneg _).trans (cubeRadius_coordinate_le n v 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeRadius_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeRadius_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeRadius_nonneg ``Submission.DifferentialGeometry.Topology.cubeRadius_nonneg

theorem cubeRadius_le_one (n : ℕ) (v : Fin (n + 1) → unitInterval) : cubeRadius n v ≤ 1 := by
  apply Finset.sup'_le
  intro i _
  exact abs_le.mpr ⟨by linarith [(v i).property.1], by linarith [(v i).property.2]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeRadius_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeRadius_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeRadius_le_one ``Submission.DifferentialGeometry.Topology.cubeRadius_le_one


theorem continuous_cubeRadius (n : ℕ) : Continuous (cubeRadius n) := by
  apply Continuous.finset_sup'_apply
  intro i _
  exact ((continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))).sub
    continuous_const).abs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.continuous_cubeRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.continuous_cubeRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.continuous_cubeRadius ``Submission.DifferentialGeometry.Topology.continuous_cubeRadius


theorem cubeRadius_attained (n : ℕ) (v : Fin (n + 1) → unitInterval) :
    ∃ i : Fin (n + 1), cubeRadius n v = |2 * (v i).val - 1| := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty
    (fun i => |2 * (v i).val - 1|)
  exact ⟨i, hi⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeRadius_attained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeRadius_attained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeRadius_attained ``Submission.DifferentialGeometry.Topology.cubeRadius_attained


theorem cubeRadius_eq_one_iff (n : ℕ) (v : Fin (n + 1) → unitInterval) :
    cubeRadius n v = 1 ↔ v ∈ Cube.boundary (Fin (n + 1)) := by
  constructor
  · intro hr
    obtain ⟨i, hi⟩ := cubeRadius_attained n v
    rw [hr] at hi
    have hab := abs_eq (show (0 : ℝ) ≤ 1 by norm_num) |>.mp hi.symm
    refine ⟨i, ?_⟩
    rcases hab with h | h
    · exact Or.inr (Subtype.ext (show (v i).val = (1 : ℝ) by linarith))
    · exact Or.inl (Subtype.ext (show (v i).val = (0 : ℝ) by linarith))
  · rintro ⟨i, hi | hi⟩
    all_goals
      apply le_antisymm (cubeRadius_le_one n v)
      have h := cubeRadius_coordinate_le n v i
      rw [hi] at h
    · change |2 * (0 : ℝ) - 1| ≤ cubeRadius n v at h
      norm_num at h
      exact h
    · change |2 * (1 : ℝ) - 1| ≤ cubeRadius n v at h
      norm_num at h
      exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.cubeRadius_eq_one_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.cubeRadius_eq_one_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.cubeRadius_eq_one_iff ``Submission.DifferentialGeometry.Topology.cubeRadius_eq_one_iff

end DifferentialGeometry.Topology
