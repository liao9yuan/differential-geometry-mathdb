/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.DiscreteSubset

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

open _root_.StrictMono in
theorem StrictMono.isDiscrete_range_nat
    {X : Type*} [LinearOrder X] [TopologicalSpace X] [OrderClosedTopology X]
    {f : ℕ → X} (hf : StrictMono f) : IsDiscrete (_root_.Set.range f) := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  rintro x ⟨n, rfl⟩
  cases n with
  | zero =>
    refine ⟨Iio (f 1), isOpen_Iio, Subset.antisymm ?_ ?_⟩
    · rintro y ⟨hy, j, rfl⟩
      have hj : j = 0 := by have := hf.lt_iff_lt.mp hy; omega
      exact congrArg f hj
    · exact singleton_subset_iff.mpr ⟨hf (by omega), _root_.Set.mem_range_self _⟩
  | succ n =>
    refine ⟨Ioo (f n) (f (n + 2)), isOpen_Ioo, Subset.antisymm ?_ ?_⟩
    · rintro y ⟨hy, j, rfl⟩
      have hj : j = n + 1 := by
        have := hf.lt_iff_lt.mp hy.1
        have := hf.lt_iff_lt.mp hy.2
        omega
      exact congrArg f hj
    · exact singleton_subset_iff.mpr ⟨⟨hf (by omega), hf (by omega)⟩, _root_.Set.mem_range_self _⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.StrictMono
  let env ← Lean.getEnv
  if env.contains `StrictMono.isDiscrete_range_nat then
    throwError "Refusing to shadow existing declaration StrictMono.isDiscrete_range_nat"
  Lean.modifyEnv fun env => Lean.addAlias env `StrictMono.isDiscrete_range_nat ``Submission.StrictMono.isDiscrete_range_nat

open _root_.StrictAnti in
theorem StrictAnti.isDiscrete_range_nat
    {X : Type*} [LinearOrder X] [TopologicalSpace X] [OrderClosedTopology X]
    {f : ℕ → X} (hf : StrictAnti f) : IsDiscrete (_root_.Set.range f) :=
  hf.dual_right.isDiscrete_range_nat

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.StrictAnti
  let env ← Lean.getEnv
  if env.contains `StrictAnti.isDiscrete_range_nat then
    throwError "Refusing to shadow existing declaration StrictAnti.isDiscrete_range_nat"
  Lean.modifyEnv fun env => Lean.addAlias env `StrictAnti.isDiscrete_range_nat ``Submission.StrictAnti.isDiscrete_range_nat
