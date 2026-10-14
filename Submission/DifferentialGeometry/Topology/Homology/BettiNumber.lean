/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homology.HomotopyEquivalence
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.AlgebraicTopology

namespace DifferentialGeometry.Homology

universe u

noncomputable def bettiNumber (k : Type u) [Field k] (X : TopCat.{u}) (n : ℕ) : ℕ :=
  Module.finrank k (((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.bettiNumber then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.bettiNumber"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.bettiNumber ``Submission.DifferentialGeometry.Homology.bettiNumber

theorem bettiNumber_eq_of_isIso (k : Type u) [Field k] {X Y : TopCat.{u}}
    (n : ℕ) (f : X ⟶ Y)
    [_root_.CategoryTheory.IsIso (((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map f)] :
    bettiNumber k X n = bettiNumber k Y n :=
  (_root_.CategoryTheory.asIso (((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
      f)).toLinearEquiv.finrank_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.bettiNumber_eq_of_isIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.bettiNumber_eq_of_isIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.bettiNumber_eq_of_isIso ``Submission.DifferentialGeometry.Homology.bettiNumber_eq_of_isIso

theorem bettiNumber_eq_of_homotopyEquiv (k : Type u) [Field k] {X Y : TopCat.{u}}
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) : bettiNumber k X n = bettiNumber k Y n := by
  let _ := isIso_singularHomologyMap_of_homotopyEquiv (ModuleCat.of k k) e n
  exact bettiNumber_eq_of_isIso k n (TopCat.ofHom e.toFun)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.bettiNumber_eq_of_homotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.bettiNumber_eq_of_homotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.bettiNumber_eq_of_homotopyEquiv ``Submission.DifferentialGeometry.Homology.bettiNumber_eq_of_homotopyEquiv

noncomputable def bettiOne (X : Type) [TopologicalSpace X] : ℕ :=
  bettiNumber ℚ (TopCat.of X) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.bettiOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.bettiOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.bettiOne ``Submission.DifferentialGeometry.Homology.bettiOne

theorem bettiNumber_zero_of_pathConnectedSpace (k : Type u) [Field k]
    (X : TopCat.{u}) [PathConnectedSpace X] : bettiNumber k X 0 = 1 := by
  have h := (_root_.CategoryTheory.asIso (X.singularHomology₀ε (ModuleCat.of k k))).toLinearEquiv.finrank_eq
  simpa only [bettiNumber, Module.finrank_self] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.bettiNumber_zero_of_pathConnectedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.bettiNumber_zero_of_pathConnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.bettiNumber_zero_of_pathConnectedSpace ``Submission.DifferentialGeometry.Homology.bettiNumber_zero_of_pathConnectedSpace

end DifferentialGeometry.Homology
