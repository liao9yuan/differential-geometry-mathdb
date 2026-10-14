/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory
open scoped _root_.ContinuousMap

universe u v

namespace DifferentialGeometry.Topology

theorem fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) (y : Y) (h : e x = y) :
    Function.Bijective (FundamentalGroup.mapOfEq e.toFun h) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  have hmap : Function.Bijective (FundamentalGroup.map e.toFun x) := by
    change Function.Bijective (E.functor.map :
      (FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x) →
        (E.functor.obj (FundamentalGroupoid.mk x) ⟶
          E.functor.obj (FundamentalGroupoid.mk x)))
    exact E.fullyFaithfulFunctor.map_bijective _ _
  have hconj : Function.Bijective
      (_root_.CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk h)).conj.toMonoidHom :=
    (_root_.CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk h)).conj.bijective
  exact hconj.comp hmap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv ``Submission.DifferentialGeometry.Topology.fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv

noncomputable def fundamentalGroupMulEquivOfHomotopyEquiv
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) (y : Y) (h : e x = y) :
    FundamentalGroup X x ≃* FundamentalGroup Y y :=
  MulEquiv.ofBijective (FundamentalGroup.mapOfEq e.toFun h)
    (fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv e x y h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv ``Submission.DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv

theorem fundamentalGroupMulEquivOfHomotopyEquiv_toMonoidHom
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) (y : Y) (h : e x = y) :
    (↑(fundamentalGroupMulEquivOfHomotopyEquiv e x y h) :
      FundamentalGroup X x →* FundamentalGroup Y y) =
        FundamentalGroup.mapOfEq e.toFun h := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv_toMonoidHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv_toMonoidHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv_toMonoidHom ``Submission.DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv_toMonoidHom

end DifferentialGeometry.Topology
