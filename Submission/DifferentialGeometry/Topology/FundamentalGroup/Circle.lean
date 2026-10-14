/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.ZMultiples
import Submission.DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import Submission.DifferentialGeometry.Topology.FundamentalGroup.Product

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.AddSubgroup

universe u

namespace DifferentialGeometry.Topology

noncomputable def intEquivZMultiplesOne : ℤ ≃+ _root_.AddSubgroup.zmultiples (1 : ℝ) :=
  AddEquiv.ofBijective
    ((Int.castAddHom ℝ).codRestrict (_root_.AddSubgroup.zmultiples (1 : ℝ))
      (fun n ↦ _root_.AddSubgroup.intCast_mem_zmultiples_one (R := ℝ) n)) <| by
    constructor
    · intro m n h
      have hr : (m : ℝ) = (n : ℝ) := congrArg Subtype.val h
      exact Int.cast_injective hr
    · rintro ⟨x, hx⟩
      rw [_root_.AddSubgroup.mem_zmultiples_iff] at hx
      obtain ⟨n, hn⟩ := hx
      refine ⟨n, Subtype.ext ?_⟩
      change (n : ℝ) = x
      simpa using hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.intEquivZMultiplesOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.intEquivZMultiplesOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.intEquivZMultiplesOne ``Submission.DifferentialGeometry.Topology.intEquivZMultiplesOne

noncomputable def fundamentalGroupUnitAddCircleEquivInt :
    FundamentalGroup (AddCircle (1 : ℝ)) 0 ≃* Multiplicative ℤ :=
  ((AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)).fundamentalGroupEquiv
      (⟨0, rfl⟩ : ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' {0})).trans
    (MulOpposite.opMulEquiv.symm.trans intEquivZMultiplesOne.toMultiplicative.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroupUnitAddCircleEquivInt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroupUnitAddCircleEquivInt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroupUnitAddCircleEquivInt ``Submission.DifferentialGeometry.Topology.fundamentalGroupUnitAddCircleEquivInt

noncomputable def fundamentalGroupCircleEquivInt :
    FundamentalGroup Circle (1 : Circle) ≃* Multiplicative ℤ :=
  (fundamentalGroupMulEquivOfHomotopyEquiv
      (AddCircle.homeomorphCircle one_ne_zero).toHomotopyEquiv
      (0 : AddCircle (1 : ℝ)) (1 : Circle) (by
        change AddCircle.homeomorphCircle one_ne_zero 0 = 1
        rw [AddCircle.homeomorphCircle_apply]
        exact AddCircle.toCircle_zero)).symm.trans
    fundamentalGroupUnitAddCircleEquivInt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroupCircleEquivInt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroupCircleEquivInt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroupCircleEquivInt ``Submission.DifferentialGeometry.Topology.fundamentalGroupCircleEquivInt

noncomputable def fundamentalGroupProdCircleEquivIntOfSimplyConnected
    {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    FundamentalGroup (X × Circle) (x, 1) ≃* Multiplicative ℤ :=
  (fundamentalGroupProdRightEquivOfSimplyConnected x (1 : Circle)).trans
    fundamentalGroupCircleEquivInt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroupProdCircleEquivIntOfSimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroupProdCircleEquivIntOfSimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroupProdCircleEquivIntOfSimplyConnected ``Submission.DifferentialGeometry.Topology.fundamentalGroupProdCircleEquivIntOfSimplyConnected

end DifferentialGeometry.Topology
