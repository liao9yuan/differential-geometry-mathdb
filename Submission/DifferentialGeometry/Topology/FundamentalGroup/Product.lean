/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Product
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

universe u v

namespace DifferentialGeometry.Topology

noncomputable def fundamentalGroupProdEquiv
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) :
    FundamentalGroup (X × Y) (x, y) ≃*
      FundamentalGroup X x × FundamentalGroup Y y :=
  MulEquiv.ofBijective
    ((FundamentalGroup.map ContinuousMap.fst (x, y)).prod
      (FundamentalGroup.map ContinuousMap.snd (x, y))) <| by
    constructor
    · intro p q hpq
      have hleft : Path.Homotopic.projLeft p = Path.Homotopic.projLeft q :=
        congrArg Prod.fst hpq
      have hright : Path.Homotopic.projRight p = Path.Homotopic.projRight q :=
        congrArg Prod.snd hpq
      rw [← Path.Homotopic.prod_projLeft_projRight p,
        ← Path.Homotopic.prod_projLeft_projRight q]
      exact congrArg₂ Path.Homotopic.prod hleft hright
    · rintro ⟨p, q⟩
      refine ⟨Path.Homotopic.prod p q, ?_⟩
      exact Prod.ext (Path.Homotopic.projLeft_prod p q)
        (Path.Homotopic.projRight_prod p q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroupProdEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroupProdEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroupProdEquiv ``Submission.DifferentialGeometry.Topology.fundamentalGroupProdEquiv

theorem fundamentalGroupProdEquiv_apply
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (p : FundamentalGroup (X × Y) (x, y)) :
    fundamentalGroupProdEquiv x y p =
      (Path.Homotopic.projLeft p, Path.Homotopic.projRight p) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroupProdEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroupProdEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroupProdEquiv_apply ``Submission.DifferentialGeometry.Topology.fundamentalGroupProdEquiv_apply

theorem fundamentalGroupProdEquiv_symm_apply
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (p : FundamentalGroup X x) (q : FundamentalGroup Y y) :
    (fundamentalGroupProdEquiv x y).symm (p, q) = Path.Homotopic.prod p q := by
  apply (fundamentalGroupProdEquiv x y).injective
  rw [MulEquiv.apply_symm_apply]
  exact Prod.ext (Path.Homotopic.projLeft_prod p q).symm
    (Path.Homotopic.projRight_prod p q).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroupProdEquiv_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroupProdEquiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroupProdEquiv_symm_apply ``Submission.DifferentialGeometry.Topology.fundamentalGroupProdEquiv_symm_apply

noncomputable def fundamentalGroupProdRightEquivOfSimplyConnected
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] (x : X) (y : Y) :
    FundamentalGroup (X × Y) (x, y) ≃* FundamentalGroup Y y :=
  MulEquiv.ofBijective (FundamentalGroup.map ContinuousMap.snd (x, y)) <| by
    constructor
    · intro p q hpq
      rw [← Path.Homotopic.prod_projLeft_projRight p,
        ← Path.Homotopic.prod_projLeft_projRight q]
      exact congrArg₂ Path.Homotopic.prod (Subsingleton.elim _ _) hpq
    · intro q
      refine ⟨Path.Homotopic.prod (1 : FundamentalGroup X x) q, ?_⟩
      exact Path.Homotopic.projRight_prod (1 : FundamentalGroup X x) q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroupProdRightEquivOfSimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroupProdRightEquivOfSimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroupProdRightEquivOfSimplyConnected ``Submission.DifferentialGeometry.Topology.fundamentalGroupProdRightEquivOfSimplyConnected

theorem fundamentalGroupProdRightEquivOfSimplyConnected_toMonoidHom
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] (x : X) (y : Y) :
    (↑(fundamentalGroupProdRightEquivOfSimplyConnected x y) :
      FundamentalGroup (X × Y) (x, y) →* FundamentalGroup Y y) =
        FundamentalGroup.map ContinuousMap.snd (x, y) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroupProdRightEquivOfSimplyConnected_toMonoidHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroupProdRightEquivOfSimplyConnected_toMonoidHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroupProdRightEquivOfSimplyConnected_toMonoidHom ``Submission.DifferentialGeometry.Topology.fundamentalGroupProdRightEquivOfSimplyConnected_toMonoidHom

theorem fundamentalGroupProdRightEquivOfSimplyConnected_symm_apply
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] (x : X) (y : Y) (q : FundamentalGroup Y y) :
    (fundamentalGroupProdRightEquivOfSimplyConnected x y).symm q =
      Path.Homotopic.prod (1 : FundamentalGroup X x) q := by
  apply (fundamentalGroupProdRightEquivOfSimplyConnected x y).injective
  rw [MulEquiv.apply_symm_apply]
  exact (Path.Homotopic.projRight_prod (1 : FundamentalGroup X x) q).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.fundamentalGroupProdRightEquivOfSimplyConnected_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.fundamentalGroupProdRightEquivOfSimplyConnected_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.fundamentalGroupProdRightEquivOfSimplyConnected_symm_apply ``Submission.DifferentialGeometry.Topology.fundamentalGroupProdRightEquivOfSimplyConnected_symm_apply

end DifferentialGeometry.Topology
