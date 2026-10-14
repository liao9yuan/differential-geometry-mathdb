/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Submission.DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import Submission.DifferentialGeometry.Topology.VanKampen.FreeProduct

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set
open scoped _root_.ContinuousMap

universe u

namespace DifferentialGeometry.Topology.VanKampen

abbrev fundamentalGroupSourceFactor
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (k₀ : K) (l₀ : L) : Bool → Type u
  | false => FundamentalGroup K k₀
  | true => FundamentalGroup L l₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactor ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactor

noncomputable instance fundamentalGroupSourceFactorGroup
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (k₀ : K) (l₀ : L) (i : Bool) :
    Group (fundamentalGroupSourceFactor k₀ l₀ i) := by
  cases i <;> simp only [fundamentalGroupSourceFactor] <;> infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorGroup ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorGroup

abbrev fundamentalGroupSourceFreeProduct
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (k₀ : K) (l₀ : L) :=
  Monoid.CoprodI (fundamentalGroupSourceFactor k₀ l₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFreeProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFreeProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFreeProduct ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFreeProduct

noncomputable def fundamentalGroupSourceFactorEquiv
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (hbaseU : eU k₀ = leftBasepoint U x₀ hx₀.1)
    (eV : L ≃ₕ V) (hbaseV : eV l₀ = rightBasepoint V x₀ hx₀.2) :
    ∀ i, fundamentalGroupSourceFactor k₀ l₀ i ≃*
      fundamentalGroupFactor U V x₀ hx₀ i
  | false => DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
      eU k₀ (leftBasepoint U x₀ hx₀.1) hbaseU
  | true => DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
      eV l₀ (rightBasepoint V x₀ hx₀.2) hbaseV

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquiv ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquiv

theorem fundamentalGroupSourceFactorEquiv_false_toMonoidHom
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (hbaseU : eU k₀ = leftBasepoint U x₀ hx₀.1)
    (eV : L ≃ₕ V) (hbaseV : eV l₀ = rightBasepoint V x₀ hx₀.2) :
    (↑(fundamentalGroupSourceFactorEquiv
      U V x₀ hx₀ k₀ l₀ eU hbaseU eV hbaseV _root_.Bool.false) :
        FundamentalGroup K k₀ →*
          FundamentalGroup U (leftBasepoint U x₀ hx₀.1)) =
      FundamentalGroup.mapOfEq eU.toFun hbaseU := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquiv_false_toMonoidHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquiv_false_toMonoidHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquiv_false_toMonoidHom ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquiv_false_toMonoidHom

theorem fundamentalGroupSourceFactorEquiv_true_toMonoidHom
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (hbaseU : eU k₀ = leftBasepoint U x₀ hx₀.1)
    (eV : L ≃ₕ V) (hbaseV : eV l₀ = rightBasepoint V x₀ hx₀.2) :
    (↑(fundamentalGroupSourceFactorEquiv
      U V x₀ hx₀ k₀ l₀ eU hbaseU eV hbaseV _root_.Bool.true) :
        FundamentalGroup L l₀ →*
          FundamentalGroup V (rightBasepoint V x₀ hx₀.2)) =
      FundamentalGroup.mapOfEq eV.toFun hbaseV := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquiv_true_toMonoidHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquiv_true_toMonoidHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquiv_true_toMonoidHom ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquiv_true_toMonoidHom

noncomputable def fundamentalGroupEquivFreeProductOfHomotopyEquiv
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (hbaseU : eU k₀ = leftBasepoint U x₀ hx₀.1)
    (eV : L ≃ₕ V) (hbaseV : eV l₀ = rightBasepoint V x₀ hx₀.2)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupSourceFreeProduct k₀ l₀ ≃* FundamentalGroup X x₀ :=
  (DifferentialGeometry.Algebra.Group.coprodIMulEquiv
      (fundamentalGroupSourceFactor k₀ l₀)
      (fundamentalGroupFactor U V x₀ hx₀)
      (fundamentalGroupSourceFactorEquiv U V x₀ hx₀ k₀ l₀ eU hbaseU eV hbaseV)).trans
    (fundamentalGroupEquivFreeProduct U V hU hV hcover x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquiv ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquiv

theorem fundamentalGroupEquivFreeProductOfHomotopyEquiv_comp_left
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (hbaseU : eU k₀ = leftBasepoint U x₀ hx₀.1)
    (eV : L ≃ₕ V) (hbaseV : eV l₀ = rightBasepoint V x₀ hx₀.2)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    (↑(fundamentalGroupEquivFreeProductOfHomotopyEquiv
      U V hU hV hcover x₀ hx₀ k₀ l₀ eU hbaseU eV hbaseV) :
        fundamentalGroupSourceFreeProduct k₀ l₀ →* FundamentalGroup X x₀).comp
      (Monoid.CoprodI.of (M := fundamentalGroupSourceFactor k₀ l₀) (i := _root_.Bool.false)) =
      (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom.comp
        (FundamentalGroup.mapOfEq eU.toFun hbaseU) := by
  ext g
  change (fundamentalGroupEquivFreeProduct U V hU hV hcover x₀ hx₀)
      (Monoid.CoprodI.of (M := fundamentalGroupFactor U V x₀ hx₀) (i := _root_.Bool.false)
        (FundamentalGroup.mapOfEq eU.toFun hbaseU g)) =
    (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom
      (FundamentalGroup.mapOfEq eU.toFun hbaseU g)
  simpa only [MonoidHom.comp_apply, fundamentalGroupFreeProductLeft,
    GrpCat.hom_ofHom, MulEquiv.coe_toMonoidHom] using DFunLike.congr_fun
      (fundamentalGroupEquivFreeProduct_comp_left U V hU hV hcover x₀ hx₀)
      (FundamentalGroup.mapOfEq eU.toFun hbaseU g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquiv_comp_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquiv_comp_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquiv_comp_left ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquiv_comp_left

theorem fundamentalGroupEquivFreeProductOfHomotopyEquiv_comp_right
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (hbaseU : eU k₀ = leftBasepoint U x₀ hx₀.1)
    (eV : L ≃ₕ V) (hbaseV : eV l₀ = rightBasepoint V x₀ hx₀.2)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    (↑(fundamentalGroupEquivFreeProductOfHomotopyEquiv
      U V hU hV hcover x₀ hx₀ k₀ l₀ eU hbaseU eV hbaseV) :
        fundamentalGroupSourceFreeProduct k₀ l₀ →* FundamentalGroup X x₀).comp
      (Monoid.CoprodI.of (M := fundamentalGroupSourceFactor k₀ l₀) (i := _root_.Bool.true)) =
      (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom.comp
        (FundamentalGroup.mapOfEq eV.toFun hbaseV) := by
  ext g
  change (fundamentalGroupEquivFreeProduct U V hU hV hcover x₀ hx₀)
      (Monoid.CoprodI.of (M := fundamentalGroupFactor U V x₀ hx₀) (i := _root_.Bool.true)
        (FundamentalGroup.mapOfEq eV.toFun hbaseV g)) =
    (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom
      (FundamentalGroup.mapOfEq eV.toFun hbaseV g)
  simpa only [MonoidHom.comp_apply, fundamentalGroupFreeProductRight,
    GrpCat.hom_ofHom, MulEquiv.coe_toMonoidHom] using DFunLike.congr_fun
      (fundamentalGroupEquivFreeProduct_comp_right U V hU hV hcover x₀ hx₀)
      (FundamentalGroup.mapOfEq eV.toFun hbaseV g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquiv_comp_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquiv_comp_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquiv_comp_right ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquiv_comp_right

end DifferentialGeometry.Topology.VanKampen
