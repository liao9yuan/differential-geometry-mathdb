/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Submission.DifferentialGeometry.Topology.FundamentalGroup.BasepointChange
import Submission.DifferentialGeometry.Topology.VanKampen.HomotopyEquivalentFreeProductCover

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

noncomputable def fundamentalGroupSourceFactorEquivOfConnectors
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (βU : Path (leftBasepoint U x₀ hx₀.1) (eU k₀))
    (eV : L ≃ₕ V) (βV : Path (rightBasepoint V x₀ hx₀.2) (eV l₀)) :
    ∀ i, fundamentalGroupSourceFactor k₀ l₀ i ≃*
      fundamentalGroupFactor U V x₀ hx₀ i
  | false =>
      (DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
        eU k₀ (eU k₀) rfl).trans
        (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint βU)
  | true =>
      (DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
        eV l₀ (eV l₀) rfl).trans
        (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint βV)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquivOfConnectors then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquivOfConnectors"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquivOfConnectors ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquivOfConnectors

theorem fundamentalGroupSourceFactorEquivOfConnectors_false_toMonoidHom
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (βU : Path (leftBasepoint U x₀ hx₀.1) (eU k₀))
    (eV : L ≃ₕ V) (βV : Path (rightBasepoint V x₀ hx₀.2) (eV l₀)) :
    (↑(fundamentalGroupSourceFactorEquivOfConnectors
      U V x₀ hx₀ k₀ l₀ eU βU eV βV _root_.Bool.false) :
        FundamentalGroup K k₀ →*
          FundamentalGroup U (leftBasepoint U x₀ hx₀.1)) =
      (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint βU).toMonoidHom.comp
        (FundamentalGroup.mapOfEq eU.toFun rfl) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquivOfConnectors_false_toMonoidHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquivOfConnectors_false_toMonoidHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquivOfConnectors_false_toMonoidHom ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquivOfConnectors_false_toMonoidHom

theorem fundamentalGroupSourceFactorEquivOfConnectors_true_toMonoidHom
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (βU : Path (leftBasepoint U x₀ hx₀.1) (eU k₀))
    (eV : L ≃ₕ V) (βV : Path (rightBasepoint V x₀ hx₀.2) (eV l₀)) :
    (↑(fundamentalGroupSourceFactorEquivOfConnectors
      U V x₀ hx₀ k₀ l₀ eU βU eV βV _root_.Bool.true) :
        FundamentalGroup L l₀ →*
          FundamentalGroup V (rightBasepoint V x₀ hx₀.2)) =
      (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint βV).toMonoidHom.comp
        (FundamentalGroup.mapOfEq eV.toFun rfl) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquivOfConnectors_true_toMonoidHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquivOfConnectors_true_toMonoidHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquivOfConnectors_true_toMonoidHom ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupSourceFactorEquivOfConnectors_true_toMonoidHom

noncomputable def fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (βU : Path (leftBasepoint U x₀ hx₀.1) (eU k₀))
    (eV : L ≃ₕ V) (βV : Path (rightBasepoint V x₀ hx₀.2) (eV l₀))
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupSourceFreeProduct k₀ l₀ ≃* FundamentalGroup X x₀ :=
  (DifferentialGeometry.Algebra.Group.coprodIMulEquiv
      (fundamentalGroupSourceFactor k₀ l₀)
      (fundamentalGroupFactor U V x₀ hx₀)
      (fundamentalGroupSourceFactorEquivOfConnectors
        U V x₀ hx₀ k₀ l₀ eU βU eV βV)).trans
    (fundamentalGroupEquivFreeProduct U V hU hV hcover x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors

theorem fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors_comp_left
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (βU : Path (leftBasepoint U x₀ hx₀.1) (eU k₀))
    (eV : L ≃ₕ V) (βV : Path (rightBasepoint V x₀ hx₀.2) (eV l₀))
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    (↑(fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors
      U V hU hV hcover x₀ hx₀ k₀ l₀ eU βU eV βV) :
        fundamentalGroupSourceFreeProduct k₀ l₀ →* FundamentalGroup X x₀).comp
      (Monoid.CoprodI.of (M := fundamentalGroupSourceFactor k₀ l₀) (i := _root_.Bool.false)) =
      (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom.comp
        ((DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint βU).toMonoidHom.comp
          (FundamentalGroup.mapOfEq eU.toFun rfl)) := by
  ext g
  change (fundamentalGroupEquivFreeProduct U V hU hV hcover x₀ hx₀)
      (Monoid.CoprodI.of (M := fundamentalGroupFactor U V x₀ hx₀) (i := _root_.Bool.false)
        (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint βU
          (FundamentalGroup.mapOfEq eU.toFun rfl g))) = _
  simpa only [MonoidHom.comp_apply, fundamentalGroupFreeProductLeft,
    GrpCat.hom_ofHom, MulEquiv.coe_toMonoidHom] using DFunLike.congr_fun
      (fundamentalGroupEquivFreeProduct_comp_left U V hU hV hcover x₀ hx₀)
      (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint βU
        (FundamentalGroup.mapOfEq eU.toFun rfl g))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors_comp_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors_comp_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors_comp_left ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors_comp_left

theorem fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors_comp_right
    {K L X : Type u} [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) (k₀ : K) (l₀ : L)
    (eU : K ≃ₕ U) (βU : Path (leftBasepoint U x₀ hx₀.1) (eU k₀))
    (eV : L ≃ₕ V) (βV : Path (rightBasepoint V x₀ hx₀.2) (eV l₀))
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    (↑(fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors
      U V hU hV hcover x₀ hx₀ k₀ l₀ eU βU eV βV) :
        fundamentalGroupSourceFreeProduct k₀ l₀ →* FundamentalGroup X x₀).comp
      (Monoid.CoprodI.of (M := fundamentalGroupSourceFactor k₀ l₀) (i := _root_.Bool.true)) =
      (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom.comp
        ((DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint βV).toMonoidHom.comp
          (FundamentalGroup.mapOfEq eV.toFun rfl)) := by
  ext g
  change (fundamentalGroupEquivFreeProduct U V hU hV hcover x₀ hx₀)
      (Monoid.CoprodI.of (M := fundamentalGroupFactor U V x₀ hx₀) (i := _root_.Bool.true)
        (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint βV
          (FundamentalGroup.mapOfEq eV.toFun rfl g))) = _
  simpa only [MonoidHom.comp_apply, fundamentalGroupFreeProductRight,
    GrpCat.hom_ofHom, MulEquiv.coe_toMonoidHom] using DFunLike.congr_fun
      (fundamentalGroupEquivFreeProduct_comp_right U V hU hV hcover x₀ hx₀)
      (DifferentialGeometry.Topology.fundamentalGroupChangeBasepoint βV
        (FundamentalGroup.mapOfEq eV.toFun rfl g))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors_comp_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors_comp_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors_comp_right ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProductOfHomotopyEquivOfConnectors_comp_right

end DifferentialGeometry.Topology.VanKampen
