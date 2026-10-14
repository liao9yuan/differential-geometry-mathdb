/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Submission.DifferentialGeometry.Topology.VanKampen.Based

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory _root_.Set

universe u

namespace DifferentialGeometry.Topology.VanKampen

noncomputable def pushoutInlMulEquivOfIsIso
    {Z X Y P : GrpCat.{u}} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (h : _root_.CategoryTheory.IsPushout f g inl inr) [_root_.CategoryTheory.IsIso g] : X ≃* P := by
  letI : _root_.CategoryTheory.IsIso inl := h.isIso_inl_of_isIso
  exact CategoryTheory.Iso.groupIsoToMulEquiv (_root_.CategoryTheory.asIso inl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.pushoutInlMulEquivOfIsIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.pushoutInlMulEquivOfIsIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.pushoutInlMulEquivOfIsIso ``Submission.DifferentialGeometry.Topology.VanKampen.pushoutInlMulEquivOfIsIso

@[simp]
theorem pushoutInlMulEquivOfIsIso_toMonoidHom
    {Z X Y P : GrpCat.{u}} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (h : _root_.CategoryTheory.IsPushout f g inl inr) [_root_.CategoryTheory.IsIso g] :
    (↑(pushoutInlMulEquivOfIsIso h) : X →* P) = inl.hom := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.pushoutInlMulEquivOfIsIso_toMonoidHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.pushoutInlMulEquivOfIsIso_toMonoidHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.pushoutInlMulEquivOfIsIso_toMonoidHom ``Submission.DifferentialGeometry.Topology.VanKampen.pushoutInlMulEquivOfIsIso_toMonoidHom

noncomputable def fundamentalGroupLeftToAmbientEquivOfSimplyConnected
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace U]
    [SimplyConnectedSpace V] [SimplyConnectedSpace (↑(U ∩ V))] :
    FundamentalGroup U (leftBasepoint U x₀ hx₀.1) ≃* FundamentalGroup X x₀ := by
  let g := fundamentalGroupInterToRight U V x₀ hx₀
  have hg : Function.Bijective g := by
    constructor
    · intro a b _
      exact Subsingleton.elim a b
    · intro y
      exact ⟨1, Subsingleton.elim _ y⟩
  letI : _root_.CategoryTheory.IsIso g := (ConcreteCategory.isIso_iff_bijective g).2 hg
  exact pushoutInlMulEquivOfIsIso
    (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbientEquivOfSimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbientEquivOfSimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbientEquivOfSimplyConnected ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbientEquivOfSimplyConnected

@[simp]
theorem fundamentalGroupLeftToAmbientEquivOfSimplyConnected_toMonoidHom
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace U]
    [SimplyConnectedSpace V] [SimplyConnectedSpace (↑(U ∩ V))] :
    (↑(fundamentalGroupLeftToAmbientEquivOfSimplyConnected
      U V hU hV hcover x₀ hx₀) :
        FundamentalGroup U (leftBasepoint U x₀ hx₀.1) →* FundamentalGroup X x₀) =
        (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbientEquivOfSimplyConnected_toMonoidHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbientEquivOfSimplyConnected_toMonoidHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbientEquivOfSimplyConnected_toMonoidHom ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbientEquivOfSimplyConnected_toMonoidHom

noncomputable def fundamentalGroupRightToAmbientEquivOfSimplyConnected
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace V]
    [SimplyConnectedSpace U] [SimplyConnectedSpace (↑(U ∩ V))] :
    FundamentalGroup V (rightBasepoint V x₀ hx₀.2) ≃* FundamentalGroup X x₀ := by
  let f := fundamentalGroupInterToLeft U V x₀ hx₀
  have hf : Function.Bijective f := by
    constructor
    · intro a b _
      exact Subsingleton.elim a b
    · intro y
      exact ⟨1, Subsingleton.elim _ y⟩
  letI : _root_.CategoryTheory.IsIso f := (ConcreteCategory.isIso_iff_bijective f).2 hf
  letI : _root_.CategoryTheory.IsIso (fundamentalGroupRightToAmbient V x₀ hx₀.2) :=
    (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀).isIso_inr_of_isIso
  exact CategoryTheory.Iso.groupIsoToMulEquiv
    (_root_.CategoryTheory.asIso (fundamentalGroupRightToAmbient V x₀ hx₀.2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbientEquivOfSimplyConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbientEquivOfSimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbientEquivOfSimplyConnected ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbientEquivOfSimplyConnected

@[simp]
theorem fundamentalGroupRightToAmbientEquivOfSimplyConnected_toMonoidHom
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) [PathConnectedSpace V]
    [SimplyConnectedSpace U] [SimplyConnectedSpace (↑(U ∩ V))] :
    (↑(fundamentalGroupRightToAmbientEquivOfSimplyConnected
      U V hU hV hcover x₀ hx₀) :
        FundamentalGroup V (rightBasepoint V x₀ hx₀.2) →* FundamentalGroup X x₀) =
        (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbientEquivOfSimplyConnected_toMonoidHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbientEquivOfSimplyConnected_toMonoidHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbientEquivOfSimplyConnected_toMonoidHom ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbientEquivOfSimplyConnected_toMonoidHom

end DifferentialGeometry.Topology.VanKampen
