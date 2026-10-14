/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Submission.DifferentialGeometry.Topology.Algebra.Group.FreeProduct
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Submission.DifferentialGeometry.Topology.VanKampen.AmalgamatedProduct

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory _root_.Set

universe u

namespace DifferentialGeometry.Topology.VanKampen

abbrev fundamentalGroupFreeProduct {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :=
  Monoid.CoprodI (fundamentalGroupFactor U V x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProduct ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProduct

noncomputable def fundamentalGroupFreeProductLeft {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    GrpCat.of (FundamentalGroup U (leftBasepoint U x₀ hx₀.1)) ⟶
      GrpCat.of (fundamentalGroupFreeProduct U V x₀ hx₀) :=
  GrpCat.ofHom (Monoid.CoprodI.of
    (M := fundamentalGroupFactor U V x₀ hx₀) (i := _root_.Bool.false))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProductLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProductLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProductLeft ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProductLeft

noncomputable def fundamentalGroupFreeProductRight {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    GrpCat.of (FundamentalGroup V (rightBasepoint V x₀ hx₀.2)) ⟶
      GrpCat.of (fundamentalGroupFreeProduct U V x₀ hx₀) :=
  GrpCat.ofHom (Monoid.CoprodI.of
    (M := fundamentalGroupFactor U V x₀ hx₀) (i := _root_.Bool.true))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProductRight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProductRight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProductRight ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProductRight

theorem fundamentalGroupFreeProduct_coverSquare_commutes
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [SimplyConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupInterToLeft U V x₀ hx₀ ≫
        fundamentalGroupFreeProductLeft U V x₀ hx₀ =
      fundamentalGroupInterToRight U V x₀ hx₀ ≫
        fundamentalGroupFreeProductRight U V x₀ hx₀ := by
  apply GrpCat.ext
  intro w
  change Monoid.CoprodI.of (M := fundamentalGroupFactor U V x₀ hx₀) (i := _root_.Bool.false)
      ((fundamentalGroupInterToLeft U V x₀ hx₀).hom w) =
    Monoid.CoprodI.of (M := fundamentalGroupFactor U V x₀ hx₀) (i := _root_.Bool.true)
      ((fundamentalGroupInterToRight U V x₀ hx₀).hom w)
  have hw : w = 1 := Subsingleton.elim _ _
  subst w
  simp only [map_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProduct_coverSquare_commutes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProduct_coverSquare_commutes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProduct_coverSquare_commutes ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProduct_coverSquare_commutes

noncomputable def freeProductToFundamentalGroup
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    GrpCat.of (fundamentalGroupFreeProduct U V x₀ hx₀) ⟶
      GrpCat.of (FundamentalGroup X x₀) :=
  GrpCat.ofHom (Monoid.CoprodI.lift (fundamentalGroupFactorToAmbient U V x₀ hx₀))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.freeProductToFundamentalGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.freeProductToFundamentalGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.freeProductToFundamentalGroup ``Submission.DifferentialGeometry.Topology.VanKampen.freeProductToFundamentalGroup

theorem fundamentalGroupFreeProductLeft_toFundamentalGroup
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    fundamentalGroupFreeProductLeft U V x₀ hx₀ ≫
        freeProductToFundamentalGroup U V x₀ hx₀ =
      fundamentalGroupLeftToAmbient U x₀ hx₀.1 := by
  apply GrpCat.ext
  intro g
  change Monoid.CoprodI.lift (fundamentalGroupFactorToAmbient U V x₀ hx₀)
      (Monoid.CoprodI.of (M := fundamentalGroupFactor U V x₀ hx₀) (i := _root_.Bool.false) g) =
    (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom g
  rw [Monoid.CoprodI.lift_of]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProductLeft_toFundamentalGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProductLeft_toFundamentalGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProductLeft_toFundamentalGroup ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProductLeft_toFundamentalGroup

theorem fundamentalGroupFreeProductRight_toFundamentalGroup
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    fundamentalGroupFreeProductRight U V x₀ hx₀ ≫
        freeProductToFundamentalGroup U V x₀ hx₀ =
      fundamentalGroupRightToAmbient V x₀ hx₀.2 := by
  apply GrpCat.ext
  intro g
  change Monoid.CoprodI.lift (fundamentalGroupFactorToAmbient U V x₀ hx₀)
      (Monoid.CoprodI.of (M := fundamentalGroupFactor U V x₀ hx₀) (i := _root_.Bool.true) g) =
    (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom g
  rw [Monoid.CoprodI.lift_of]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProductRight_toFundamentalGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProductRight_toFundamentalGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProductRight_toFundamentalGroup ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupFreeProductRight_toFundamentalGroup

noncomputable def fundamentalGroupToFreeProduct
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    GrpCat.of (FundamentalGroup X x₀) ⟶
      GrpCat.of (fundamentalGroupFreeProduct U V x₀ hx₀) :=
  (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀).desc
    (fundamentalGroupFreeProductLeft U V x₀ hx₀)
    (fundamentalGroupFreeProductRight U V x₀ hx₀)
    (fundamentalGroupFreeProduct_coverSquare_commutes U V x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupToFreeProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupToFreeProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupToFreeProduct ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupToFreeProduct

theorem fundamentalGroupLeftToAmbient_toFreeProduct
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupLeftToAmbient U x₀ hx₀.1 ≫
        fundamentalGroupToFreeProduct U V hU hV hcover x₀ hx₀ =
      fundamentalGroupFreeProductLeft U V x₀ hx₀ := by
  apply (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀).inl_desc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbient_toFreeProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbient_toFreeProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbient_toFreeProduct ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbient_toFreeProduct

theorem fundamentalGroupRightToAmbient_toFreeProduct
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupRightToAmbient V x₀ hx₀.2 ≫
        fundamentalGroupToFreeProduct U V hU hV hcover x₀ hx₀ =
      fundamentalGroupFreeProductRight U V x₀ hx₀ := by
  apply (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀).inr_desc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbient_toFreeProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbient_toFreeProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbient_toFreeProduct ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbient_toFreeProduct

theorem freeProductCanonicalMaps_forward_inverse
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupToFreeProduct U V hU hV hcover x₀ hx₀ ≫
        freeProductToFundamentalGroup U V x₀ hx₀ =
      𝟙 (GrpCat.of (FundamentalGroup X x₀)) := by
  apply (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀).hom_ext
  · rw [← Category.assoc, fundamentalGroupLeftToAmbient_toFreeProduct,
      fundamentalGroupFreeProductLeft_toFundamentalGroup, Category.comp_id]
  · rw [← Category.assoc, fundamentalGroupRightToAmbient_toFreeProduct,
      fundamentalGroupFreeProductRight_toFundamentalGroup, Category.comp_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.freeProductCanonicalMaps_forward_inverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.freeProductCanonicalMaps_forward_inverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.freeProductCanonicalMaps_forward_inverse ``Submission.DifferentialGeometry.Topology.VanKampen.freeProductCanonicalMaps_forward_inverse

theorem freeProductCanonicalMaps_inverse_forward
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    freeProductToFundamentalGroup U V x₀ hx₀ ≫
        fundamentalGroupToFreeProduct U V hU hV hcover x₀ hx₀ =
      𝟙 (GrpCat.of (fundamentalGroupFreeProduct U V x₀ hx₀)) := by
  apply GrpCat.hom_ext
  apply Monoid.CoprodI.ext_hom
  intro i
  cases i with
  | false =>
      have hleft : fundamentalGroupFreeProductLeft U V x₀ hx₀ ≫
            (freeProductToFundamentalGroup U V x₀ hx₀ ≫
              fundamentalGroupToFreeProduct U V hU hV hcover x₀ hx₀) =
          fundamentalGroupFreeProductLeft U V x₀ hx₀ ≫ 𝟙 _ := by
        rw [← Category.assoc, fundamentalGroupFreeProductLeft_toFundamentalGroup,
          fundamentalGroupLeftToAmbient_toFreeProduct, Category.comp_id]
      simpa only [fundamentalGroupFreeProductLeft, GrpCat.hom_comp,
        GrpCat.hom_id, GrpCat.hom_ofHom] using congrArg GrpCat.Hom.hom hleft
  | true =>
      have hright : fundamentalGroupFreeProductRight U V x₀ hx₀ ≫
            (freeProductToFundamentalGroup U V x₀ hx₀ ≫
              fundamentalGroupToFreeProduct U V hU hV hcover x₀ hx₀) =
          fundamentalGroupFreeProductRight U V x₀ hx₀ ≫ 𝟙 _ := by
        rw [← Category.assoc, fundamentalGroupFreeProductRight_toFundamentalGroup,
          fundamentalGroupRightToAmbient_toFreeProduct, Category.comp_id]
      simpa only [fundamentalGroupFreeProductRight, GrpCat.hom_comp,
        GrpCat.hom_id, GrpCat.hom_ofHom] using congrArg GrpCat.Hom.hom hright

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.freeProductCanonicalMaps_inverse_forward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.freeProductCanonicalMaps_inverse_forward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.freeProductCanonicalMaps_inverse_forward ``Submission.DifferentialGeometry.Topology.VanKampen.freeProductCanonicalMaps_inverse_forward

noncomputable def fundamentalGroupEquivFreeProduct
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupFreeProduct U V x₀ hx₀ ≃* FundamentalGroup X x₀ :=
  MonoidHom.toMulEquiv
    (freeProductToFundamentalGroup U V x₀ hx₀).hom
    (fundamentalGroupToFreeProduct U V hU hV hcover x₀ hx₀).hom
    (congrArg GrpCat.Hom.hom <|
      freeProductCanonicalMaps_inverse_forward U V hU hV hcover x₀ hx₀)
    (congrArg GrpCat.Hom.hom <|
      freeProductCanonicalMaps_forward_inverse U V hU hV hcover x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProduct ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProduct

theorem fundamentalGroupEquivFreeProduct_comp_left
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    (fundamentalGroupEquivFreeProduct U V hU hV hcover x₀ hx₀).toMonoidHom.comp
        (fundamentalGroupFreeProductLeft U V x₀ hx₀).hom =
      (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom := by
  exact congrArg GrpCat.Hom.hom
    (fundamentalGroupFreeProductLeft_toFundamentalGroup U V x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProduct_comp_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProduct_comp_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProduct_comp_left ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProduct_comp_left

theorem fundamentalGroupEquivFreeProduct_comp_right
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (↑(U ∩ V))] :
    (fundamentalGroupEquivFreeProduct U V hU hV hcover x₀ hx₀).toMonoidHom.comp
        (fundamentalGroupFreeProductRight U V x₀ hx₀).hom =
      (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom := by
  exact congrArg GrpCat.Hom.hom
    (fundamentalGroupFreeProductRight_toFundamentalGroup U V x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProduct_comp_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProduct_comp_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProduct_comp_right ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivFreeProduct_comp_right

end DifferentialGeometry.Topology.VanKampen
