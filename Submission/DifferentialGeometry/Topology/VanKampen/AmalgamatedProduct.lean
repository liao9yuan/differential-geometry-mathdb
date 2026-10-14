/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Submission.DifferentialGeometry.Topology.Algebra.Group.AmalgamatedProduct
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

abbrev fundamentalGroupFactor {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) : Bool → Type u
  | false => FundamentalGroup U (leftBasepoint U x₀ hx₀.1)
  | true => FundamentalGroup V (rightBasepoint V x₀ hx₀.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactor ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactor

noncomputable instance fundamentalGroupFactorGroup {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) (i : Bool) :
    Group (fundamentalGroupFactor U V x₀ hx₀ i) := by
  cases i <;> simp only [fundamentalGroupFactor] <;> infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactorGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactorGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactorGroup ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactorGroup

noncomputable def fundamentalGroupAmalgamation {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    ∀ i, FundamentalGroup (↑(U ∩ V)) (overlapBasepoint U V x₀ hx₀) →*
      fundamentalGroupFactor U V x₀ hx₀ i
  | false => (fundamentalGroupInterToLeft U V x₀ hx₀).hom
  | true => (fundamentalGroupInterToRight U V x₀ hx₀).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamation ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamation

abbrev fundamentalGroupAmalgamatedProduct {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :=
  Monoid.PushoutI (fundamentalGroupAmalgamation U V x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProduct ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProduct

noncomputable def fundamentalGroupAmalgamatedProductLeft {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    GrpCat.of (FundamentalGroup U (leftBasepoint U x₀ hx₀.1)) ⟶
      GrpCat.of (fundamentalGroupAmalgamatedProduct U V x₀ hx₀) :=
  GrpCat.ofHom (Monoid.PushoutI.of
    (φ := fundamentalGroupAmalgamation U V x₀ hx₀) _root_.Bool.false)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProductLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProductLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProductLeft ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProductLeft

noncomputable def fundamentalGroupAmalgamatedProductRight {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    GrpCat.of (FundamentalGroup V (rightBasepoint V x₀ hx₀.2)) ⟶
      GrpCat.of (fundamentalGroupAmalgamatedProduct U V x₀ hx₀) :=
  GrpCat.ofHom (Monoid.PushoutI.of
    (φ := fundamentalGroupAmalgamation U V x₀ hx₀) _root_.Bool.true)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProductRight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProductRight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProductRight ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProductRight

theorem fundamentalGroupAmalgamatedProduct_coverSquare_commutes
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    fundamentalGroupInterToLeft U V x₀ hx₀ ≫
        fundamentalGroupAmalgamatedProductLeft U V x₀ hx₀ =
      fundamentalGroupInterToRight U V x₀ hx₀ ≫
        fundamentalGroupAmalgamatedProductRight U V x₀ hx₀ := by
  apply GrpCat.ext
  intro w
  change Monoid.PushoutI.of _root_.Bool.false (fundamentalGroupAmalgamation U V x₀ hx₀ _root_.Bool.false w) =
    Monoid.PushoutI.of _root_.Bool.true (fundamentalGroupAmalgamation U V x₀ hx₀ _root_.Bool.true w)
  rw [Monoid.PushoutI.of_apply_eq_base, Monoid.PushoutI.of_apply_eq_base]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProduct_coverSquare_commutes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProduct_coverSquare_commutes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProduct_coverSquare_commutes ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProduct_coverSquare_commutes

noncomputable def fundamentalGroupFactorToAmbient {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    ∀ i, fundamentalGroupFactor U V x₀ hx₀ i →* FundamentalGroup X x₀
  | false => (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom
  | true => (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactorToAmbient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactorToAmbient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactorToAmbient ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactorToAmbient

theorem fundamentalGroupFactorToAmbient_compatible {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (i : Bool) :
    (fundamentalGroupFactorToAmbient U V x₀ hx₀ i).comp
        (fundamentalGroupAmalgamation U V x₀ hx₀ i) =
      (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom.comp
        (fundamentalGroupInterToLeft U V x₀ hx₀).hom := by
  cases i with
  | false => rfl
  | true =>
      have h := congrArg GrpCat.Hom.hom
        (fundamentalGroup_coverSquare_commutes U V x₀ hx₀)
      simpa only [fundamentalGroupFactorToAmbient, fundamentalGroupAmalgamation,
        GrpCat.hom_comp] using h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactorToAmbient_compatible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactorToAmbient_compatible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactorToAmbient_compatible ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupFactorToAmbient_compatible

noncomputable def amalgamatedProductToFundamentalGroup {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    GrpCat.of (fundamentalGroupAmalgamatedProduct U V x₀ hx₀) ⟶
      GrpCat.of (FundamentalGroup X x₀) :=
  GrpCat.ofHom <| Monoid.PushoutI.lift
    (fundamentalGroupFactorToAmbient U V x₀ hx₀)
    ((fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom.comp
      (fundamentalGroupInterToLeft U V x₀ hx₀).hom)
    (fundamentalGroupFactorToAmbient_compatible U V x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.amalgamatedProductToFundamentalGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.amalgamatedProductToFundamentalGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.amalgamatedProductToFundamentalGroup ``Submission.DifferentialGeometry.Topology.VanKampen.amalgamatedProductToFundamentalGroup

theorem fundamentalGroupAmalgamatedProductLeft_toFundamentalGroup
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    fundamentalGroupAmalgamatedProductLeft U V x₀ hx₀ ≫
        amalgamatedProductToFundamentalGroup U V x₀ hx₀ =
      fundamentalGroupLeftToAmbient U x₀ hx₀.1 := by
  apply GrpCat.ext
  intro g
  change (Monoid.PushoutI.lift
      (fundamentalGroupFactorToAmbient U V x₀ hx₀)
      ((fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom.comp
        (fundamentalGroupInterToLeft U V x₀ hx₀).hom)
      (fundamentalGroupFactorToAmbient_compatible U V x₀ hx₀))
      (Monoid.PushoutI.of
        (φ := fundamentalGroupAmalgamation U V x₀ hx₀) _root_.Bool.false g) =
    (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom g
  rw [Monoid.PushoutI.lift_of]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProductLeft_toFundamentalGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProductLeft_toFundamentalGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProductLeft_toFundamentalGroup ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProductLeft_toFundamentalGroup

theorem fundamentalGroupAmalgamatedProductRight_toFundamentalGroup
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    fundamentalGroupAmalgamatedProductRight U V x₀ hx₀ ≫
        amalgamatedProductToFundamentalGroup U V x₀ hx₀ =
      fundamentalGroupRightToAmbient V x₀ hx₀.2 := by
  apply GrpCat.ext
  intro g
  change (Monoid.PushoutI.lift
      (fundamentalGroupFactorToAmbient U V x₀ hx₀)
      ((fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom.comp
        (fundamentalGroupInterToLeft U V x₀ hx₀).hom)
      (fundamentalGroupFactorToAmbient_compatible U V x₀ hx₀))
      (Monoid.PushoutI.of
        (φ := fundamentalGroupAmalgamation U V x₀ hx₀) _root_.Bool.true g) =
    (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom g
  rw [Monoid.PushoutI.lift_of]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProductRight_toFundamentalGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProductRight_toFundamentalGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProductRight_toFundamentalGroup ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupAmalgamatedProductRight_toFundamentalGroup

noncomputable def fundamentalGroupToAmalgamatedProduct
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))] :
    GrpCat.of (FundamentalGroup X x₀) ⟶
      GrpCat.of (fundamentalGroupAmalgamatedProduct U V x₀ hx₀) :=
  (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀).desc
    (fundamentalGroupAmalgamatedProductLeft U V x₀ hx₀)
    (fundamentalGroupAmalgamatedProductRight U V x₀ hx₀)
    (fundamentalGroupAmalgamatedProduct_coverSquare_commutes U V x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupToAmalgamatedProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupToAmalgamatedProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupToAmalgamatedProduct ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupToAmalgamatedProduct

theorem fundamentalGroupLeftToAmbient_toAmalgamatedProduct
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupLeftToAmbient U x₀ hx₀.1 ≫
        fundamentalGroupToAmalgamatedProduct U V hU hV hcover x₀ hx₀ =
      fundamentalGroupAmalgamatedProductLeft U V x₀ hx₀ := by
  apply (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀).inl_desc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbient_toAmalgamatedProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbient_toAmalgamatedProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbient_toAmalgamatedProduct ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbient_toAmalgamatedProduct

theorem fundamentalGroupRightToAmbient_toAmalgamatedProduct
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupRightToAmbient V x₀ hx₀.2 ≫
        fundamentalGroupToAmalgamatedProduct U V hU hV hcover x₀ hx₀ =
      fundamentalGroupAmalgamatedProductRight U V x₀ hx₀ := by
  apply (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀).inr_desc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbient_toAmalgamatedProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbient_toAmalgamatedProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbient_toAmalgamatedProduct ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbient_toAmalgamatedProduct

theorem canonicalMaps_forward_inverse
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupToAmalgamatedProduct U V hU hV hcover x₀ hx₀ ≫
        amalgamatedProductToFundamentalGroup U V x₀ hx₀ =
      𝟙 (GrpCat.of (FundamentalGroup X x₀)) := by
  apply (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀).hom_ext
  · rw [← Category.assoc, fundamentalGroupLeftToAmbient_toAmalgamatedProduct,
      fundamentalGroupAmalgamatedProductLeft_toFundamentalGroup, Category.comp_id]
  · rw [← Category.assoc, fundamentalGroupRightToAmbient_toAmalgamatedProduct,
      fundamentalGroupAmalgamatedProductRight_toFundamentalGroup, Category.comp_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.canonicalMaps_forward_inverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.canonicalMaps_forward_inverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.canonicalMaps_forward_inverse ``Submission.DifferentialGeometry.Topology.VanKampen.canonicalMaps_forward_inverse

theorem canonicalMaps_inverse_forward
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))] :
    amalgamatedProductToFundamentalGroup U V x₀ hx₀ ≫
        fundamentalGroupToAmalgamatedProduct U V hU hV hcover x₀ hx₀ =
      𝟙 (GrpCat.of (fundamentalGroupAmalgamatedProduct U V x₀ hx₀)) := by
  apply GrpCat.hom_ext
  apply Monoid.PushoutI.hom_ext_nonempty
  intro i
  cases i with
  | false =>
      have hleft : fundamentalGroupAmalgamatedProductLeft U V x₀ hx₀ ≫
            (amalgamatedProductToFundamentalGroup U V x₀ hx₀ ≫
              fundamentalGroupToAmalgamatedProduct U V hU hV hcover x₀ hx₀) =
          fundamentalGroupAmalgamatedProductLeft U V x₀ hx₀ ≫ 𝟙 _ := by
        rw [← Category.assoc, fundamentalGroupAmalgamatedProductLeft_toFundamentalGroup,
          fundamentalGroupLeftToAmbient_toAmalgamatedProduct, Category.comp_id]
      simpa only [fundamentalGroupAmalgamatedProductLeft, GrpCat.hom_comp,
        GrpCat.hom_id, GrpCat.hom_ofHom] using congrArg GrpCat.Hom.hom hleft
  | true =>
      have hright : fundamentalGroupAmalgamatedProductRight U V x₀ hx₀ ≫
            (amalgamatedProductToFundamentalGroup U V x₀ hx₀ ≫
              fundamentalGroupToAmalgamatedProduct U V hU hV hcover x₀ hx₀) =
          fundamentalGroupAmalgamatedProductRight U V x₀ hx₀ ≫ 𝟙 _ := by
        rw [← Category.assoc, fundamentalGroupAmalgamatedProductRight_toFundamentalGroup,
          fundamentalGroupRightToAmbient_toAmalgamatedProduct, Category.comp_id]
      simpa only [fundamentalGroupAmalgamatedProductRight, GrpCat.hom_comp,
        GrpCat.hom_id, GrpCat.hom_ofHom] using congrArg GrpCat.Hom.hom hright

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.canonicalMaps_inverse_forward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.canonicalMaps_inverse_forward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.canonicalMaps_inverse_forward ``Submission.DifferentialGeometry.Topology.VanKampen.canonicalMaps_inverse_forward

noncomputable def fundamentalGroupEquivAmalgamatedProduct
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupAmalgamatedProduct U V x₀ hx₀ ≃* FundamentalGroup X x₀ :=
  MonoidHom.toMulEquiv
    (amalgamatedProductToFundamentalGroup U V x₀ hx₀).hom
    (fundamentalGroupToAmalgamatedProduct U V hU hV hcover x₀ hx₀).hom
    (congrArg GrpCat.Hom.hom <|
      canonicalMaps_inverse_forward U V hU hV hcover x₀ hx₀)
    (congrArg GrpCat.Hom.hom <|
      canonicalMaps_forward_inverse U V hU hV hcover x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivAmalgamatedProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivAmalgamatedProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivAmalgamatedProduct ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivAmalgamatedProduct

theorem fundamentalGroupEquivAmalgamatedProduct_comp_left
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))] :
    (fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x₀ hx₀).toMonoidHom.comp
        (fundamentalGroupAmalgamatedProductLeft U V x₀ hx₀).hom =
      (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom := by
  exact congrArg GrpCat.Hom.hom
    (fundamentalGroupAmalgamatedProductLeft_toFundamentalGroup U V x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivAmalgamatedProduct_comp_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivAmalgamatedProduct_comp_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivAmalgamatedProduct_comp_left ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivAmalgamatedProduct_comp_left

theorem fundamentalGroupEquivAmalgamatedProduct_comp_right
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))] :
    (fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x₀ hx₀).toMonoidHom.comp
        (fundamentalGroupAmalgamatedProductRight U V x₀ hx₀).hom =
      (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom := by
  exact congrArg GrpCat.Hom.hom
    (fundamentalGroupAmalgamatedProductRight_toFundamentalGroup U V x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivAmalgamatedProduct_comp_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivAmalgamatedProduct_comp_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivAmalgamatedProduct_comp_right ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupEquivAmalgamatedProduct_comp_right

end DifferentialGeometry.Topology.VanKampen
