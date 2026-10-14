/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Submission.DifferentialGeometry.Topology.VanKampen.ConnectedSumNeck
import Submission.DifferentialGeometry.Topology.VanKampen.HomotopyEquivalentFreeProductCover

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set _root_.Topology
open scoped _root_.ContinuousMap _root_.unitInterval

universe u

namespace DifferentialGeometry.Topology.ThreeManifold

open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Topology.CellAttachment

noncomputable def connectedSumNeckBoundaryBasepoint : CellBoundary 3 :=
  cellBoundaryThreeHomeomorphSphereTwo.symm DifferentialGeometry.Topology.sphereTwoNorth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckBoundaryBasepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckBoundaryBasepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckBoundaryBasepoint ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckBoundaryBasepoint




abbrev ConnectedSumNeckLeftPrequotient
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :=
  (adjunctionMk connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)) ⁻¹'
    connectedSumNeckLeft leftBoundary rightBoundary glue

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumNeckLeftPrequotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.ConnectedSumNeckLeftPrequotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.ConnectedSumNeckLeftPrequotient ``Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSumNeckLeftPrequotient


def connectedSumNeckLeftQuotientMap
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    ConnectedSumNeckLeftPrequotient leftBoundary rightBoundary glue →
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue) :=
  (connectedSumNeckLeft leftBoundary rightBoundary glue).restrictPreimage
    (adjunctionMk connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftQuotientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftQuotientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftQuotientMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftQuotientMap


theorem isQuotientMap_connectedSumNeckLeftQuotientMap
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    _root_.Topology.IsQuotientMap
      (connectedSumNeckLeftQuotientMap leftBoundary rightBoundary glue) :=
  (isQuotientMap_adjunctionMk connectedSumNeckBoundaryInclusion
    (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)).restrictPreimage_isOpen
      (isOpen_connectedSumNeckLeft leftBoundary rightBoundary glue)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.isQuotientMap_connectedSumNeckLeftQuotientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.isQuotientMap_connectedSumNeckLeftQuotientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.isQuotientMap_connectedSumNeckLeftQuotientMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.isQuotientMap_connectedSumNeckLeftQuotientMap


noncomputable def connectedSumNeckLeftQuotientContinuousMap
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    C(ConnectedSumNeckLeftPrequotient leftBoundary rightBoundary glue,
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue)) :=
  ⟨connectedSumNeckLeftQuotientMap leftBoundary rightBoundary glue,
    (isQuotientMap_connectedSumNeckLeftQuotientMap
      leftBoundary rightBoundary glue).continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftQuotientContinuousMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftQuotientContinuousMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftQuotientContinuousMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftQuotientContinuousMap

theorem isQuotientMap_connectedSumNeckLeftQuotientContinuousMap
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    _root_.Topology.IsQuotientMap ⇑(connectedSumNeckLeftQuotientContinuousMap
      leftBoundary rightBoundary glue) :=
  isQuotientMap_connectedSumNeckLeftQuotientMap leftBoundary rightBoundary glue

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.isQuotientMap_connectedSumNeckLeftQuotientContinuousMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.isQuotientMap_connectedSumNeckLeftQuotientContinuousMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.isQuotientMap_connectedSumNeckLeftQuotientContinuousMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.isQuotientMap_connectedSumNeckLeftQuotientContinuousMap

noncomputable def connectedSumNeckLeftRawRetractionTotal
    {K L : Type u} (leftBoundary : CellBoundary 3 → K) :
    ConnectedSumNeckCylinder ⊕ (K ⊕ L) → K
  | Sum.inl p => leftBoundary p.1
  | Sum.inr (Sum.inl k) => k
  | Sum.inr (Sum.inr _) => leftBoundary connectedSumNeckBoundaryBasepoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetractionTotal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetractionTotal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetractionTotal ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetractionTotal

theorem continuous_connectedSumNeckLeftRawRetractionTotal
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    {leftBoundary : CellBoundary 3 → K} (hleft : Continuous leftBoundary) :
    Continuous (@connectedSumNeckLeftRawRetractionTotal K L leftBoundary) := by
  have h : Continuous (Sum.elim
      (fun p : ConnectedSumNeckCylinder ↦ leftBoundary p.1)
      (Sum.elim id
        (fun _ : L ↦ leftBoundary connectedSumNeckBoundaryBasepoint))) := by
    apply Continuous.sumElim
    · exact hleft.comp continuous_fst
    · apply Continuous.sumElim
      · exact continuous_id
      · exact continuous_const
  convert h using 1
  funext z
  rcases z with p | (k | l) <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftRawRetractionTotal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftRawRetractionTotal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftRawRetractionTotal ``Submission.DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftRawRetractionTotal


noncomputable def connectedSumNeckLeftRawRetraction
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    ConnectedSumNeckLeftPrequotient leftBoundary rightBoundary glue → K :=
  connectedSumNeckLeftRawRetractionTotal leftBoundary ∘ Subtype.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetraction ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetraction

theorem continuous_connectedSumNeckLeftRawRetraction
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    {leftBoundary : CellBoundary 3 → K} (hleft : Continuous leftBoundary)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    Continuous (connectedSumNeckLeftRawRetraction
      leftBoundary rightBoundary glue) :=
  (continuous_connectedSumNeckLeftRawRetractionTotal hleft).comp continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftRawRetraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftRawRetraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftRawRetraction ``Submission.DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftRawRetraction


noncomputable def connectedSumNeckLeftRawRetractionContinuousMap
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (hleft : Continuous leftBoundary)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    C(ConnectedSumNeckLeftPrequotient leftBoundary rightBoundary glue, K) :=
  ⟨connectedSumNeckLeftRawRetraction leftBoundary rightBoundary glue,
    continuous_connectedSumNeckLeftRawRetraction hleft rightBoundary glue⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetractionContinuousMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetractionContinuousMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetractionContinuousMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetractionContinuousMap


noncomputable def connectedSumNeckLeftRetractionCodeRaw
    {K L : Type u} (leftBoundary : CellBoundary 3 → K) :
    ConnectedSumNeckCylinder ⊕ (K ⊕ L) → Option K
  | Sum.inl p =>
      if (p.2 : ℝ) < 2 / 3 then _root_.Option.some (leftBoundary p.1) else _root_.Option.none
  | Sum.inr (Sum.inl k) => _root_.Option.some k
  | Sum.inr (Sum.inr _) => _root_.Option.none

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetractionCodeRaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetractionCodeRaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetractionCodeRaw ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetractionCodeRaw

theorem connectedSumNeckLeftRetractionCodeRaw_eq_of_rel
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (a b : ConnectedSumNeckCylinder ⊕ (K ⊕ L))
    (hab : adjunctionRel connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) a b) :
    connectedSumNeckLeftRetractionCodeRaw leftBoundary a =
      connectedSumNeckLeftRetractionCodeRaw leftBoundary b := by
  rcases hab with ⟨s, hs | hs⟩
  · rcases hs with ⟨rfl, rfl⟩
    cases s with
    | inl x =>
      norm_num [connectedSumNeckLeftRetractionCodeRaw,
        connectedSumNeckBoundaryInclusion, connectedSumNeckAttachingMap]
    | inr x =>
      norm_num [connectedSumNeckLeftRetractionCodeRaw,
        connectedSumNeckBoundaryInclusion, connectedSumNeckAttachingMap]
  · rcases hs with ⟨rfl, rfl⟩
    cases s with
    | inl x =>
      norm_num [connectedSumNeckLeftRetractionCodeRaw,
        connectedSumNeckBoundaryInclusion, connectedSumNeckAttachingMap]
    | inr x =>
      norm_num [connectedSumNeckLeftRetractionCodeRaw,
        connectedSumNeckBoundaryInclusion, connectedSumNeckAttachingMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetractionCodeRaw_eq_of_rel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetractionCodeRaw_eq_of_rel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetractionCodeRaw_eq_of_rel ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetractionCodeRaw_eq_of_rel


noncomputable def connectedSumNeckLeftRetractionCode
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    ConnectedSumNeck leftBoundary rightBoundary glue → Option K :=
  Quot.lift (connectedSumNeckLeftRetractionCodeRaw leftBoundary)
    (connectedSumNeckLeftRetractionCodeRaw_eq_of_rel
      leftBoundary rightBoundary glue)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetractionCode then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetractionCode"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetractionCode ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetractionCode

@[simp]
theorem connectedSumNeckLeftRetractionCode_quotientMap
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (z : ConnectedSumNeckLeftPrequotient leftBoundary rightBoundary glue) :
    connectedSumNeckLeftRetractionCode leftBoundary rightBoundary glue
        (connectedSumNeckLeftQuotientMap leftBoundary rightBoundary glue z) =
      some (connectedSumNeckLeftRawRetraction leftBoundary rightBoundary glue z) := by
  rcases z with ⟨z, hz⟩
  change connectedSumNeckLeftRaw z at hz
  rcases z with p | (k | l)
  · change (p.2 : ℝ) < 2 / 3 at hz
    change (if (p.2 : ℝ) < 2 / 3 then _root_.Option.some (leftBoundary p.1) else _root_.Option.none) =
      _root_.Option.some (leftBoundary p.1)
    rw [if_pos hz]
  · rfl
  · exact False.elim hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetractionCode_quotientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetractionCode_quotientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetractionCode_quotientMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetractionCode_quotientMap


theorem connectedSumNeckLeftRawRetraction_factorsThrough
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (hleft : Continuous leftBoundary)
    (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    Function.FactorsThrough
      ⇑(connectedSumNeckLeftRawRetractionContinuousMap
        leftBoundary hleft rightBoundary glue)
      ⇑(connectedSumNeckLeftQuotientContinuousMap
        leftBoundary rightBoundary glue) := by
  intro x y hxy
  apply Option.some.inj
  change _root_.Option.some (connectedSumNeckLeftRawRetraction leftBoundary rightBoundary glue x) =
    _root_.Option.some (connectedSumNeckLeftRawRetraction leftBoundary rightBoundary glue y)
  rw [← connectedSumNeckLeftRetractionCode_quotientMap,
    ← connectedSumNeckLeftRetractionCode_quotientMap]
  exact congrArg (connectedSumNeckLeftRetractionCode leftBoundary rightBoundary glue)
    (congrArg Subtype.val hxy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetraction_factorsThrough then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetraction_factorsThrough"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetraction_factorsThrough ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetraction_factorsThrough


noncomputable def connectedSumNeckLeftRetraction
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (hleft : Continuous leftBoundary)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    C(↑(connectedSumNeckLeft leftBoundary rightBoundary glue), K) :=
  (isQuotientMap_connectedSumNeckLeftQuotientContinuousMap
      leftBoundary rightBoundary glue).lift
    (connectedSumNeckLeftRawRetractionContinuousMap
      leftBoundary hleft rightBoundary glue)
    (connectedSumNeckLeftRawRetraction_factorsThrough
      leftBoundary hleft rightBoundary glue)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetraction ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetraction


def connectedSumNeckLeftCoverInclusion
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    C(K, ↑(connectedSumNeckLeft leftBoundary rightBoundary glue)) where
  toFun k := ⟨connectedSumNeckLeftInclusion leftBoundary rightBoundary glue k, trivial⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_connectedSumNeckLeftInclusion leftBoundary rightBoundary glue) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftCoverInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftCoverInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftCoverInclusion ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftCoverInclusion

@[simp]
theorem connectedSumNeckLeftRetraction_inclusion
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (hleft : Continuous leftBoundary)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (k : K) :
    connectedSumNeckLeftRetraction leftBoundary hleft rightBoundary glue
        (connectedSumNeckLeftCoverInclusion leftBoundary rightBoundary glue k) = k := by
  let z : ConnectedSumNeckLeftPrequotient leftBoundary rightBoundary glue :=
    ⟨Sum.inr (Sum.inl k), trivial⟩
  have hcomp := ContinuousMap.congr_fun
    ((isQuotientMap_connectedSumNeckLeftQuotientContinuousMap
      leftBoundary rightBoundary glue).lift_comp
        (connectedSumNeckLeftRawRetractionContinuousMap
          leftBoundary hleft rightBoundary glue)
        (connectedSumNeckLeftRawRetraction_factorsThrough
          leftBoundary hleft rightBoundary glue)) z
  exact hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetraction_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetraction_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetraction_inclusion ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRetraction_inclusion


noncomputable def connectedSumNeckLeftPushCylinder
    (s : I) (p : ConnectedSumNeckCylinder) : ConnectedSumNeckCylinder :=
  ⟨p.1, ⟨(1 - (s : ℝ)) * (p.2 : ℝ), by
    constructor <;> nlinarith [s.2.1, s.2.2, p.2.2.1, p.2.2.2]⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder

theorem continuous_connectedSumNeckLeftPushCylinder :
    Continuous (fun p : I × ConnectedSumNeckCylinder ↦
      connectedSumNeckLeftPushCylinder p.1 p.2) := by
  apply continuous_fst.comp continuous_snd |>.prodMk
  apply Continuous.subtype_mk
  exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    ((continuous_subtype_val.comp continuous_snd).comp continuous_snd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftPushCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftPushCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftPushCylinder ``Submission.DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftPushCylinder

@[simp]
theorem connectedSumNeckLeftPushCylinder_zero (p : ConnectedSumNeckCylinder) :
    connectedSumNeckLeftPushCylinder 0 p = p := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp [connectedSumNeckLeftPushCylinder]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder_zero ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder_zero

@[simp]
theorem connectedSumNeckLeftPushCylinder_one (p : ConnectedSumNeckCylinder) :
    connectedSumNeckLeftPushCylinder 1 p = (p.1, 0) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp [connectedSumNeckLeftPushCylinder]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder_one ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder_one

@[simp]
theorem connectedSumNeckLeftPushCylinder_leftEndpoint
    (s : I) (b : CellBoundary 3) :
    connectedSumNeckLeftPushCylinder s (b, 0) = (b, 0) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp [connectedSumNeckLeftPushCylinder]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder_leftEndpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder_leftEndpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder_leftEndpoint ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder_leftEndpoint

theorem connectedSumNeckLeftPushCylinder_mem
    (s : I) (p : ConnectedSumNeckCylinder) (hp : (p.2 : ℝ) < 2 / 3) :
    ((connectedSumNeckLeftPushCylinder s p).2 : ℝ) < 2 / 3 := by
  change (1 - (s : ℝ)) * (p.2 : ℝ) < 2 / 3
  nlinarith [s.2.1, s.2.2, p.2.2.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder_mem ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCylinder_mem


noncomputable def connectedSumNeckLeftPushRawTotal
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    I × (ConnectedSumNeckCylinder ⊕ (K ⊕ L)) →
      ConnectedSumNeck leftBoundary rightBoundary glue
  | (s, Sum.inl p) =>
      adjunctionCell connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
        (connectedSumNeckLeftPushCylinder s p)
  | (_, Sum.inr (Sum.inl k)) =>
      connectedSumNeckLeftInclusion leftBoundary rightBoundary glue k
  | (_, Sum.inr (Sum.inr _)) =>
      connectedSumNeckLeftInclusion leftBoundary rightBoundary glue
        (leftBoundary connectedSumNeckBoundaryBasepoint)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRawTotal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRawTotal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRawTotal ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRawTotal

theorem continuous_connectedSumNeckLeftPushRawTotal
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    Continuous (connectedSumNeckLeftPushRawTotal
      leftBoundary rightBoundary glue) := by
  have hright : Continuous (Sum.elim
      (connectedSumNeckLeftInclusion leftBoundary rightBoundary glue)
      (fun _ : L ↦ connectedSumNeckLeftInclusion leftBoundary rightBoundary glue
        (leftBoundary connectedSumNeckBoundaryBasepoint))) := by
    apply Continuous.sumElim
    · exact continuous_connectedSumNeckLeftInclusion
        leftBoundary rightBoundary glue
    · exact continuous_const
  have hsum : Continuous (Sum.elim
      (fun p : I × ConnectedSumNeckCylinder ↦
        adjunctionCell connectedSumNeckBoundaryInclusion
          (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
          (connectedSumNeckLeftPushCylinder p.1 p.2))
      (fun p : I × (K ⊕ L) ↦ Sum.elim
        (connectedSumNeckLeftInclusion leftBoundary rightBoundary glue)
        (fun _ : L ↦ connectedSumNeckLeftInclusion leftBoundary rightBoundary glue
          (leftBoundary connectedSumNeckBoundaryBasepoint)) p.2)) := by
    apply Continuous.sumElim
    · exact (continuous_adjunctionCell connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)).comp
          continuous_connectedSumNeckLeftPushCylinder
    · exact hright.comp continuous_snd
  let e : I × (ConnectedSumNeckCylinder ⊕ (K ⊕ L)) ≃ₜ
      (I × ConnectedSumNeckCylinder) ⊕ (I × (K ⊕ L)) :=
    Homeomorph.prodSumDistrib
  have hcomp := hsum.comp e.continuous
  convert hcomp using 1
  funext p
  rcases p with ⟨s, p | (k | l)⟩ <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftPushRawTotal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftPushRawTotal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftPushRawTotal ``Submission.DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftPushRawTotal


noncomputable def connectedSumNeckLeftPushRaw
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    I × ConnectedSumNeckLeftPrequotient leftBoundary rightBoundary glue →
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue) :=
  fun p ↦ ⟨connectedSumNeckLeftPushRawTotal leftBoundary rightBoundary glue
      (p.1, p.2.1), by
    rcases p with ⟨s, ⟨z, hz⟩⟩
    change connectedSumNeckLeftRaw z at hz
    rcases z with q | (k | l)
    · exact connectedSumNeckLeftPushCylinder_mem s q hz
    · exact trivial
    · exact False.elim hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRaw ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRaw

theorem continuous_connectedSumNeckLeftPushRaw
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    Continuous (connectedSumNeckLeftPushRaw leftBoundary rightBoundary glue) := by
  apply Continuous.subtype_mk
  exact (continuous_connectedSumNeckLeftPushRawTotal
    leftBoundary rightBoundary glue).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftPushRaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftPushRaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftPushRaw ``Submission.DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftPushRaw

noncomputable def connectedSumNeckLeftPushCodeRaw
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (s : I) :
    ConnectedSumNeckCylinder ⊕ (K ⊕ L) →
      Option ↑(connectedSumNeckLeft leftBoundary rightBoundary glue)
  | Sum.inl p =>
      if hp : (p.2 : ℝ) < 2 / 3 then
        _root_.Option.some ⟨adjunctionCell connectedSumNeckBoundaryInclusion
          (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
          (connectedSumNeckLeftPushCylinder s p),
          connectedSumNeckLeftPushCylinder_mem s p hp⟩
      else _root_.Option.none
  | Sum.inr (Sum.inl k) =>
      _root_.Option.some ⟨connectedSumNeckLeftInclusion leftBoundary rightBoundary glue k, trivial⟩
  | Sum.inr (Sum.inr _) => _root_.Option.none

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCodeRaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCodeRaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCodeRaw ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCodeRaw

theorem connectedSumNeckLeftPushCodeRaw_eq_of_rel
    {K L : Type u}
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (s : I)
    (a b : ConnectedSumNeckCylinder ⊕ (K ⊕ L))
    (hab : adjunctionRel connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) a b) :
    connectedSumNeckLeftPushCodeRaw leftBoundary rightBoundary glue s a =
      connectedSumNeckLeftPushCodeRaw leftBoundary rightBoundary glue s b := by
  rcases hab with ⟨q, hq | hq⟩
  · rcases hq with ⟨rfl, rfl⟩
    cases q with
    | inl b =>
      simp only [connectedSumNeckLeftPushCodeRaw.eq_def]
      split
      · change _root_.Option.some _ = _root_.Option.some _
        congr 2
        change adjunctionCell connectedSumNeckBoundaryInclusion
            (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
              (connectedSumNeckLeftPushCylinder s (b, 0)) = _
        rw [connectedSumNeckLeftPushCylinder_leftEndpoint]
        exact adjunction_coherence connectedSumNeckBoundaryInclusion
          (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) (Sum.inl b)
      · rename_i h
        norm_num [connectedSumNeckBoundaryInclusion] at h
    | inr b =>
      simp only [connectedSumNeckLeftPushCodeRaw.eq_def]
      split
      · rename_i h
        norm_num [connectedSumNeckBoundaryInclusion] at h
      · simp only [connectedSumNeckAttachingMap]
  · rcases hq with ⟨rfl, rfl⟩
    symm
    cases q with
    | inl b =>
      simp only [connectedSumNeckLeftPushCodeRaw.eq_def]
      split
      · change _root_.Option.some _ = _root_.Option.some _
        congr 2
        change adjunctionCell connectedSumNeckBoundaryInclusion
            (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
              (connectedSumNeckLeftPushCylinder s (b, 0)) = _
        rw [connectedSumNeckLeftPushCylinder_leftEndpoint]
        exact adjunction_coherence connectedSumNeckBoundaryInclusion
          (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) (Sum.inl b)
      · rename_i h
        norm_num [connectedSumNeckBoundaryInclusion] at h
    | inr b =>
      simp only [connectedSumNeckLeftPushCodeRaw.eq_def]
      split
      · rename_i h
        norm_num [connectedSumNeckBoundaryInclusion] at h
      · simp only [connectedSumNeckAttachingMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCodeRaw_eq_of_rel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCodeRaw_eq_of_rel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCodeRaw_eq_of_rel ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCodeRaw_eq_of_rel


noncomputable def connectedSumNeckLeftPushCode
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (s : I) :
    ConnectedSumNeck leftBoundary rightBoundary glue →
      Option ↑(connectedSumNeckLeft leftBoundary rightBoundary glue) :=
  Quot.lift (connectedSumNeckLeftPushCodeRaw leftBoundary rightBoundary glue s)
    (connectedSumNeckLeftPushCodeRaw_eq_of_rel
      leftBoundary rightBoundary glue s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCode then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCode"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCode ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCode

@[simp]
theorem connectedSumNeckLeftPushCode_quotientMap
    {K L : Type u} (leftBoundary : CellBoundary 3 → K)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (s : I) (z : ConnectedSumNeckLeftPrequotient leftBoundary rightBoundary glue) :
    connectedSumNeckLeftPushCode leftBoundary rightBoundary glue s
        (connectedSumNeckLeftQuotientMap leftBoundary rightBoundary glue z) =
      some (connectedSumNeckLeftPushRaw leftBoundary rightBoundary glue (s, z)) := by
  rcases z with ⟨z, hz⟩
  change connectedSumNeckLeftRaw z at hz
  rcases z with p | (k | l)
  · change (if hp : (p.2 : ℝ) < 2 / 3 then
        _root_.Option.some (⟨adjunctionCell connectedSumNeckBoundaryInclusion
          (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
          (connectedSumNeckLeftPushCylinder s p),
          connectedSumNeckLeftPushCylinder_mem s p hp⟩ :
            ↑(connectedSumNeckLeft leftBoundary rightBoundary glue))
      else _root_.Option.none) =
        _root_.Option.some (⟨adjunctionCell connectedSumNeckBoundaryInclusion
          (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
          (connectedSumNeckLeftPushCylinder s p),
          connectedSumNeckLeftPushCylinder_mem s p hz⟩ :
            ↑(connectedSumNeckLeft leftBoundary rightBoundary glue))
    split
    · rfl
    · contradiction
  · rfl
  · exact False.elim hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCode_quotientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCode_quotientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCode_quotientMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushCode_quotientMap


theorem connectedSumNeckLeftPushRaw_factorsThrough
    {K L : Type u}
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (s : I) :
    Function.FactorsThrough
      (fun z ↦ connectedSumNeckLeftPushRaw leftBoundary rightBoundary glue (s, z))
      (connectedSumNeckLeftQuotientMap leftBoundary rightBoundary glue) := by
  intro x y hxy
  apply Option.some.inj
  change _root_.Option.some (connectedSumNeckLeftPushRaw leftBoundary rightBoundary glue (s, x)) =
    _root_.Option.some (connectedSumNeckLeftPushRaw leftBoundary rightBoundary glue (s, y))
  rw [← connectedSumNeckLeftPushCode_quotientMap,
    ← connectedSumNeckLeftPushCode_quotientMap]
  exact congrArg (connectedSumNeckLeftPushCode leftBoundary rightBoundary glue s)
    (congrArg Subtype.val hxy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRaw_factorsThrough then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRaw_factorsThrough"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRaw_factorsThrough ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRaw_factorsThrough


noncomputable def connectedSumNeckLeftPushRawContinuousMap
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (s : I) :
    C(ConnectedSumNeckLeftPrequotient leftBoundary rightBoundary glue,
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue)) :=
  ⟨fun z ↦ connectedSumNeckLeftPushRaw leftBoundary rightBoundary glue (s, z),
    (continuous_connectedSumNeckLeftPushRaw leftBoundary rightBoundary glue).comp
      (continuous_const.prodMk continuous_id)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRawContinuousMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRawContinuousMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRawContinuousMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRawContinuousMap


theorem connectedSumNeckLeftPushRawContinuousMap_factorsThrough
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (s : I) :
    Function.FactorsThrough
      ⇑(connectedSumNeckLeftPushRawContinuousMap
        leftBoundary rightBoundary glue s)
      ⇑(connectedSumNeckLeftQuotientContinuousMap
        leftBoundary rightBoundary glue) :=
  connectedSumNeckLeftPushRaw_factorsThrough leftBoundary rightBoundary glue s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRawContinuousMap_factorsThrough then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRawContinuousMap_factorsThrough"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRawContinuousMap_factorsThrough ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRawContinuousMap_factorsThrough


noncomputable def connectedSumNeckLeftPushAt
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (s : I) :
    C(↑(connectedSumNeckLeft leftBoundary rightBoundary glue),
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue)) :=
  (isQuotientMap_connectedSumNeckLeftQuotientContinuousMap
      leftBoundary rightBoundary glue).lift
    (connectedSumNeckLeftPushRawContinuousMap
      leftBoundary rightBoundary glue s)
    (connectedSumNeckLeftPushRawContinuousMap_factorsThrough
      leftBoundary rightBoundary glue s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushAt ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushAt

@[simp]
theorem connectedSumNeckLeftPushAt_quotientMap
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (s : I)
    (z : ConnectedSumNeckLeftPrequotient leftBoundary rightBoundary glue) :
    connectedSumNeckLeftPushAt leftBoundary rightBoundary glue s
        (connectedSumNeckLeftQuotientMap leftBoundary rightBoundary glue z) =
      connectedSumNeckLeftPushRaw leftBoundary rightBoundary glue (s, z) :=
  ContinuousMap.congr_fun
    ((isQuotientMap_connectedSumNeckLeftQuotientContinuousMap
      leftBoundary rightBoundary glue).lift_comp
        (connectedSumNeckLeftPushRawContinuousMap
          leftBoundary rightBoundary glue s)
        (connectedSumNeckLeftPushRawContinuousMap_factorsThrough
          leftBoundary rightBoundary glue s)) z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushAt_quotientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushAt_quotientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushAt_quotientMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushAt_quotientMap


noncomputable def connectedSumNeckLeftPush
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    I × ↑(connectedSumNeckLeft leftBoundary rightBoundary glue) →
      ↑(connectedSumNeckLeft leftBoundary rightBoundary glue) :=
  fun p ↦ connectedSumNeckLeftPushAt
    leftBoundary rightBoundary glue p.1 p.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPush then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPush"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPush ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPush

theorem continuous_connectedSumNeckLeftPush
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    Continuous (connectedSumNeckLeftPush leftBoundary rightBoundary glue) := by
  apply (isQuotientMap_connectedSumNeckLeftQuotientMap
    leftBoundary rightBoundary glue).continuous_lift_prod_right
  have heq : (fun p : I ×
      ConnectedSumNeckLeftPrequotient leftBoundary rightBoundary glue ↦
        connectedSumNeckLeftPush leftBoundary rightBoundary glue
          (p.1, connectedSumNeckLeftQuotientMap
            leftBoundary rightBoundary glue p.2)) =
      connectedSumNeckLeftPushRaw leftBoundary rightBoundary glue := by
    funext p
    exact connectedSumNeckLeftPushAt_quotientMap
      leftBoundary rightBoundary glue p.1 p.2
  rw [heq]
  exact continuous_connectedSumNeckLeftPushRaw
    leftBoundary rightBoundary glue

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftPush then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftPush"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftPush ``Submission.DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckLeftPush

@[simp]
theorem connectedSumNeckLeftRawRetraction_quotientMap
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (hleft : Continuous leftBoundary)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (z : ConnectedSumNeckLeftPrequotient leftBoundary rightBoundary glue) :
    connectedSumNeckLeftRetraction leftBoundary hleft rightBoundary glue
        (connectedSumNeckLeftQuotientMap leftBoundary rightBoundary glue z) =
      connectedSumNeckLeftRawRetraction leftBoundary rightBoundary glue z :=
  ContinuousMap.congr_fun
    ((isQuotientMap_connectedSumNeckLeftQuotientContinuousMap
      leftBoundary rightBoundary glue).lift_comp
        (connectedSumNeckLeftRawRetractionContinuousMap
          leftBoundary hleft rightBoundary glue)
        (connectedSumNeckLeftRawRetraction_factorsThrough
          leftBoundary hleft rightBoundary glue)) z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetraction_quotientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetraction_quotientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetraction_quotientMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftRawRetraction_quotientMap

@[simp]
theorem connectedSumNeckLeftPushRaw_zero
    {K L : Type u}
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (z : ConnectedSumNeckLeftPrequotient leftBoundary rightBoundary glue) :
    connectedSumNeckLeftPushRaw leftBoundary rightBoundary glue (0, z) =
      connectedSumNeckLeftQuotientMap leftBoundary rightBoundary glue z := by
  apply Subtype.ext
  rcases z with ⟨z, hz⟩
  change connectedSumNeckLeftRaw z at hz
  rcases z with p | (k | l)
  · change adjunctionCell connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
        (connectedSumNeckLeftPushCylinder 0 p) = _
    rw [connectedSumNeckLeftPushCylinder_zero]
    rfl
  · rfl
  · exact False.elim hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRaw_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRaw_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRaw_zero ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRaw_zero

@[simp]
theorem connectedSumNeckLeftPushRaw_one
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (z : ConnectedSumNeckLeftPrequotient leftBoundary rightBoundary glue) :
    connectedSumNeckLeftPushRaw leftBoundary rightBoundary glue (1, z) =
      connectedSumNeckLeftCoverInclusion leftBoundary rightBoundary glue
        (connectedSumNeckLeftRawRetraction leftBoundary rightBoundary glue z) := by
  apply Subtype.ext
  rcases z with ⟨z, hz⟩
  change connectedSumNeckLeftRaw z at hz
  rcases z with p | (k | l)
  · change adjunctionCell connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
        (connectedSumNeckLeftPushCylinder 1 p) =
      connectedSumNeckLeftInclusion leftBoundary rightBoundary glue (leftBoundary p.1)
    rw [connectedSumNeckLeftPushCylinder_one]
    exact adjunction_coherence connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) (Sum.inl p.1)
  · rfl
  · exact False.elim hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRaw_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRaw_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRaw_one ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPushRaw_one

@[simp]
theorem connectedSumNeckLeftPush_zero
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (q : ↑(connectedSumNeckLeft leftBoundary rightBoundary glue)) :
    connectedSumNeckLeftPush leftBoundary rightBoundary glue (0, q) = q := by
  obtain ⟨z, rfl⟩ := (isQuotientMap_connectedSumNeckLeftQuotientMap
    leftBoundary rightBoundary glue).surjective q
  rw [connectedSumNeckLeftPush, connectedSumNeckLeftPushAt_quotientMap,
    connectedSumNeckLeftPushRaw_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPush_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPush_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPush_zero ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPush_zero

@[simp]
theorem connectedSumNeckLeftPush_one
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (hleft : Continuous leftBoundary)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (q : ↑(connectedSumNeckLeft leftBoundary rightBoundary glue)) :
    connectedSumNeckLeftPush leftBoundary rightBoundary glue (1, q) =
      connectedSumNeckLeftCoverInclusion leftBoundary rightBoundary glue
        (connectedSumNeckLeftRetraction leftBoundary hleft rightBoundary glue q) := by
  obtain ⟨z, rfl⟩ := (isQuotientMap_connectedSumNeckLeftQuotientMap
    leftBoundary rightBoundary glue).surjective q
  rw [connectedSumNeckLeftPush, connectedSumNeckLeftPushAt_quotientMap,
    connectedSumNeckLeftPushRaw_one,
    connectedSumNeckLeftRawRetraction_quotientMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPush_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPush_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPush_one ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftPush_one

noncomputable def connectedSumNeckLeftHomotopyEquiv
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (hleft : Continuous leftBoundary)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    K ≃ₕ ↑(connectedSumNeckLeft leftBoundary rightBoundary glue) where
  toFun := connectedSumNeckLeftCoverInclusion leftBoundary rightBoundary glue
  invFun := connectedSumNeckLeftRetraction leftBoundary hleft rightBoundary glue
  left_inv := by
    rw [show (connectedSumNeckLeftRetraction leftBoundary hleft rightBoundary glue).comp
        (connectedSumNeckLeftCoverInclusion leftBoundary rightBoundary glue) =
      ContinuousMap.id K by
        ext k
        exact connectedSumNeckLeftRetraction_inclusion
          leftBoundary hleft rightBoundary glue k]
  right_inv := by
    let H : ContinuousMap.Homotopy
        (ContinuousMap.id ↑(connectedSumNeckLeft leftBoundary rightBoundary glue))
        ((connectedSumNeckLeftCoverInclusion leftBoundary rightBoundary glue).comp
          (connectedSumNeckLeftRetraction leftBoundary hleft rightBoundary glue)) := {
      toContinuousMap := ⟨connectedSumNeckLeftPush leftBoundary rightBoundary glue,
        continuous_connectedSumNeckLeftPush leftBoundary rightBoundary glue⟩
      map_zero_left := connectedSumNeckLeftPush_zero leftBoundary rightBoundary glue
      map_one_left := connectedSumNeckLeftPush_one
        leftBoundary hleft rightBoundary glue
    }
    exact ⟨H.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftHomotopyEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckLeftHomotopyEquiv




def connectedSumNeckReverseCylinderHomeomorph
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    ConnectedSumNeckCylinder ≃ₜ ConnectedSumNeckCylinder :=
  glue.prodCongr unitInterval.symmHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseCylinderHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseCylinderHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseCylinderHomeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseCylinderHomeomorph

@[simp]
theorem connectedSumNeckReverseCylinderHomeomorph_apply
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (p : ConnectedSumNeckCylinder) :
    connectedSumNeckReverseCylinderHomeomorph glue p =
      (glue p.1, unitInterval.symm p.2) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseCylinderHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseCylinderHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseCylinderHomeomorph_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseCylinderHomeomorph_apply


def connectedSumNeckReverseRawHomeomorph
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    ConnectedSumNeckCylinder ⊕ (K ⊕ L) ≃ₜ
      ConnectedSumNeckCylinder ⊕ (L ⊕ K) :=
  (connectedSumNeckReverseCylinderHomeomorph glue).sumCongr
    (Homeomorph.sumComm K L)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRawHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRawHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRawHomeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRawHomeomorph

@[simp]
theorem connectedSumNeckReverseRawHomeomorph_inl
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (p : ConnectedSumNeckCylinder) :
    connectedSumNeckReverseRawHomeomorph (K := K) (L := L) glue (Sum.inl p) =
      Sum.inl (glue p.1, unitInterval.symm p.2) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRawHomeomorph_inl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRawHomeomorph_inl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRawHomeomorph_inl ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRawHomeomorph_inl

@[simp]
theorem connectedSumNeckReverseRawHomeomorph_inr_inl
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (k : K) :
    connectedSumNeckReverseRawHomeomorph (K := K) (L := L) glue
        (Sum.inr (Sum.inl k)) = Sum.inr (Sum.inr k) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRawHomeomorph_inr_inl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRawHomeomorph_inr_inl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRawHomeomorph_inr_inl ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRawHomeomorph_inr_inl

@[simp]
theorem connectedSumNeckReverseRawHomeomorph_inr_inr
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) (l : L) :
    connectedSumNeckReverseRawHomeomorph (K := K) (L := L) glue
        (Sum.inr (Sum.inr l)) = Sum.inr (Sum.inl l) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRawHomeomorph_inr_inr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRawHomeomorph_inr_inr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRawHomeomorph_inr_inr ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRawHomeomorph_inr_inr

theorem connectedSumNeckReverseRaw_eq_of_rel
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (a b : ConnectedSumNeckCylinder ⊕ (K ⊕ L))
    (hab : adjunctionRel connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) a b) :
    adjunctionMk connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap rightBoundary leftBoundary glue.symm)
        (connectedSumNeckReverseRawHomeomorph glue a) =
      adjunctionMk connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap rightBoundary leftBoundary glue.symm)
        (connectedSumNeckReverseRawHomeomorph glue b) := by
  rcases hab with ⟨q, hq | hq⟩
  · rcases hq with ⟨rfl, rfl⟩
    cases q with
    | inl b =>
      simp only [connectedSumNeckBoundaryInclusion,
        connectedSumNeckAttachingMap,
        connectedSumNeckReverseRawHomeomorph_inl,
        connectedSumNeckReverseRawHomeomorph_inr_inl,
        unitInterval.symm_zero]
      change adjunctionCell connectedSumNeckBoundaryInclusion
          (connectedSumNeckAttachingMap rightBoundary leftBoundary glue.symm)
            (glue b, 1) =
        adjunctionLower (connectedSumNeckAttachingMap rightBoundary leftBoundary glue.symm)
          (Sum.inr (leftBoundary b))
      convert adjunction_coherence connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap rightBoundary leftBoundary glue.symm)
        (Sum.inr (glue b)) using 1 <;>
          simp [connectedSumNeckBoundaryInclusion, connectedSumNeckAttachingMap]
    | inr b =>
      simp only [connectedSumNeckBoundaryInclusion,
        connectedSumNeckAttachingMap,
        connectedSumNeckReverseRawHomeomorph_inl,
        connectedSumNeckReverseRawHomeomorph_inr_inr,
        unitInterval.symm_one]
      change adjunctionCell connectedSumNeckBoundaryInclusion
          (connectedSumNeckAttachingMap rightBoundary leftBoundary glue.symm)
            (glue b, 0) =
        adjunctionLower (connectedSumNeckAttachingMap rightBoundary leftBoundary glue.symm)
          (Sum.inl (rightBoundary (glue b)))
      convert adjunction_coherence connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap rightBoundary leftBoundary glue.symm)
        (Sum.inl (glue b)) using 1 <;>
          simp [connectedSumNeckBoundaryInclusion, connectedSumNeckAttachingMap]
  · rcases hq with ⟨rfl, rfl⟩
    symm
    cases q with
    | inl b =>
      simp only [connectedSumNeckBoundaryInclusion,
        connectedSumNeckAttachingMap,
        connectedSumNeckReverseRawHomeomorph_inl,
        connectedSumNeckReverseRawHomeomorph_inr_inl,
        unitInterval.symm_zero]
      change adjunctionCell connectedSumNeckBoundaryInclusion
          (connectedSumNeckAttachingMap rightBoundary leftBoundary glue.symm)
            (glue b, 1) =
        adjunctionLower (connectedSumNeckAttachingMap rightBoundary leftBoundary glue.symm)
          (Sum.inr (leftBoundary b))
      convert adjunction_coherence connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap rightBoundary leftBoundary glue.symm)
        (Sum.inr (glue b)) using 1 <;>
          simp [connectedSumNeckBoundaryInclusion, connectedSumNeckAttachingMap]
    | inr b =>
      simp only [connectedSumNeckBoundaryInclusion,
        connectedSumNeckAttachingMap,
        connectedSumNeckReverseRawHomeomorph_inl,
        connectedSumNeckReverseRawHomeomorph_inr_inr,
        unitInterval.symm_one]
      change adjunctionCell connectedSumNeckBoundaryInclusion
          (connectedSumNeckAttachingMap rightBoundary leftBoundary glue.symm)
            (glue b, 0) =
        adjunctionLower (connectedSumNeckAttachingMap rightBoundary leftBoundary glue.symm)
          (Sum.inl (rightBoundary (glue b)))
      convert adjunction_coherence connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap rightBoundary leftBoundary glue.symm)
        (Sum.inl (glue b)) using 1 <;>
          simp [connectedSumNeckBoundaryInclusion, connectedSumNeckAttachingMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRaw_eq_of_rel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRaw_eq_of_rel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRaw_eq_of_rel ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseRaw_eq_of_rel


noncomputable def connectedSumNeckReverse
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    ConnectedSumNeck leftBoundary rightBoundary glue →
      ConnectedSumNeck rightBoundary leftBoundary glue.symm :=
  Quot.lift (fun z ↦ adjunctionMk connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap rightBoundary leftBoundary glue.symm)
      (connectedSumNeckReverseRawHomeomorph glue z))
    (connectedSumNeckReverseRaw_eq_of_rel leftBoundary rightBoundary glue)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverse ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverse

theorem continuous_connectedSumNeckReverse
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    Continuous (connectedSumNeckReverse leftBoundary rightBoundary glue) := by
  apply continuous_adjunction_lift connectedSumNeckBoundaryInclusion
    (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
    (connectedSumNeckReverseRaw_eq_of_rel leftBoundary rightBoundary glue)
  exact (continuous_adjunctionMk connectedSumNeckBoundaryInclusion
    (connectedSumNeckAttachingMap rightBoundary leftBoundary glue.symm)).comp
      (connectedSumNeckReverseRawHomeomorph glue).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckReverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckReverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckReverse ``Submission.DifferentialGeometry.Topology.ThreeManifold.continuous_connectedSumNeckReverse

@[simp]
theorem connectedSumNeckReverse_reverse
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (q : ConnectedSumNeck leftBoundary rightBoundary glue) :
    connectedSumNeckReverse rightBoundary leftBoundary glue.symm
        (connectedSumNeckReverse leftBoundary rightBoundary glue q) = q := by
  refine Quot.inductionOn q ?_
  intro z
  rcases z with p | (k | l)
  · change adjunctionMk connectedSumNeckBoundaryInclusion
      (connectedSumNeckAttachingMap leftBoundary rightBoundary glue)
        (Sum.inl (glue.symm (glue p.1),
          unitInterval.symm (unitInterval.symm p.2))) =
      adjunctionMk connectedSumNeckBoundaryInclusion
        (connectedSumNeckAttachingMap leftBoundary rightBoundary glue) (Sum.inl p)
    congr 3 <;> simp
  · rfl
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverse_reverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverse_reverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverse_reverse ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverse_reverse


noncomputable def connectedSumNeckReverseHomeomorph
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    ConnectedSumNeck leftBoundary rightBoundary glue ≃ₜ
      ConnectedSumNeck rightBoundary leftBoundary glue.symm where
  toFun := connectedSumNeckReverse leftBoundary rightBoundary glue
  invFun := connectedSumNeckReverse rightBoundary leftBoundary glue.symm
  left_inv := connectedSumNeckReverse_reverse leftBoundary rightBoundary glue
  right_inv := connectedSumNeckReverse_reverse rightBoundary leftBoundary glue.symm
  continuous_toFun := continuous_connectedSumNeckReverse leftBoundary rightBoundary glue
  continuous_invFun := continuous_connectedSumNeckReverse
    rightBoundary leftBoundary glue.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseHomeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverseHomeomorph

theorem connectedSumNeckReverse_mem_left_iff_mem_right
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (q : ConnectedSumNeck leftBoundary rightBoundary glue) :
    connectedSumNeckReverse leftBoundary rightBoundary glue q ∈
        connectedSumNeckLeft rightBoundary leftBoundary glue.symm ↔
      q ∈ connectedSumNeckRight leftBoundary rightBoundary glue := by
  refine Quot.inductionOn q ?_
  intro z
  rcases z with p | (k | l)
  · change 1 - (p.2 : ℝ) < 2 / 3 ↔ 1 / 3 < (p.2 : ℝ)
    constructor <;> intro h <;> linarith
  · rfl
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverse_mem_left_iff_mem_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverse_mem_left_iff_mem_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverse_mem_left_iff_mem_right ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckReverse_mem_left_iff_mem_right

noncomputable def connectedSumNeckRightToSwappedLeftHomeomorph
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    ↑(connectedSumNeckRight leftBoundary rightBoundary glue) ≃ₜ
      ↑(connectedSumNeckLeft rightBoundary leftBoundary glue.symm) where
  toFun q := ⟨connectedSumNeckReverse leftBoundary rightBoundary glue q,
    (connectedSumNeckReverse_mem_left_iff_mem_right
      leftBoundary rightBoundary glue q).2 q.2⟩
  invFun q := ⟨connectedSumNeckReverse rightBoundary leftBoundary glue.symm q, by
    have h := connectedSumNeckReverse_mem_left_iff_mem_right
      leftBoundary rightBoundary glue
        (connectedSumNeckReverse rightBoundary leftBoundary glue.symm q)
    have hr : connectedSumNeckReverse leftBoundary rightBoundary glue
        (connectedSumNeckReverse rightBoundary leftBoundary glue.symm q) = q := by
      simpa using connectedSumNeckReverse_reverse
        rightBoundary leftBoundary glue.symm q
    rw [hr] at h
    exact h.1 q.2⟩
  left_inv := fun q ↦ Subtype.ext
    (connectedSumNeckReverse_reverse leftBoundary rightBoundary glue q)
  right_inv := fun q ↦ Subtype.ext
    (connectedSumNeckReverse_reverse rightBoundary leftBoundary glue.symm q)
  continuous_toFun := Continuous.subtype_mk
    ((continuous_connectedSumNeckReverse leftBoundary rightBoundary glue).comp
      continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    ((continuous_connectedSumNeckReverse rightBoundary leftBoundary glue.symm).comp
      continuous_subtype_val) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightToSwappedLeftHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightToSwappedLeftHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightToSwappedLeftHomeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightToSwappedLeftHomeomorph


def connectedSumNeckRightCoverInclusion
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    C(L, ↑(connectedSumNeckRight leftBoundary rightBoundary glue)) where
  toFun l := ⟨connectedSumNeckRightInclusion leftBoundary rightBoundary glue l, trivial⟩
  continuous_toFun := Continuous.subtype_mk
    (continuous_connectedSumNeckRightInclusion leftBoundary rightBoundary glue) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightCoverInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightCoverInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightCoverInclusion ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightCoverInclusion


noncomputable def connectedSumNeckRightHomotopyEquiv
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (hright : Continuous rightBoundary) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    L ≃ₕ ↑(connectedSumNeckRight leftBoundary rightBoundary glue) :=
  (connectedSumNeckLeftHomotopyEquiv
      rightBoundary hright leftBoundary glue.symm).trans
    (connectedSumNeckRightToSwappedLeftHomeomorph
      leftBoundary rightBoundary glue).symm.toHomotopyEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightHomotopyEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightHomotopyEquiv

@[simp]
theorem connectedSumNeckRightHomotopyEquiv_apply
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (hright : Continuous rightBoundary) (glue : CellBoundary 3 ≃ₜ CellBoundary 3)
    (l : L) :
    connectedSumNeckRightHomotopyEquiv leftBoundary rightBoundary hright glue l =
      connectedSumNeckRightCoverInclusion leftBoundary rightBoundary glue l := by
  apply Subtype.ext
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightHomotopyEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightHomotopyEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightHomotopyEquiv_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.connectedSumNeckRightHomotopyEquiv_apply


theorem pathConnectedSpace_of_homotopyEquiv
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] (e : X ≃ₕ Y) : PathConnectedSpace Y := by
  constructor
  · exact ⟨e (Classical.choice (inferInstance : Nonempty X))⟩
  · intro y₀ y₁
    obtain ⟨H⟩ := e.right_inv
    have h₀ : Joined y₀ (e (e.symm y₀)) := ⟨(H.evalAt y₀).symm⟩
    have hmid : Joined (e (e.symm y₀)) (e (e.symm y₁)) :=
      (PathConnectedSpace.joined (e.symm y₀) (e.symm y₁)).map e.continuous
    have h₁ : Joined (e (e.symm y₁)) y₁ := ⟨H.evalAt y₁⟩
    exact h₀.trans (hmid.trans h₁)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.pathConnectedSpace_of_homotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.pathConnectedSpace_of_homotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.pathConnectedSpace_of_homotopyEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.pathConnectedSpace_of_homotopyEquiv


theorem pathConnectedSpace_connectedSumNeckLeft
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    [PathConnectedSpace K]
    (leftBoundary : CellBoundary 3 → K) (hleft : Continuous leftBoundary)
    (rightBoundary : CellBoundary 3 → L) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    PathConnectedSpace ↑(connectedSumNeckLeft leftBoundary rightBoundary glue) :=
  pathConnectedSpace_of_homotopyEquiv
    (connectedSumNeckLeftHomotopyEquiv leftBoundary hleft rightBoundary glue)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.pathConnectedSpace_connectedSumNeckLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.pathConnectedSpace_connectedSumNeckLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.pathConnectedSpace_connectedSumNeckLeft ``Submission.DifferentialGeometry.Topology.ThreeManifold.pathConnectedSpace_connectedSumNeckLeft


theorem pathConnectedSpace_connectedSumNeckRight
    {K L : Type u} [TopologicalSpace K] [TopologicalSpace L]
    [PathConnectedSpace L]
    (leftBoundary : CellBoundary 3 → K) (rightBoundary : CellBoundary 3 → L)
    (hright : Continuous rightBoundary) (glue : CellBoundary 3 ≃ₜ CellBoundary 3) :
    PathConnectedSpace ↑(connectedSumNeckRight leftBoundary rightBoundary glue) :=
  pathConnectedSpace_of_homotopyEquiv
    (connectedSumNeckRightHomotopyEquiv leftBoundary rightBoundary hright glue)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.pathConnectedSpace_connectedSumNeckRight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.pathConnectedSpace_connectedSumNeckRight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.pathConnectedSpace_connectedSumNeckRight ``Submission.DifferentialGeometry.Topology.ThreeManifold.pathConnectedSpace_connectedSumNeckRight

end DifferentialGeometry.Topology.ThreeManifold
