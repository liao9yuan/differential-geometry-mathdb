import Submission.DifferentialGeometry.Topology.VanKampen.TwoSidedCollarSeparation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

section

variable {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]
  {e : S → X} (c : TwoSidedCollar e) (U : Set X) (hU : c.range ⊆ U)

def codRestrict :
    TwoSidedCollar (U.codRestrict e (fun s ↦ hU ⟨(s, 0), c.zero_eq s⟩)) where
  toFun := U.codRestrict c.toFun (fun p ↦ hU ⟨p, rfl⟩)
  isOpenEmbedding_toFun := .of_isEmbedding_isOpenMap
    (c.isOpenEmbedding_toFun.toIsEmbedding.codRestrict U (fun p ↦ hU ⟨p, rfl⟩))
    (c.isOpenEmbedding_toFun.isOpenMap.codRestrict (fun p ↦ hU ⟨p, rfl⟩))
  zero_eq s := Subtype.ext (c.zero_eq s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict

@[simp]
theorem codRestrict_toFun_val (p : S × ℝ) :
    ((c.codRestrict U hU).toFun p).val = c.toFun p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict_toFun_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict_toFun_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict_toFun_val ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict_toFun_val

@[simp]
theorem codRestrict_range :
    (c.codRestrict U hU).range = Subtype.val ⁻¹' c.range := by
  ext x
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, congrArg Subtype.val hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, Subtype.ext hp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict_range ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict_range

theorem image_codRestrict_range :
    Subtype.val '' (c.codRestrict U hU).range = c.range := by
  ext x
  constructor
  · rintro ⟨y, ⟨p, rfl⟩, rfl⟩
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨(c.codRestrict U hU).toFun p, ⟨p, rfl⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.image_codRestrict_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.image_codRestrict_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.image_codRestrict_range ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.image_codRestrict_range

theorem codRestrict_toFun_zero_val (s : S) :
    ((c.codRestrict U hU).toFun (s, 0)).val = e s := c.zero_eq s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict_toFun_zero_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict_toFun_zero_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict_toFun_zero_val ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict_toFun_zero_val

theorem codRestrict_complement :
    (c.codRestrict U hU).complement = Subtype.val ⁻¹' c.complement := by
  ext x
  change (¬ ∃ s : S, (⟨e s, hU ⟨(s, 0), c.zero_eq s⟩⟩ : U) = x) ↔
    ¬ ∃ s : S, e s = x.val
  constructor
  · intro hx hs
    obtain ⟨s, hs⟩ := hs
    exact hx ⟨s, Subtype.ext hs⟩
  · intro hx hs
    obtain ⟨s, hs⟩ := hs
    exact hx ⟨s, congrArg Subtype.val hs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict_complement ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.codRestrict_complement

end

section

universe u v w

variable {X : Type u} [TopologicalSpace X] {S : Type v} [TopologicalSpace S]
  {ι : Type w} {e : ι → S → X}

theorem range_subset_connectedComponentIn_complement
    [PreconnectedSpace S] (c : ∀ i, TwoSidedCollar (e i))
    (hdisj : Pairwise fun i j => Disjoint (c i).range (c j).range)
    (J : Set ι) {i : ι} (hi : i ∉ J) {x : X} (hx : x ∈ (c i).range) :
    (c i).range ⊆ connectedComponentIn (⋃ j ∈ J, Set.range (e j))ᶜ x := by
  have hsub : (c i).range ⊆ (⋃ j ∈ J, Set.range (e j))ᶜ := by
    intro y hy hyJ
    obtain ⟨j, hjJ, s, hs⟩ := by simpa only [_root_.Set.mem_iUnion, _root_.Set.mem_range] using hyJ
    have hij : i ≠ j := fun hij => hi (hij.symm ▸ hjJ)
    exact Set.disjoint_left.mp (hdisj hij) hy
      ⟨(s, 0), ((c j).zero_eq s).trans hs⟩
  exact IsPreconnected.subset_connectedComponentIn
    (isPreconnected_range (c i).isOpenEmbedding_toFun.continuous) hx hsub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_subset_connectedComponentIn_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_subset_connectedComponentIn_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_subset_connectedComponentIn_complement ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_subset_connectedComponentIn_complement

end

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
