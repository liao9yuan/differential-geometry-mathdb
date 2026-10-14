import Mathlib.Topology.Connected.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Submission.DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

section

variable {X : Type*} [TopologicalSpace X]

theorem connectedComponentIn_inter_connectedComponentIn {A B : Set X} (hBA : B ⊆ A)
    (x : X) :
    connectedComponentIn (connectedComponentIn A x ∩ B) x = connectedComponentIn B x := by
  apply le_antisymm (connectedComponentIn_mono x _root_.Set.inter_subset_right)
  by_cases hx : x ∈ B
  · apply isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx)
    exact _root_.Set.subset_inter (connectedComponentIn_mono x hBA) (connectedComponentIn_subset B x)
  · rw [connectedComponentIn_eq_empty hx]
    exact _root_.Set.empty_subset _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `connectedComponentIn_inter_connectedComponentIn then
    throwError "Refusing to shadow existing declaration connectedComponentIn_inter_connectedComponentIn"
  Lean.modifyEnv fun env => Lean.addAlias env `connectedComponentIn_inter_connectedComponentIn ``Submission.connectedComponentIn_inter_connectedComponentIn

theorem image_connectedComponentIn_preimage_connectedComponentIn {A B : Set X}
    (hBA : B ⊆ A) {x : X} (hx : x ∈ B) :
    Subtype.val '' connectedComponentIn
      (Subtype.val ⁻¹' B : Set (connectedComponentIn A x))
      ⟨x, mem_connectedComponentIn (hBA hx)⟩ = connectedComponentIn B x := by
  let C := connectedComponentIn A x
  let y : C := ⟨x, mem_connectedComponentIn (hBA hx)⟩
  change Subtype.val '' connectedComponentIn (Subtype.val ⁻¹' B : Set C) y = _
  have hsub : connectedComponentIn B x ⊆ C := connectedComponentIn_mono x hBA
  have himage : Subtype.val '' (Subtype.val ⁻¹' connectedComponentIn B x : Set C) =
      connectedComponentIn B x := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hsub]
  apply le_antisymm
  · apply isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn
      |>.subset_connectedComponentIn
        (_root_.Set.mem_image_of_mem Subtype.val (mem_connectedComponentIn hx))
    rintro z ⟨w, hw, rfl⟩
    exact (connectedComponentIn_subset (Subtype.val ⁻¹' B : Set C) y) hw
  · rw [← himage]
    apply _root_.Set.image_mono
    have hp : IsPreconnected (Subtype.val ⁻¹' connectedComponentIn B x : Set C) :=
      Topology.IsInducing.subtypeVal.isPreconnected_image.mp
        (himage.symm ▸ isPreconnected_connectedComponentIn)
    exact hp.subset_connectedComponentIn (mem_connectedComponentIn hx)
      (_root_.Set.preimage_mono (connectedComponentIn_subset B x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `image_connectedComponentIn_preimage_connectedComponentIn then
    throwError "Refusing to shadow existing declaration image_connectedComponentIn_preimage_connectedComponentIn"
  Lean.modifyEnv fun env => Lean.addAlias env `image_connectedComponentIn_preimage_connectedComponentIn ``Submission.image_connectedComponentIn_preimage_connectedComponentIn

end

noncomputable section

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {U : Set X} {x : X} (hx : x ∈ U)

def connectedComponentHomeomorphConnectedComponentIn :
    connectedComponent (⟨x, hx⟩ : U) ≃ₜ connectedComponentIn U x :=
  (Topology.IsEmbedding.subtypeVal.homeomorphImage
    (connectedComponent (⟨x, hx⟩ : U))).trans
      (Homeomorph.setCongr (connectedComponentIn_eq_image hx).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedComponentHomeomorphConnectedComponentIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedComponentHomeomorphConnectedComponentIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedComponentHomeomorphConnectedComponentIn ``Submission.DifferentialGeometry.Topology.connectedComponentHomeomorphConnectedComponentIn

theorem simplyConnectedSpace_connectedComponentIn_iff :
    SimplyConnectedSpace (connectedComponentIn U x) ↔
      SimplyConnectedSpace (connectedComponent (⟨x, hx⟩ : U)) :=
  (connectedComponentHomeomorphConnectedComponentIn hx).toHomotopyEquiv.simplyConnectedSpace_iff.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplyConnectedSpace_connectedComponentIn_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplyConnectedSpace_connectedComponentIn_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplyConnectedSpace_connectedComponentIn_iff ``Submission.DifferentialGeometry.Topology.simplyConnectedSpace_connectedComponentIn_iff

end DifferentialGeometry.Topology

theorem closure_connectedComponentIn_inter {X : Type*} [TopologicalSpace X]
    (U : Set X) (x : X) : closure (connectedComponentIn U x) ∩ U = connectedComponentIn U x := by
  by_cases hx : x ∈ U
  · rw [connectedComponentIn_eq_image hx]
    ext y
    constructor
    · rintro ⟨hy, hyU⟩
      have hmem : (⟨y, hyU⟩ : U) ∈ closure (connectedComponent (⟨x, hx⟩ : U)) := by
        rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
        exact hy
      rw [isClosed_connectedComponent.closure_eq] at hmem
      exact ⟨⟨y, hyU⟩, hmem, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨subset_closure (_root_.Set.mem_image_of_mem Subtype.val hy), y.property⟩
  · rw [connectedComponentIn_eq_empty hx, closure_empty, _root_.Set.empty_inter]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `closure_connectedComponentIn_inter then
    throwError "Refusing to shadow existing declaration closure_connectedComponentIn_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `closure_connectedComponentIn_inter ``Submission.closure_connectedComponentIn_inter

open _root_.IsPreconnected in
theorem IsPreconnected.subset_connectedComponentIn_pair
    {X : Type*} [TopologicalSpace X] {U A B : Set X} {p q : X}
    (hA : IsPreconnected A) (hB : IsPreconnected B) (hAU : A ⊆ U) (hBU : B ⊆ U)
    (hp : ((A ∪ B) ∩ _root_.connectedComponentIn U p).Nonempty)
    (hq : ((A ∪ B) ∩ _root_.connectedComponentIn U q).Nonempty)
    (hne : _root_.connectedComponentIn U p ≠ _root_.connectedComponentIn U q) :
    (A ⊆ _root_.connectedComponentIn U p ∧ B ⊆ _root_.connectedComponentIn U q) ∨
      (A ⊆ _root_.connectedComponentIn U q ∧ B ⊆ _root_.connectedComponentIn U p) := by
  have hsub {C : Set X} (hC : IsPreconnected C) (hCU : C ⊆ U)
      {r z : X} (hzC : z ∈ C) (hzr : z ∈ _root_.connectedComponentIn U r) :
      C ⊆ _root_.connectedComponentIn U r := by
    rw [connectedComponentIn_eq hzr]
    exact hC.subset_connectedComponentIn hzC hCU
  obtain ⟨u, huAB, hup⟩ := hp
  obtain ⟨v, hvAB, hvq⟩ := hq
  rcases huAB with huA | huB
  · have hAp := hsub hA hAU huA hup
    rcases hvAB with hvA | hvB
    · exact False.elim (hne ((connectedComponentIn_eq (hAp hvA)).trans
        (connectedComponentIn_eq hvq).symm))
    · exact Or.inl ⟨hAp, hsub hB hBU hvB hvq⟩
  · have hBp := hsub hB hBU huB hup
    rcases hvAB with hvA | hvB
    · exact Or.inr ⟨hsub hA hAU hvA hvq, hBp⟩
    · exact False.elim (hne ((connectedComponentIn_eq (hBp hvB)).trans
        (connectedComponentIn_eq hvq).symm))

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.IsPreconnected
  let env ← Lean.getEnv
  if env.contains `IsPreconnected.subset_connectedComponentIn_pair then
    throwError "Refusing to shadow existing declaration IsPreconnected.subset_connectedComponentIn_pair"
  Lean.modifyEnv fun env => Lean.addAlias env `IsPreconnected.subset_connectedComponentIn_pair ``Submission.IsPreconnected.subset_connectedComponentIn_pair

open scoped _root_.Topology in
open _root_.IsPreconnected in
theorem IsPreconnected.subset_connectedComponentIn_pair_of_mem_closure
    {X : Type*} [TopologicalSpace X] {U N A B : Set X} {x p q : X}
    (hA : IsPreconnected A) (hB : IsPreconnected B)
    (hxN : N ∈ 𝓝 x) (hcover : N ∩ U = A ∪ B)
    (hp : x ∈ closure (_root_.connectedComponentIn U p))
    (hq : x ∈ closure (_root_.connectedComponentIn U q))
    (hne : _root_.connectedComponentIn U p ≠ _root_.connectedComponentIn U q) :
    (A ⊆ _root_.connectedComponentIn U p ∧ B ⊆ _root_.connectedComponentIn U q) ∨
      (A ⊆ _root_.connectedComponentIn U q ∧ B ⊆ _root_.connectedComponentIn U p) := by
  have hAU : A ⊆ U := fun z hz => (hcover.symm.subset (Or.inl hz)).2
  have hBU : B ⊆ U := fun z hz => (hcover.symm.subset (Or.inr hz)).2
  obtain ⟨u, huN, hup⟩ := mem_closure_iff_nhds.mp hp N hxN
  obtain ⟨v, hvN, hvq⟩ := mem_closure_iff_nhds.mp hq N hxN
  exact hA.subset_connectedComponentIn_pair hB hAU hBU
    ⟨u, hcover.subset ⟨huN, connectedComponentIn_subset U p hup⟩, hup⟩
    ⟨v, hcover.subset ⟨hvN, connectedComponentIn_subset U q hvq⟩, hvq⟩ hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsPreconnected.subset_connectedComponentIn_pair_of_mem_closure then
    throwError "Refusing to shadow existing declaration IsPreconnected.subset_connectedComponentIn_pair_of_mem_closure"
  Lean.modifyEnv fun env => Lean.addAlias env `IsPreconnected.subset_connectedComponentIn_pair_of_mem_closure ``Submission.IsPreconnected.subset_connectedComponentIn_pair_of_mem_closure

open _root_.IsClosed in
theorem IsClosed.connectedComponentIn {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsClosed U) (x : X) : IsClosed (connectedComponentIn U x) := by
  by_cases hx : x ∈ U
  · apply isClosed_of_closure_subset
    exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx))
      (closure_minimal (connectedComponentIn_subset U x) hU)
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.IsClosed
  let env ← Lean.getEnv
  if env.contains `IsClosed.connectedComponentIn then
    throwError "Refusing to shadow existing declaration IsClosed.connectedComponentIn"
  Lean.modifyEnv fun env => Lean.addAlias env `IsClosed.connectedComponentIn ``Submission.IsClosed.connectedComponentIn

theorem closure_connectedComponentIn_subset {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hV : IsClosed V) (hUV : U ⊆ V) (x : X) :
    closure (connectedComponentIn U x) ⊆ connectedComponentIn V x :=
  closure_minimal (connectedComponentIn_mono x hUV) (hV.connectedComponentIn x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `closure_connectedComponentIn_subset then
    throwError "Refusing to shadow existing declaration closure_connectedComponentIn_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `closure_connectedComponentIn_subset ``Submission.closure_connectedComponentIn_subset

open _root_.ContinuousOn in
theorem ContinuousOn.mem_closure_connectedComponentIn_inter
    {X : Type*} [TopologicalSpace X] {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (_root_.Set.Icc a b)) (hab : a < b)
    {A W : Set X} (hA : _root_.Set.MapsTo γ (_root_.Set.Ioc a b) A) (hW : _root_.Set.MapsTo γ (_root_.Set.Ioo a b) W) :
    γ a ∈ closure (connectedComponentIn A (γ b) ∩ W) := by
  have hconn : IsPreconnected (γ '' _root_.Set.Ioc a b) :=
    isPreconnected_Ioc.image γ (hγ.mono _root_.Set.Ioc_subset_Icc_self)
  have hsub : γ '' _root_.Set.Ioc a b ⊆ connectedComponentIn A (γ b) :=
    hconn.subset_connectedComponentIn (_root_.Set.mem_image_of_mem γ ⟨hab, le_rfl⟩) hA.image_subset
  have ha : a ∈ closure (_root_.Set.Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact ⟨le_rfl, hab.le⟩
  exact ((hγ a ⟨le_rfl, hab.le⟩).mono _root_.Set.Ioo_subset_Icc_self).mem_closure ha
    (fun t ht => ⟨hsub (_root_.Set.mem_image_of_mem γ ⟨ht.1, ht.2.le⟩), hW ht⟩)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContinuousOn
  let env ← Lean.getEnv
  if env.contains `ContinuousOn.mem_closure_connectedComponentIn_inter then
    throwError "Refusing to shadow existing declaration ContinuousOn.mem_closure_connectedComponentIn_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousOn.mem_closure_connectedComponentIn_inter ``Submission.ContinuousOn.mem_closure_connectedComponentIn_inter
