import Submission.DifferentialGeometry.Topology.VanKampen.TwoSidedCollarSeparation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

variable {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]
  {e : S → X} (h : TwoSidedCollar e)


theorem negative_component_ne_positive_of_disconnected
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hsep : ¬ IsConnected h.complement) :
    ConnectedComponents.mk h.negativePoint ≠ ConnectedComponents.mk h.positivePoint := by
  intro hnp
  apply hsep
  rw [isConnected_iff_connectedSpace]
  let _ : Nonempty h.complement := ⟨h.negativePoint⟩
  let _ : PreconnectedSpace h.complement := preconnectedSpace_iff_connectedComponent.mpr (by
    intro y
    apply Set.eq_univ_of_forall
    intro z
    have hy := h.component_eq_negative_or_positive y
    have hz := h.component_eq_negative_or_positive z
    have hzy : ConnectedComponents.mk z = ConnectedComponents.mk y := by
      rcases hz with hz | hz <;> rcases hy with hy | hy
      · exact hz.trans hy.symm
      · exact hz.trans (hnp.trans hy.symm)
      · exact hz.trans (hnp.symm.trans hy.symm)
      · exact hz.trans hy.symm
    rw [← ConnectedComponents.coe_eq_coe.mp hzy]
    exact mem_connectedComponent)
  exact { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negative_component_ne_positive_of_disconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negative_component_ne_positive_of_disconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negative_component_ne_positive_of_disconnected ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negative_component_ne_positive_of_disconnected


theorem disjoint_negativeSide_positiveSide_of_disconnected
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hsep : ¬ IsConnected h.complement) :
    Disjoint h.negativeSide h.positiveSide := by
  rw [Set.disjoint_left]
  rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  have hab' : a = b := Subtype.ext hab.symm
  subst b
  have hccne : connectedComponent h.negativePoint ≠ connectedComponent h.positivePoint :=
    ConnectedComponents.coe_ne_coe.mp (h.negative_component_ne_positive_of_disconnected hsep)
  exact Set.disjoint_left.mp (connectedComponent_disjoint hccne) ha hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.disjoint_negativeSide_positiveSide_of_disconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.disjoint_negativeSide_positiveSide_of_disconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.disjoint_negativeSide_positiveSide_of_disconnected ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.disjoint_negativeSide_positiveSide_of_disconnected


theorem compl_negativeSide_union_zeroSlice_of_disconnected
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hsep : ¬ IsConnected h.complement) :
    (h.negativeSide ∪ Set.range e)ᶜ = h.positiveSide := by
  ext x
  constructor
  · intro hx
    have hxZ : x ∉ Set.range e := fun hxe => hx (Or.inr hxe)
    have hxU : x ∈ h.complement := hxZ
    rw [h.complement_eq_negativeSide_union_positiveSide] at hxU
    exact hxU.resolve_left (fun hxn => hx (Or.inl hxn))
  · intro hxp hx
    rcases hx with hxn | hxz
    · exact Set.disjoint_left.mp (h.disjoint_negativeSide_positiveSide_of_disconnected hsep) hxn hxp
    · exact Set.disjoint_left.mp h.zeroSlice_disjoint_positiveSide hxz hxp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.compl_negativeSide_union_zeroSlice_of_disconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.compl_negativeSide_union_zeroSlice_of_disconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.compl_negativeSide_union_zeroSlice_of_disconnected ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.compl_negativeSide_union_zeroSlice_of_disconnected


theorem compl_positiveSide_union_zeroSlice_of_disconnected
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hsep : ¬ IsConnected h.complement) :
    (h.positiveSide ∪ Set.range e)ᶜ = h.negativeSide := by
  ext x
  constructor
  · intro hx
    have hxZ : x ∉ Set.range e := fun hxe => hx (Or.inr hxe)
    have hxU : x ∈ h.complement := hxZ
    rw [h.complement_eq_negativeSide_union_positiveSide] at hxU
    exact hxU.resolve_right (fun hxp => hx (Or.inl hxp))
  · intro hxn hx
    rcases hx with hxp | hxz
    · exact Set.disjoint_left.mp (h.disjoint_negativeSide_positiveSide_of_disconnected hsep) hxn hxp
    · exact Set.disjoint_left.mp h.zeroSlice_disjoint_negativeSide hxz hxn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.compl_positiveSide_union_zeroSlice_of_disconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.compl_positiveSide_union_zeroSlice_of_disconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.compl_positiveSide_union_zeroSlice_of_disconnected ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.compl_positiveSide_union_zeroSlice_of_disconnected


theorem closure_negativeSide_of_disconnected
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hsep : ¬ IsConnected h.complement) :
    closure h.negativeSide = h.negativeSide ∪ Set.range e := by
  apply Set.Subset.antisymm
  · apply closure_minimal Set.subset_union_left
    rw [← isOpen_compl_iff, (h.compl_negativeSide_union_zeroSlice_of_disconnected hsep)]
    exact h.isOpen_positiveSide
  · exact Set.union_subset subset_closure h.range_e_subset_closure_negativeSide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_negativeSide_of_disconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_negativeSide_of_disconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_negativeSide_of_disconnected ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_negativeSide_of_disconnected


theorem closure_positiveSide_of_disconnected
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hsep : ¬ IsConnected h.complement) :
    closure h.positiveSide = h.positiveSide ∪ Set.range e := by
  apply Set.Subset.antisymm
  · apply closure_minimal Set.subset_union_left
    rw [← isOpen_compl_iff, (h.compl_positiveSide_union_zeroSlice_of_disconnected hsep)]
    exact h.isOpen_negativeSide
  · exact Set.union_subset subset_closure h.range_e_subset_closure_positiveSide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_positiveSide_of_disconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_positiveSide_of_disconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_positiveSide_of_disconnected ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_positiveSide_of_disconnected


theorem frontier_negativeSide_of_disconnected
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hsep : ¬ IsConnected h.complement) :
    frontier h.negativeSide = Set.range e := by
  rw [h.isOpen_negativeSide.frontier_eq, (h.closure_negativeSide_of_disconnected hsep)]
  ext x
  constructor
  · rintro ⟨hxn | hxz, hnotn⟩
    · exact (hnotn hxn).elim
    · exact hxz
  · intro hxz
    exact ⟨Or.inr hxz, fun hxn =>
      Set.disjoint_left.mp h.zeroSlice_disjoint_negativeSide hxz hxn⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_negativeSide_of_disconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_negativeSide_of_disconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_negativeSide_of_disconnected ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_negativeSide_of_disconnected


theorem frontier_positiveSide_of_disconnected
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hsep : ¬ IsConnected h.complement) :
    frontier h.positiveSide = Set.range e := by
  rw [h.isOpen_positiveSide.frontier_eq, (h.closure_positiveSide_of_disconnected hsep)]
  ext x
  constructor
  · rintro ⟨hxp | hxz, hnotp⟩
    · exact (hnotp hxp).elim
    · exact hxz
  · intro hxz
    exact ⟨Or.inr hxz, fun hxp =>
      Set.disjoint_left.mp h.zeroSlice_disjoint_positiveSide hxz hxp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_positiveSide_of_disconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_positiveSide_of_disconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_positiveSide_of_disconnected ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_positiveSide_of_disconnected


theorem isConnected_negativeSide [Nonempty S] : IsConnected h.negativeSide :=
  isConnected_connectedComponent.image Subtype.val continuous_subtype_val.continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isConnected_negativeSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isConnected_negativeSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isConnected_negativeSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isConnected_negativeSide


theorem isConnected_positiveSide [Nonempty S] : IsConnected h.positiveSide :=
  isConnected_connectedComponent.image Subtype.val continuous_subtype_val.continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isConnected_positiveSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isConnected_positiveSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isConnected_positiveSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isConnected_positiveSide

section Separated
variable [CompactSpace S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
  [LocallyPathConnectedSpace X] (hsep : ¬ IsConnected h.complement)

include hsep


theorem toFun_mem_negativeSide_iff (s : S) (t : ℝ) :
    h.toFun (s, t) ∈ h.negativeSide ↔ t < 0 := by
  constructor
  · intro hx
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · exact ht
    · exact (h.negativeSide_subset_complement hx ⟨s, (h.zero_eq s).symm⟩).elim
    · exact (Set.disjoint_left.mp (h.disjoint_negativeSide_positiveSide_of_disconnected hsep)
        hx (h.toFun_mem_positiveSide_of_pos s ht)).elim
  · exact h.toFun_mem_negativeSide_of_neg s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_negativeSide_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_negativeSide_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_negativeSide_iff ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_negativeSide_iff


theorem toFun_mem_positiveSide_iff (s : S) (t : ℝ) :
    h.toFun (s, t) ∈ h.positiveSide ↔ 0 < t := by
  constructor
  · intro hx
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · exact (Set.disjoint_left.mp (h.disjoint_negativeSide_positiveSide_of_disconnected hsep)
        (h.toFun_mem_negativeSide_of_neg s ht) hx).elim
    · exact (h.positiveSide_subset_complement hx ⟨s, (h.zero_eq s).symm⟩).elim
    · exact ht
  · exact h.toFun_mem_positiveSide_of_pos s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_positiveSide_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_positiveSide_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_positiveSide_iff ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_positiveSide_iff


theorem toFun_mem_closure_negativeSide_iff (s : S) (t : ℝ) :
    h.toFun (s, t) ∈ closure h.negativeSide ↔ t ≤ 0 := by
  rw [h.closure_negativeSide_of_disconnected hsep]
  constructor
  · rintro (hn | hz)
    · exact (h.toFun_mem_negativeSide_iff hsep s t).mp hn |>.le
    · by_contra ht
      exact h.toFun_mem_complement_of_ne_zero s (ne_of_gt (lt_of_not_ge ht)) hz
  · intro ht
    rcases lt_or_eq_of_le ht with ht | rfl
    · exact Or.inl (h.toFun_mem_negativeSide_of_neg s ht)
    · exact Or.inr ⟨s, (h.zero_eq s).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_closure_negativeSide_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_closure_negativeSide_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_closure_negativeSide_iff ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_closure_negativeSide_iff


theorem toFun_mem_closure_positiveSide_iff (s : S) (t : ℝ) :
    h.toFun (s, t) ∈ closure h.positiveSide ↔ 0 ≤ t := by
  rw [h.closure_positiveSide_of_disconnected hsep]
  constructor
  · rintro (hp | hz)
    · exact (h.toFun_mem_positiveSide_iff hsep s t).mp hp |>.le
    · by_contra ht
      exact h.toFun_mem_complement_of_ne_zero s (ne_of_lt (lt_of_not_ge ht)) hz
  · intro ht
    rcases lt_or_eq_of_le ht with ht | ht
    · exact Or.inl (h.toFun_mem_positiveSide_of_pos s ht)
    · subst t
      exact Or.inr ⟨s, (h.zero_eq s).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_closure_positiveSide_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_closure_positiveSide_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_closure_positiveSide_iff ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_closure_positiveSide_iff


theorem closure_negativeSide_inter_closure_positiveSide :
    closure h.negativeSide ∩ closure h.positiveSide = Set.range e := by
  rw [h.closure_negativeSide_of_disconnected hsep,
    h.closure_positiveSide_of_disconnected hsep]
  ext x
  constructor
  · rintro ⟨hn | hz, hp | hz'⟩
    · exact (Set.disjoint_left.mp (h.disjoint_negativeSide_positiveSide_of_disconnected hsep)
        hn hp).elim
    · exact hz'
    · exact hz
    · exact hz
  · intro hz
    exact ⟨Or.inr hz, Or.inr hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_negativeSide_inter_closure_positiveSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_negativeSide_inter_closure_positiveSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_negativeSide_inter_closure_positiveSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_negativeSide_inter_closure_positiveSide


theorem closure_negativeSide_union_closure_positiveSide :
    closure h.negativeSide ∪ closure h.positiveSide = Set.univ := by
  rw [h.closure_negativeSide_of_disconnected hsep,
    h.closure_positiveSide_of_disconnected hsep]
  have := h.complement_union_zeroSlice
  rw [h.complement_eq_negativeSide_union_positiveSide] at this
  convert this using 1
  ext x
  simp only [_root_.Set.mem_union]
  tauto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_negativeSide_union_closure_positiveSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_negativeSide_union_closure_positiveSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_negativeSide_union_closure_positiveSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_negativeSide_union_closure_positiveSide

def negativeHalfCollar (q : S × Set.Iic (0 : ℝ)) : closure h.negativeSide :=
  ⟨h.toFun (q.1, q.2), (h.toFun_mem_closure_negativeSide_iff hsep q.1 q.2).mpr q.2.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeHalfCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeHalfCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeHalfCollar ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeHalfCollar


@[simp]
theorem negativeHalfCollar_coe (q : S × Set.Iic (0 : ℝ)) :
    (h.negativeHalfCollar hsep q : X) = h.toFun (q.1, q.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeHalfCollar_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeHalfCollar_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeHalfCollar_coe ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeHalfCollar_coe

theorem range_negativeHalfCollar :
    Set.range (h.negativeHalfCollar hsep) =
      Subtype.val ⁻¹' h.range := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨(q.1, q.2), rfl⟩
  · rintro ⟨p, hp⟩
    have ht : p.2 ≤ 0 := (h.toFun_mem_closure_negativeSide_iff hsep p.1 p.2).mp
      (hp.symm ▸ x.2)
    exact ⟨(p.1, ⟨p.2, ht⟩), Subtype.ext hp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_negativeHalfCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_negativeHalfCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_negativeHalfCollar ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_negativeHalfCollar


theorem isOpenEmbedding_negativeHalfCollar :
    Topology.IsOpenEmbedding (h.negativeHalfCollar hsep) := by
  have hi : Topology.IsEmbedding (fun q : S × Set.Iic (0 : ℝ) ↦
      h.toFun (q.1, q.2)) :=
    h.isOpenEmbedding_toFun.isEmbedding.comp
      (Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal)
  refine ⟨hi.codRestrict _ _, ?_⟩
  rw [h.range_negativeHalfCollar hsep]
  exact h.isOpen_range.preimage continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpenEmbedding_negativeHalfCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpenEmbedding_negativeHalfCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpenEmbedding_negativeHalfCollar ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpenEmbedding_negativeHalfCollar

noncomputable def negativeHalfCollarHomeomorph :
    S × Set.Iic (0 : ℝ) ≃ₜ Set.range (h.negativeHalfCollar hsep) :=
  (h.isOpenEmbedding_negativeHalfCollar hsep).isEmbedding.toHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeHalfCollarHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeHalfCollarHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeHalfCollarHomeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeHalfCollarHomeomorph


theorem negativeHalfCollar_zero (s : S) :
    (h.negativeHalfCollar hsep (s, ⟨0, by simp⟩) : X) = e s := h.zero_eq s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeHalfCollar_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeHalfCollar_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeHalfCollar_zero ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeHalfCollar_zero

def positiveHalfCollar (q : S × Set.Ici (0 : ℝ)) : closure h.positiveSide :=
  ⟨h.toFun (q.1, q.2), (h.toFun_mem_closure_positiveSide_iff hsep q.1 q.2).mpr q.2.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveHalfCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveHalfCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveHalfCollar ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveHalfCollar


@[simp]
theorem positiveHalfCollar_coe (q : S × Set.Ici (0 : ℝ)) :
    (h.positiveHalfCollar hsep q : X) = h.toFun (q.1, q.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveHalfCollar_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveHalfCollar_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveHalfCollar_coe ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveHalfCollar_coe

theorem range_positiveHalfCollar :
    Set.range (h.positiveHalfCollar hsep) =
      Subtype.val ⁻¹' h.range := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨(q.1, q.2), rfl⟩
  · rintro ⟨p, hp⟩
    have ht : 0 ≤ p.2 := (h.toFun_mem_closure_positiveSide_iff hsep p.1 p.2).mp
      (hp.symm ▸ x.2)
    exact ⟨(p.1, ⟨p.2, ht⟩), Subtype.ext hp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_positiveHalfCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_positiveHalfCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_positiveHalfCollar ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_positiveHalfCollar


theorem isOpenEmbedding_positiveHalfCollar :
    Topology.IsOpenEmbedding (h.positiveHalfCollar hsep) := by
  have hi : Topology.IsEmbedding (fun q : S × Set.Ici (0 : ℝ) ↦
      h.toFun (q.1, q.2)) :=
    h.isOpenEmbedding_toFun.isEmbedding.comp
      (Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal)
  refine ⟨hi.codRestrict _ _, ?_⟩
  rw [h.range_positiveHalfCollar hsep]
  exact h.isOpen_range.preimage continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpenEmbedding_positiveHalfCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpenEmbedding_positiveHalfCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpenEmbedding_positiveHalfCollar ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpenEmbedding_positiveHalfCollar

noncomputable def positiveHalfCollarHomeomorph :
    S × Set.Ici (0 : ℝ) ≃ₜ Set.range (h.positiveHalfCollar hsep) :=
  (h.isOpenEmbedding_positiveHalfCollar hsep).isEmbedding.toHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveHalfCollarHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveHalfCollarHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveHalfCollarHomeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveHalfCollarHomeomorph


theorem positiveHalfCollar_zero (s : S) :
    (h.positiveHalfCollar hsep (s, ⟨0, by simp⟩) : X) = e s := h.zero_eq s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveHalfCollar_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveHalfCollar_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveHalfCollar_zero ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveHalfCollar_zero


theorem interior_closure_negativeSide :
    interior (closure h.negativeSide) = h.negativeSide := by
  rw [interior_eq_compl_closure_compl, h.closure_negativeSide_of_disconnected hsep,
    h.compl_negativeSide_union_zeroSlice_of_disconnected hsep,
    h.closure_positiveSide_of_disconnected hsep,
    h.compl_positiveSide_union_zeroSlice_of_disconnected hsep]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.interior_closure_negativeSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.interior_closure_negativeSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.interior_closure_negativeSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.interior_closure_negativeSide


theorem interior_closure_positiveSide :
    interior (closure h.positiveSide) = h.positiveSide := by
  rw [interior_eq_compl_closure_compl, h.closure_positiveSide_of_disconnected hsep,
    h.compl_positiveSide_union_zeroSlice_of_disconnected hsep,
    h.closure_negativeSide_of_disconnected hsep,
    h.compl_negativeSide_union_zeroSlice_of_disconnected hsep]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.interior_closure_positiveSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.interior_closure_positiveSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.interior_closure_positiveSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.interior_closure_positiveSide


theorem frontier_closure_negativeSide :
    frontier (closure h.negativeSide) = Set.range e := by
  rw [frontier, closure_closure, h.interior_closure_negativeSide hsep]
  rw [← h.isOpen_negativeSide.frontier_eq]
  exact h.frontier_negativeSide_of_disconnected hsep

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_closure_negativeSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_closure_negativeSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_closure_negativeSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_closure_negativeSide


theorem frontier_closure_positiveSide :
    frontier (closure h.positiveSide) = Set.range e := by
  rw [frontier, closure_closure, h.interior_closure_positiveSide hsep]
  rw [← h.isOpen_positiveSide.frontier_eq]
  exact h.frontier_positiveSide_of_disconnected hsep

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_closure_positiveSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_closure_positiveSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_closure_positiveSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_closure_positiveSide

noncomputable def negativeFrontierHomeomorph :
    S ≃ₜ frontier (closure h.negativeSide) :=
  (h.continuous_e.isClosedEmbedding h.injective_e).isEmbedding.toHomeomorph |>.trans
    (Homeomorph.setCongr (h.frontier_closure_negativeSide hsep).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeFrontierHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeFrontierHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeFrontierHomeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeFrontierHomeomorph


@[simp]
theorem negativeFrontierHomeomorph_coe (s : S) :
    (h.negativeFrontierHomeomorph hsep s : X) = e s := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeFrontierHomeomorph_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeFrontierHomeomorph_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeFrontierHomeomorph_coe ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeFrontierHomeomorph_coe

noncomputable def positiveFrontierHomeomorph :
    S ≃ₜ frontier (closure h.positiveSide) :=
  (h.continuous_e.isClosedEmbedding h.injective_e).isEmbedding.toHomeomorph |>.trans
    (Homeomorph.setCongr (h.frontier_closure_positiveSide hsep).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveFrontierHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveFrontierHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveFrontierHomeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveFrontierHomeomorph


@[simp]
theorem positiveFrontierHomeomorph_coe (s : S) :
    (h.positiveFrontierHomeomorph hsep s : X) = e s := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveFrontierHomeomorph_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveFrontierHomeomorph_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveFrontierHomeomorph_coe ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveFrontierHomeomorph_coe

end Separated


theorem isCompact_closure_negativeSide [Nonempty S] [CompactSpace X] :
    IsCompact (closure h.negativeSide) := isClosed_closure.isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isCompact_closure_negativeSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isCompact_closure_negativeSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isCompact_closure_negativeSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isCompact_closure_negativeSide


theorem isCompact_closure_positiveSide [Nonempty S] [CompactSpace X] :
    IsCompact (closure h.positiveSide) := isClosed_closure.isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isCompact_closure_positiveSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isCompact_closure_positiveSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isCompact_closure_positiveSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isCompact_closure_positiveSide

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
