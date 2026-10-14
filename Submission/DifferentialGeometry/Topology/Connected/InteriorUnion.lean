import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Submission.DifferentialGeometry.Topology.Connected.ComponentIn
import Submission.DifferentialGeometry.Topology.OpenPartialHomeomorph.Images
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Instances.Real.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology

theorem isConnected_interior_union {X : Type*} [TopologicalSpace X] {S T : Set X}
    (hS : S ⊆ closure (interior S)) (hT : T ⊆ closure (interior T))
    (hconnS : IsPreconnected (interior S)) (hconnT : IsPreconnected (interior T))
    (hmeet : (closure (interior S) ∩ closure (interior T) ∩ interior (S ∪ T)).Nonempty) :
    IsConnected (interior (S ∪ T)) := by
  obtain ⟨p, ⟨hpS, hpT⟩, hp⟩ := hmeet
  have hSp : IsPreconnected (_root_.Insert.insert p (interior S)) :=
    hconnS.subset_closure (_root_.Set.subset_insert p _) (_root_.Set.insert_subset hpS subset_closure)
  have hTp : IsPreconnected (_root_.Insert.insert p (interior T)) :=
    hconnT.subset_closure (_root_.Set.subset_insert p _) (_root_.Set.insert_subset hpT subset_closure)
  have hconn : IsPreconnected (_root_.Insert.insert p (interior S) ∪ _root_.Insert.insert p (interior T)) :=
    hSp.union p (_root_.Set.mem_insert p _) (_root_.Set.mem_insert p _) hTp
  refine ⟨⟨p, hp⟩, hconn.subset_closure ?_ ?_⟩
  · apply _root_.Set.union_subset
    · exact _root_.Set.insert_subset hp (interior_mono _root_.Set.subset_union_left)
    · exact _root_.Set.insert_subset hp (interior_mono _root_.Set.subset_union_right)
  · apply interior_subset.trans
    apply _root_.Set.union_subset
    · exact hS.trans (closure_mono ((_root_.Set.subset_insert p _).trans _root_.Set.subset_union_left))
    · exact hT.trans (closure_mono ((_root_.Set.subset_insert p _).trans _root_.Set.subset_union_right))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isConnected_interior_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isConnected_interior_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isConnected_interior_union ``Submission.DifferentialGeometry.Topology.isConnected_interior_union

section

variable {N M : Type*} [TopologicalSpace N] [ConnectedSpace N]
  [TopologicalSpace M]

private theorem collar_interior_attachment
    (A : OpenPartialHomeomorph (N × ℝ) M) {a b : ℝ} (hab : a < b)
    (hsource : _root_.Set.univ ×ˢ _root_.Set.Icc a b ⊆ A.source) {W : Set M}
    (hW : W ⊆ closure (interior W))
    (hfill : A '' (_root_.Set.univ ×ˢ ({a} : Set ℝ)) ⊆
      interior (W ∪ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b))) :
    (A '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b) ⊆ closure (interior (A '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b)))) ∧
      IsPreconnected (interior (A '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b))) ∧
      (closure (interior W) ∩ closure (interior (A '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b))) ∩
        interior (W ∪ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b))).Nonempty := by
  let B := A '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b)
  have hBint : interior B = A '' (_root_.Set.univ ×ˢ _root_.Set.Ioo a b) := by
    rw [← A.image_interior_of_subset_source hsource, interior_prod_eq,
      interior_univ, interior_Icc]
  have hBreg : B ⊆ closure (interior B) := by
    have hclosure : closure (_root_.Set.univ ×ˢ _root_.Set.Ioo a b : Set (N × ℝ)) = _root_.Set.univ ×ˢ _root_.Set.Icc a b := by
      rw [closure_prod_eq, closure_univ, closure_Ioo hab.ne]
    have hc : ContinuousOn A (closure (_root_.Set.univ ×ˢ _root_.Set.Ioo a b)) := by
      rw [hclosure]
      exact A.continuousOn.mono hsource
    simpa only [hclosure, ← hBint] using hc.image_closure
  have hBconn : IsPreconnected (interior B) := by
    rw [hBint]
    exact (isPreconnected_univ.prod isPreconnected_Ioo).image _
      (A.continuousOn.mono ((_root_.Set.prod_mono Subset.rfl _root_.Set.Ioo_subset_Icc_self).trans hsource))
  obtain ⟨q⟩ := (inferInstance : Nonempty N)
  have hp : A (q, a) ∈ A '' (_root_.Set.univ ×ˢ ({a} : Set ℝ)) :=
    ⟨(q, a), ⟨mem_univ _, rfl⟩, rfl⟩
  let p := A (q, a)
  have hpnotint : p ∉ interior B := by
    rw [hBint]
    rintro ⟨⟨r, t⟩, ⟨_, ht⟩, he⟩
    have hqa := hsource (show (q, a) ∈ _root_.Set.univ ×ˢ _root_.Set.Icc a b from ⟨mem_univ _, le_rfl, hab.le⟩)
    have hrt := hsource (show (r, t) ∈ _root_.Set.univ ×ˢ _root_.Set.Icc a b from
      ⟨mem_univ _, ht.1.le, ht.2.le⟩)
    have hta : t = a := congrArg Prod.snd (A.injOn hrt hqa he)
    exact ht.1.ne hta.symm
  have hpS : p ∈ closure (interior W) := by
    have hpclosure : p ∈ closure W := by
      by_contra hpW
      exact hpnotint (interior_union_inter_interior_compl_left_subset
        ⟨hfill hp, (show p ∈ interior Wᶜ by simpa only [interior_compl, _root_.Set.mem_compl_iff] using hpW)⟩)
    simpa only [closure_closure] using closure_mono hW hpclosure
  have hpT : p ∈ B := by
    rcases hp with ⟨q, hq, hqp⟩
    exact ⟨q, (_root_.Set.prod_mono Subset.rfl (by
      intro t ht
      have ht' : t = a := ht
      subst ht'
      exact ⟨le_rfl, hab.le⟩)) hq, hqp⟩
  exact ⟨hBreg, hBconn, ⟨p, ⟨hpS, hBreg hpT⟩, hfill hp⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.collar_interior_attachment
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.collar_interior_attachment target :: scope.openDecls } }

theorem isConnected_interior_union_of_collar
    (A : OpenPartialHomeomorph (N × ℝ) M) {a b : ℝ} (hab : a < b)
    (hsource : _root_.Set.univ ×ˢ _root_.Set.Icc a b ⊆ A.source) {W : Set M}
    (hW : W ⊆ closure (interior W))
    (hWconn : IsPreconnected (interior W))
    (hfill : A '' (_root_.Set.univ ×ˢ ({a} : Set ℝ)) ⊆
      interior (W ∪ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b))) :
    IsConnected (interior (W ∪ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b))) := by
  obtain ⟨hBreg, hBconn, hmeet⟩ := collar_interior_attachment A hab hsource hW hfill
  exact isConnected_interior_union hW hBreg hWconn hBconn hmeet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isConnected_interior_union_of_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isConnected_interior_union_of_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isConnected_interior_union_of_collar ``Submission.DifferentialGeometry.Topology.isConnected_interior_union_of_collar

end

section

variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X] {W K : Set X}

theorem connectedComponentIn_interior_union_inter_interior_nonempty
    (hW : W ⊆ closure (interior W)) (hK : IsClosed K) (hKconn : IsPreconnected K)
    (hfill : K ⊆ interior (W ∪ K)) (hmeet : (K ∩ W).Nonempty)
    {x : X} (hx : x ∈ interior (W ∪ K)) :
    (connectedComponentIn (interior (W ∪ K)) x ∩ interior W).Nonempty := by
  by_cases hxK : x ∈ K
  · have hKC : K ⊆ connectedComponentIn (interior (W ∪ K)) x :=
      hKconn.subset_connectedComponentIn hxK hfill
    obtain ⟨y, hyK, hyW⟩ := hmeet
    exact mem_closure_iff.mp (hW hyW)
      (connectedComponentIn (interior (W ∪ K)) x)
      isOpen_interior.connectedComponentIn (hKC hyK)
  · have hsub : interior (W ∪ K) ∩ Kᶜ ⊆ W := by
      intro y hy
      exact (interior_subset hy.1).resolve_right hy.2
    exact ⟨x, mem_connectedComponentIn hx,
      interior_maximal hsub (isOpen_interior.inter hK.isOpen_compl) ⟨hx, hxK⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedComponentIn_interior_union_inter_interior_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedComponentIn_interior_union_inter_interior_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedComponentIn_interior_union_inter_interior_nonempty ``Submission.DifferentialGeometry.Topology.connectedComponentIn_interior_union_inter_interior_nonempty

theorem exists_mem_connectedComponentIn_interior_union
    (hW : W ⊆ closure (interior W)) (hK : IsClosed K) (hKconn : IsPreconnected K)
    (hfill : K ⊆ interior (W ∪ K)) (hmeet : (K ∩ W).Nonempty)
    {P : X → Prop}
    (hP : ∀ x ∈ interior W, ∃ a ∈ connectedComponentIn (interior W) x, P a)
    {x : X} (hx : x ∈ interior (W ∪ K)) :
    ∃ a ∈ connectedComponentIn (interior (W ∪ K)) x, P a := by
  obtain ⟨y, hyC, hyW⟩ := connectedComponentIn_interior_union_inter_interior_nonempty
    hW hK hKconn hfill hmeet hx
  obtain ⟨a, haC, haP⟩ := hP y hyW
  refine ⟨a, ?_, haP⟩
  rw [connectedComponentIn_eq hyC]
  exact connectedComponentIn_mono y (interior_mono _root_.Set.subset_union_left) haC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_mem_connectedComponentIn_interior_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_mem_connectedComponentIn_interior_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_mem_connectedComponentIn_interior_union ``Submission.DifferentialGeometry.Topology.exists_mem_connectedComponentIn_interior_union

end

section

variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]

theorem connectedComponentIn_interior_union_inter_interior_nonempty_of_preconnected_interior
    {W K : Set X} (hW : W ⊆ closure (interior W)) (hK : K ⊆ closure (interior K))
    (hKconn : IsPreconnected (interior K))
    (hmeet : (closure (interior W) ∩ closure (interior K) ∩ interior (W ∪ K)).Nonempty)
    {x : X} (hx : x ∈ interior (W ∪ K)) :
    (connectedComponentIn (interior (W ∪ K)) x ∩ interior W).Nonempty := by
  let C := connectedComponentIn (interior (W ∪ K)) x
  have hCopen : IsOpen C := isOpen_interior.connectedComponentIn
  rcases interior_subset hx with hxW | hxK
  · exact mem_closure_iff.mp (hW hxW) C hCopen (mem_connectedComponentIn hx)
  · obtain ⟨y, hyC, hyK⟩ :=
      mem_closure_iff.mp (hK hxK) C hCopen (mem_connectedComponentIn hx)
    have hKC : interior K ⊆ C := by
      change interior K ⊆ connectedComponentIn (interior (W ∪ K)) x
      rw [connectedComponentIn_eq hyC]
      exact hKconn.subset_connectedComponentIn hyK (interior_mono _root_.Set.subset_union_right)
    obtain ⟨p, ⟨hpW, hpK⟩, hp⟩ := hmeet
    have hpC : p ∈ C := by
      change p ∈ connectedComponentIn (interior (W ∪ K)) x
      rw [← closure_connectedComponentIn_inter (interior (W ∪ K)) x]
      exact ⟨closure_mono hKC hpK, hp⟩
    exact mem_closure_iff.mp hpW C hCopen hpC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedComponentIn_interior_union_inter_interior_nonempty_of_preconnected_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedComponentIn_interior_union_inter_interior_nonempty_of_preconnected_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedComponentIn_interior_union_inter_interior_nonempty_of_preconnected_interior ``Submission.DifferentialGeometry.Topology.connectedComponentIn_interior_union_inter_interior_nonempty_of_preconnected_interior

theorem exists_mem_connectedComponentIn_interior_union_of_preconnected_interior
    {W K : Set X} (hW : W ⊆ closure (interior W)) (hK : K ⊆ closure (interior K))
    (hKconn : IsPreconnected (interior K))
    (hmeet : (closure (interior W) ∩ closure (interior K) ∩ interior (W ∪ K)).Nonempty)
    {P : X → Prop}
    (hP : ∀ x ∈ interior W, ∃ a ∈ connectedComponentIn (interior W) x, P a)
    {x : X} (hx : x ∈ interior (W ∪ K)) :
    ∃ a ∈ connectedComponentIn (interior (W ∪ K)) x, P a := by
  obtain ⟨y, hyC, hyW⟩ :=
    connectedComponentIn_interior_union_inter_interior_nonempty_of_preconnected_interior
      hW hK hKconn hmeet hx
  obtain ⟨a, ha, hPa⟩ := hP y hyW
  refine ⟨a, ?_, hPa⟩
  rw [connectedComponentIn_eq hyC]
  exact connectedComponentIn_mono y (interior_mono _root_.Set.subset_union_left) ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_mem_connectedComponentIn_interior_union_of_preconnected_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_mem_connectedComponentIn_interior_union_of_preconnected_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_mem_connectedComponentIn_interior_union_of_preconnected_interior ``Submission.DifferentialGeometry.Topology.exists_mem_connectedComponentIn_interior_union_of_preconnected_interior

end

section

variable {N M : Type*} [TopologicalSpace N] [PreconnectedSpace N]
  [TopologicalSpace M] [LocallyConnectedSpace M]

theorem connectedComponentIn_interior_union_collar_inter_interior_nonempty
    (A : OpenPartialHomeomorph (N × ℝ) M) {a b : ℝ} (hab : a < b)
    (hsource : _root_.Set.univ ×ˢ _root_.Set.Icc a b ⊆ A.source) {W : Set M}
    (hW : W ⊆ closure (interior W))
    (hfill : A '' (_root_.Set.univ ×ˢ ({a} : Set ℝ)) ⊆
      interior (W ∪ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b)))
    {x : M} (hx : x ∈ interior (W ∪ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b))) :
    (connectedComponentIn (interior (W ∪ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b))) x ∩ interior W).Nonempty := by
  rcases isEmpty_or_nonempty N with hN | hN
  · let _ : IsEmpty N := hN
    have hempty : A '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b) = ∅ := by
      rw [Set.eq_empty_of_isEmpty (_root_.Set.univ : Set N), _root_.Set.empty_prod, _root_.Set.image_empty]
    simp only [hempty, _root_.Set.union_empty] at hx ⊢
    exact ⟨x, mem_connectedComponentIn hx, hx⟩
  · let _ : Nonempty N := hN
    let _ : ConnectedSpace N := ⟨hN⟩
    obtain ⟨hBreg, hBconn, hmeet⟩ := collar_interior_attachment A hab hsource hW hfill
    exact connectedComponentIn_interior_union_inter_interior_nonempty_of_preconnected_interior
      hW hBreg hBconn hmeet hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedComponentIn_interior_union_collar_inter_interior_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedComponentIn_interior_union_collar_inter_interior_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedComponentIn_interior_union_collar_inter_interior_nonempty ``Submission.DifferentialGeometry.Topology.connectedComponentIn_interior_union_collar_inter_interior_nonempty

theorem exists_mem_connectedComponentIn_interior_union_collar
    (A : OpenPartialHomeomorph (N × ℝ) M) {a b : ℝ} (hab : a < b)
    (hsource : _root_.Set.univ ×ˢ _root_.Set.Icc a b ⊆ A.source) {W : Set M}
    (hW : W ⊆ closure (interior W))
    (hfill : A '' (_root_.Set.univ ×ˢ ({a} : Set ℝ)) ⊆
      interior (W ∪ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b)))
    {P : M → Prop}
    (hP : ∀ x ∈ interior W, ∃ z ∈ connectedComponentIn (interior W) x, P z)
    {x : M} (hx : x ∈ interior (W ∪ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b))) :
    ∃ z ∈ connectedComponentIn (interior (W ∪ A '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b))) x, P z := by
  obtain ⟨y, hyC, hyW⟩ := connectedComponentIn_interior_union_collar_inter_interior_nonempty
    A hab hsource hW hfill hx
  obtain ⟨z, hz, hPz⟩ := hP y hyW
  refine ⟨z, ?_, hPz⟩
  rw [connectedComponentIn_eq hyC]
  exact connectedComponentIn_mono y (interior_mono _root_.Set.subset_union_left) hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_mem_connectedComponentIn_interior_union_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_mem_connectedComponentIn_interior_union_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_mem_connectedComponentIn_interior_union_collar ``Submission.DifferentialGeometry.Topology.exists_mem_connectedComponentIn_interior_union_collar

end

variable {X : Type*} [TopologicalSpace X]

theorem interior_subset_connectedComponentIn_interior_union_of_incident_component
    {W B : Set X} {a : X} (hB : IsPreconnected (interior B))
    (hmeet : (closure (connectedComponentIn (interior W) a) ∩
      closure (interior B) ∩ interior (W ∪ B)).Nonempty) :
    interior B ⊆ connectedComponentIn (interior (W ∪ B)) a := by
  obtain ⟨p, ⟨hpW, hpB⟩, hpV⟩ := hmeet
  have hpC : p ∈ connectedComponentIn (interior (W ∪ B)) a := by
    rw [← closure_connectedComponentIn_inter (interior (W ∪ B)) a]
    exact ⟨closure_mono (connectedComponentIn_mono a (interior_mono _root_.Set.subset_union_left)) hpW, hpV⟩
  have hconn : IsPreconnected (_root_.Insert.insert p (interior B)) :=
    hB.subset_closure (_root_.Set.subset_insert p _) (_root_.Set.insert_subset hpB subset_closure)
  have hsub : _root_.Insert.insert p (interior B) ⊆ interior (W ∪ B) :=
    _root_.Set.insert_subset hpV (interior_mono _root_.Set.subset_union_right)
  rw [connectedComponentIn_eq hpC]
  exact (_root_.Set.subset_insert p _).trans (hconn.subset_connectedComponentIn (_root_.Set.mem_insert p _) hsub)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.interior_subset_connectedComponentIn_interior_union_of_incident_component then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.interior_subset_connectedComponentIn_interior_union_of_incident_component"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.interior_subset_connectedComponentIn_interior_union_of_incident_component ``Submission.DifferentialGeometry.Topology.interior_subset_connectedComponentIn_interior_union_of_incident_component

theorem subset_closure_connectedComponentIn_interior_union_of_incident_component
    {W B : Set X} {a : X} (hB : B ⊆ closure (interior B))
    (hBconn : IsPreconnected (interior B))
    (hmeet : (closure (connectedComponentIn (interior W) a) ∩
      closure (interior B) ∩ interior (W ∪ B)).Nonempty) :
    B ⊆ closure (connectedComponentIn (interior (W ∪ B)) a) :=
  hB.trans (closure_mono
    (interior_subset_connectedComponentIn_interior_union_of_incident_component hBconn hmeet))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subset_closure_connectedComponentIn_interior_union_of_incident_component then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subset_closure_connectedComponentIn_interior_union_of_incident_component"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subset_closure_connectedComponentIn_interior_union_of_incident_component ``Submission.DifferentialGeometry.Topology.subset_closure_connectedComponentIn_interior_union_of_incident_component

theorem connectedComponentIn_interior_union_eq_of_incident_components
    {W B : Set X} {a b : X} (hB : IsPreconnected (interior B))
    (ha : (closure (connectedComponentIn (interior W) a) ∩
      closure (interior B) ∩ interior (W ∪ B)).Nonempty)
    (hb : (closure (connectedComponentIn (interior W) b) ∩
      closure (interior B) ∩ interior (W ∪ B)).Nonempty) :
    connectedComponentIn (interior (W ∪ B)) a =
      connectedComponentIn (interior (W ∪ B)) b := by
  have hne : (interior B).Nonempty :=
    closure_nonempty_iff.mp ⟨ha.choose, ha.choose_spec.1.2⟩
  obtain ⟨z, hz⟩ := hne
  exact (connectedComponentIn_eq
    (interior_subset_connectedComponentIn_interior_union_of_incident_component hB ha hz)).trans
      (connectedComponentIn_eq
        (interior_subset_connectedComponentIn_interior_union_of_incident_component hB hb hz)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedComponentIn_interior_union_eq_of_incident_components then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedComponentIn_interior_union_eq_of_incident_components"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedComponentIn_interior_union_eq_of_incident_components ``Submission.DifferentialGeometry.Topology.connectedComponentIn_interior_union_eq_of_incident_components

end DifferentialGeometry.Topology
