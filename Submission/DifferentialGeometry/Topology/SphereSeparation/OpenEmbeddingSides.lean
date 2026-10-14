import Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair
import Submission.DifferentialGeometry.Topology.Connected.ComplementSides
import Mathlib.Topology.Separation.Hausdorff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set

namespace DifferentialGeometry.Topology.SphereSeparation

theorem SphereSides.exists_image_openEmbedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    [ConnectedSpace Y] [LocallyConnectedSpace Y] [NoncompactSpace Y]
    {S : Set X} (d : SphereSides S) {f : X → Y} (hf : _root_.Topology.IsOpenEmbedding f) :
    ∃ e : SphereSides (f '' S), e.compactSide = f '' d.compactSide := by
  let B := f '' d.compactSide
  let E := f '' d.endSide
  let T := f '' S
  have hBop : IsOpen B := hf.isOpenMap _ d.isOpen_compactSide
  have hBconn : IsConnected B := d.isConnected_compactSide.image f hf.continuous.continuousOn
  have hEconn : IsConnected E := d.isConnected_endSide.image f hf.continuous.continuousOn
  have hBE : Disjoint B E := by
    dsimp [B,E]
    exact Set.disjoint_image_of_injective hf.injective d.disjoint
  have hBcl : closure B = B ∪ T := by
    rw [← image_closure_of_isCompact d.isCompact_closure_compactSide hf.continuous.continuousOn,
      d.closure_compactSide, _root_.Set.image_union]
  have hBc : IsCompact (closure B) := by
    rw [← image_closure_of_isCompact d.isCompact_closure_compactSide hf.continuous.continuousOn]
    exact d.isCompact_closure_compactSide.image hf.continuous
  have hBT : Disjoint B T := by
    dsimp [B,T]
    exact Set.disjoint_image_of_injective hf.injective d.compactSide_disjoint_sphere
  have hTcl : T ⊆ closure B := hBcl.symm ▸ _root_.Set.subset_union_right
  have hTc : IsCompact T := hBc.of_isClosed_subset
    (by
      have hT : T = frontier B := by
        rw [hBop.frontier_eq, hBcl]
        exact (_root_.Set.union_sdiff_cancel_left hBT.le_bot).symm
      rw [hT]
      exact isClosed_frontier) hTcl
  have hTne : T.Nonempty := by
    have hBuniv : B ≠ univ := by
      intro hh
      obtain ⟨x,hx⟩ := hEconn.nonempty
      exact hBE.le_bot ⟨hh ▸ _root_.Set.mem_univ x,hx⟩
    have hh := nonempty_frontier_iff.mpr ⟨hBconn.nonempty,hBuniv⟩
    obtain ⟨x,hx⟩ := hh
    refine ⟨x,?_⟩
    rw [hBop.frontier_eq,hBcl] at hx
    exact hx.1.resolve_left hx.2
  have hlocal : _root_.Set.range f \ T = B ∪ E := by
    rw [← _root_.Set.image_univ, ← _root_.Set.image_sdiff hf.injective]
    have hh : (_root_.Set.univ \ S : Set X) = Sᶜ := by ext x; simp only [_root_.Set.mem_sdiff,_root_.Set.mem_univ,true_and,_root_.Set.mem_compl_iff]
    rw [hh]
    rw [← d.union_eq_compl, _root_.Set.image_union]
  obtain ⟨b,hb⟩ := hBconn.nonempty
  obtain ⟨e,he⟩ := hEconn.nonempty
  obtain ⟨hunion, heq, hBC, hEC⟩ :=
    DifferentialGeometry.Topology.complement_eq_union_components_of_two_local_sides
      hTc.isClosed hTne hf.isOpen_range (_root_.Set.image_subset_range _ _) hlocal
      hBconn.isPreconnected hEconn.isPreconnected hb he
  have hBcom : B = connectedComponentIn Tᶜ b := by
    apply Subset.antisymm hBC
    apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hBop
      ⟨b,mem_connectedComponentIn (show b ∈ Tᶜ from fun h => hBT.le_bot ⟨hb,h⟩),hb⟩
    intro x hx
    rw [hBcl] at hx
    exact hx.1.resolve_right (connectedComponentIn_subset Tᶜ b hx.2)
  have hcompdisj : Disjoint (connectedComponentIn Tᶜ b) (connectedComponentIn Tᶜ e) := by
    rcases heq with heq | hd
    · have heB : e ∈ B := hBcom.symm ▸ (heq.symm ▸ hEC he)
      exact False.elim (hBE.le_bot ⟨heB,he⟩)
    · exact hd
  have heT : e ∈ Tᶜ := connectedComponentIn_subset Tᶜ e (hEC he)
  let p : ComplementPair T := {
    left := B
    right := connectedComponentIn Tᶜ e
    isOpen_left := hBop
    isOpen_right := hTc.isClosed.isOpen_compl.connectedComponentIn
    isConnected_left := hBconn
    isConnected_right := isConnected_connectedComponentIn_iff.mpr heT
    disjoint := hBcom.symm ▸ hcompdisj
    union_eq_compl := hBcom.symm ▸ hunion }
  have hTr : T ⊆ closure p.right := by
    rintro y ⟨x,hx,rfl⟩
    have hxcl : x ∈ closure d.endSide := d.closure_endSide.symm ▸ Or.inr hx
    have hycl : f x ∈ closure E := image_closure_subset_closure_image hf.continuous ⟨x,hxcl,rfl⟩
    exact closure_mono hEC hycl
  have hRnc : ¬ IsCompact (closure p.right) := by
    intro hR
    have hcover : closure B ∪ closure p.right = univ := by
      apply _root_.Set.eq_univ_of_forall
      intro x
      by_cases hx : x ∈ T
      · exact Or.inl (hTcl hx)
      · have hh : x ∈ p.left ∪ p.right := p.union_eq_compl.symm ▸ hx
        exact hh.elim (fun h => Or.inl (subset_closure h))
          (fun h => Or.inr (subset_closure h))
    exact noncompact_univ Y (hcover ▸ hBc.union hR)
  exact ⟨p.toSphereSides hBc hRnc hTcl hTr,rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SphereSides.exists_image_openEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SphereSides.exists_image_openEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SphereSides.exists_image_openEmbedding ``Submission.DifferentialGeometry.Topology.SphereSeparation.SphereSides.exists_image_openEmbedding

end DifferentialGeometry.Topology.SphereSeparation
