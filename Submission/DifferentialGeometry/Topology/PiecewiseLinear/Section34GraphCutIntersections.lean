/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCutFamily
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCellBoundaries
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34ResidualFaceRestriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

theorem section34GraphSplitCell_subset_vertex_of_subset
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦') (hwe : w.1 ⊆ e.1) :
    section34GraphSplitCell 𝒦 𝒦' e ⊆ section34GraphVertexCell 𝒦 𝒦' w := by
  classical
  obtain ⟨a, b, -, hab, heq⟩ := exists_section34GraphSplitCell_endpoints hsub hmap e
  obtain ⟨p, hp⟩ := 𝒦'.complex.nonempty_of_mem_faces w.2.1
  have hpe : p ∈ (e.1 : Set Ea) := hwe hp
  rw [hab] at hpe
  have hequal (z : Section34VertexIndex 𝒦 𝒦') (hpz : p ∈ z.1) : w = z := by
    apply Subtype.ext
    have hw : ({p} : Finset Ea) = w.1 := Finset.eq_of_subset_of_card_le
      (Finset.singleton_subset_iff.mpr hp) (by simp [w.2.2.1])
    have hz : ({p} : Finset Ea) = z.1 := Finset.eq_of_subset_of_card_le
      (Finset.singleton_subset_iff.mpr hpz) (by simp [z.2.2.1])
    exact hw.symm.trans hz
  rcases hpe with hpa | hpb
  · rw [hequal a hpa, heq]
    exact _root_.Set.inter_subset_left
  · rw [hequal b hpb, heq]
    exact _root_.Set.inter_subset_right

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34GraphSplitCell_subset_vertex_of_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34GraphSplitCell_subset_vertex_of_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34GraphSplitCell_subset_vertex_of_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34GraphSplitCell_subset_vertex_of_subset

private noncomputable def graphFactor (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U) :
    Option (Section34VertexIndex 𝒦 𝒦' ⊕ Section34EdgeIndex 𝒦 𝒦') → Set M
  | none => _root_.Set.univ
  | some (.inl w) => section34GraphVertexCell 𝒦 𝒦' w
  | some (.inr e) => section34GraphSplitCell 𝒦 𝒦' e

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.graphFactor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.graphFactor target :: scope.openDecls } }

private theorem graphFactor_inter
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (a b : Option (Section34VertexIndex 𝒦 𝒦' ⊕ Section34EdgeIndex 𝒦 𝒦'))
    (hne : (graphFactor 𝒦 𝒦' a ∩ graphFactor 𝒦 𝒦' b).Nonempty) :
    ∃ c, graphFactor 𝒦 𝒦' a ∩ graphFactor 𝒦 𝒦' b = graphFactor 𝒦 𝒦' c ∧
      (c = _root_.Option.none → a = _root_.Option.none ∧ b = _root_.Option.none) := by
  classical
  cases a with
  | none => exact ⟨b, _root_.Set.univ_inter _, fun h => ⟨rfl, h⟩⟩
  | some a =>
    cases b with
    | none => exact ⟨some a, _root_.Set.inter_univ _, fun h => (Option.some_ne_none _ h).elim⟩
    | some b =>
      cases a with
      | inl w =>
        cases b with
        | inl z =>
          by_cases hwz : w = z
          · subst z
            exact ⟨some (.inl w), _root_.Set.inter_self _, fun h => (Option.some_ne_none _ h).elim⟩
          · obtain ⟨e, -, he⟩ :=
              exists_section34GraphSplitCell_of_vertex_inter_nonempty hsub hmap w z hwz hne
            exact ⟨some (.inr e), he.symm, fun h => (Option.some_ne_none _ h).elim⟩
        | inr e =>
          have hwe := vertex_subset_edge_of_section34GraphVertexCell_inter_splitCell_nonempty
            hsub hmap w e hne
          exact ⟨some (.inr e), inter_eq_right.mpr
            (section34GraphSplitCell_subset_vertex_of_subset hsub hmap w e hwe),
            fun h => (Option.some_ne_none _ h).elim⟩
      | inr e =>
        cases b with
        | inl w =>
          have hwe := vertex_subset_edge_of_section34GraphVertexCell_inter_splitCell_nonempty
            hsub hmap w e (_root_.Set.inter_comm _ _ ▸ hne)
          exact ⟨some (.inr e), inter_eq_left.mpr
            (section34GraphSplitCell_subset_vertex_of_subset hsub hmap w e hwe),
            fun h => (Option.some_ne_none _ h).elim⟩
        | inr f =>
          by_cases hef : e = f
          · subst f
            exact ⟨some (.inr e), _root_.Set.inter_self _, fun h => (Option.some_ne_none _ h).elim⟩
          · exact (hne.ne_empty
              (disjoint_iff_inter_eq_empty.mp (pairwise_disjoint_section34GraphSplitCell
                𝒦 𝒦' hef))).elim

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.graphFactor_inter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.graphFactor_inter target :: scope.openDecls } }

private def residualSimplex : Section34SimplexIndex 𝒦 3 ⊕ Section34SimplexIndex 𝒦 4 →
    Finset Ea
  | .inl s => s.1
  | .inr t => t.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.residualSimplex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.residualSimplex target :: scope.openDecls } }

private theorem residualSimplex_mem (r : Section34SimplexIndex 𝒦 3 ⊕
    Section34SimplexIndex 𝒦 4) : residualSimplex r ∈ 𝒦.complex.faces := by
  cases r with
  | inl s => exact s.2.1
  | inr t => exact t.2.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.residualSimplex_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.residualSimplex_mem target :: scope.openDecls } }

private theorem residualSimplex_card_le (r : Section34SimplexIndex 𝒦 3 ⊕
    Section34SimplexIndex 𝒦 4) : (residualSimplex r).card ≤ 4 := by
  cases r with
  | inl s => exact s.2.2.le.trans (by decide)
  | inr t => exact t.2.2.le

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.residualSimplex_card_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.residualSimplex_card_le target :: scope.openDecls } }

private noncomputable def residualFactor (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U) :
    Option (Section34SimplexIndex 𝒦 3 ⊕ Section34SimplexIndex 𝒦 4) → Set M
  | none => _root_.Set.univ
  | some r => section34GraphResidualCell 𝒦 𝒦' (residualSimplex r)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.residualFactor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.residualFactor target :: scope.openDecls } }

variable [T2Space M]

private theorem residualFactor_inter
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (a b : Option (Section34SimplexIndex 𝒦 3 ⊕ Section34SimplexIndex 𝒦 4))
    (hne : (residualFactor 𝒦 𝒦' a ∩ residualFactor 𝒦 𝒦' b).Nonempty) :
    ∃ c, residualFactor 𝒦 𝒦' a ∩ residualFactor 𝒦 𝒦' b = residualFactor 𝒦 𝒦' c ∧
      (c = _root_.Option.none → a = _root_.Option.none ∧ b = _root_.Option.none) := by
  classical
  cases a with
  | none => exact ⟨b, _root_.Set.univ_inter _, fun h => ⟨rfl, h⟩⟩
  | some a =>
    cases b with
    | none => exact ⟨some a, _root_.Set.inter_univ _, fun h => (Option.some_ne_none _ h).elim⟩
    | some b =>
      let t := residualSimplex a ∩ residualSimplex b
      have heq : residualFactor 𝒦 𝒦' (_root_.Option.some a) ∩ residualFactor 𝒦 𝒦' (_root_.Option.some b) =
          section34GraphResidualCell 𝒦 𝒦' t :=
        section34GraphResidualCell_inter hsub hmap (residualSimplex_mem a) (residualSimplex_mem b)
      have htne : t.Nonempty := by
        by_contra ht
        rw [heq, Finset.not_nonempty_iff_eq_empty.mp ht] at hne
        simp [section34GraphResidualCell, simplexBody] at hne
      have ht : t ∈ 𝒦.complex.faces :=
        𝒦.complex.down_closed (residualSimplex_mem a) Finset.inter_subset_left htne
      have hlo : 2 < t.card := by
        by_contra hcard
        rw [heq, section34GraphResidualCell_eq_empty_of_card_le_two hsub hmap ht
          (Nat.le_of_not_gt hcard)] at hne
        exact hne.ne_empty rfl
      have hhi : t.card ≤ 4 :=
        (Finset.card_le_card Finset.inter_subset_left).trans (residualSimplex_card_le a)
      have hcases : t.card = 3 ∨ t.card = 4 := by omega
      rcases hcases with hc | hc
      · exact ⟨some (.inl ⟨t, ht, hc⟩), heq, fun h => (Option.some_ne_none _ h).elim⟩
      · exact ⟨some (.inr ⟨t, ht, hc⟩), heq, fun h => (Option.some_ne_none _ h).elim⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.residualFactor_inter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.residualFactor_inter target :: scope.openDecls } }

private def graphTag : Section34CutLabelOf 𝒦 𝒦' →
    Option (Section34VertexIndex 𝒦 𝒦' ⊕ Section34EdgeIndex 𝒦 𝒦')
  | .vertexBall w => _root_.Option.some (.inl w)
  | .tetraBall _ => _root_.Option.none
  | .splitDisk e => _root_.Option.some (.inr e)
  | .faceDisk _ => _root_.Option.none
  | .patch p => _root_.Option.some (.inl p.1.2)
  | .faceArc a => _root_.Option.some (.inl a.1.2)
  | .edgeArc i => _root_.Option.some (.inr i.1.2)
  | .markedPoint p => _root_.Option.some (.inr p.1.2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.graphTag
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.graphTag target :: scope.openDecls } }

private def residualTag : Section34CutLabelOf 𝒦 𝒦' →
    Option (Section34SimplexIndex 𝒦 3 ⊕ Section34SimplexIndex 𝒦 4)
  | .vertexBall _ => _root_.Option.none
  | .tetraBall t => _root_.Option.some (.inr t)
  | .splitDisk _ => _root_.Option.none
  | .faceDisk s => _root_.Option.some (.inl s)
  | .patch p => _root_.Option.some (.inr p.1.1)
  | .faceArc a => _root_.Option.some (.inl a.1.1)
  | .edgeArc i => _root_.Option.some (.inr i.1.1)
  | .markedPoint p => _root_.Option.some (.inl p.1.1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.residualTag
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.residualTag target :: scope.openDecls } }

omit [T2Space M] in
private theorem cutFamily_eq_factors (l : Section34CutLabelOf 𝒦 𝒦') :
    section34GraphCutFamily 𝒦 𝒦' l =
      graphFactor 𝒦 𝒦' (graphTag l) ∩ residualFactor 𝒦 𝒦' (residualTag l) := by
  cases l <;> simp [section34GraphCutFamily, graphTag, residualTag, graphFactor,
    residualFactor, residualSimplex, _root_.Set.inter_comm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.cutFamily_eq_factors
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.cutFamily_eq_factors target :: scope.openDecls } }

omit [T2Space M] in
private theorem cutFamily_tags_ne_none (l : Section34CutLabelOf 𝒦 𝒦') :
    ¬ (graphTag l = _root_.Option.none ∧ residualTag l = _root_.Option.none) := by
  cases l <;> simp [graphTag, residualTag]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.cutFamily_tags_ne_none
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.cutFamily_tags_ne_none target :: scope.openDecls } }

private theorem exists_cutFamily_of_factors
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (a : Option (Section34VertexIndex 𝒦 𝒦' ⊕ Section34EdgeIndex 𝒦 𝒦'))
    (b : Option (Section34SimplexIndex 𝒦 3 ⊕ Section34SimplexIndex 𝒦 4))
    (hnot : ¬ (a = _root_.Option.none ∧ b = _root_.Option.none))
    (hne : (graphFactor 𝒦 𝒦' a ∩ residualFactor 𝒦 𝒦' b).Nonempty) :
    ∃ l, graphFactor 𝒦 𝒦' a ∩ residualFactor 𝒦 𝒦' b =
      section34GraphCutFamily 𝒦 𝒦' l := by
  cases a with
  | none =>
    cases b with
    | none => exact (hnot ⟨rfl, rfl⟩).elim
    | some b =>
      cases b with
      | inl s => exact ⟨.faceDisk s, _root_.Set.univ_inter _⟩
      | inr t => exact ⟨.tetraBall t, _root_.Set.univ_inter _⟩
  | some a =>
    cases b with
    | none =>
      cases a with
      | inl w => exact ⟨.vertexBall w, _root_.Set.inter_univ _⟩
      | inr e => exact ⟨.splitDisk e, _root_.Set.inter_univ _⟩
    | some b =>
      cases a with
      | inl w =>
        cases b with
        | inl s =>
          have hws := (section34GraphVertexCell_inter_simplexBody_nonempty_iff
            hsub hmap w s.2.1).mp (hne.mono (_root_.Set.inter_subset_inter_right _
              (section34GraphResidualCell_subset_simplexBody s.2.1)))
          exact ⟨.faceArc ⟨(s, w), hws⟩, rfl⟩
        | inr t =>
          have hwt := (section34GraphVertexCell_inter_simplexBody_nonempty_iff
            hsub hmap w t.2.1).mp (hne.mono (_root_.Set.inter_subset_inter_right _
              (section34GraphResidualCell_subset_simplexBody t.2.1)))
          exact ⟨.patch ⟨(t, w), hwt⟩, _root_.Set.inter_comm _ _⟩
      | inr e =>
        cases b with
        | inl s =>
          have hes := (section34GraphSplitCell_inter_simplexBody_nonempty_iff
            hsub hmap e s.2.1).mp (hne.mono (_root_.Set.inter_subset_inter_right _
              (section34GraphResidualCell_subset_simplexBody s.2.1)))
          exact ⟨.markedPoint ⟨(s, e), hes⟩, rfl⟩
        | inr t =>
          have het := (section34GraphSplitCell_inter_simplexBody_nonempty_iff
            hsub hmap e t.2.1).mp (hne.mono (_root_.Set.inter_subset_inter_right _
              (section34GraphResidualCell_subset_simplexBody t.2.1)))
          exact ⟨.edgeArc ⟨(t, e), het⟩, _root_.Set.inter_comm _ _⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_cutFamily_of_factors
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.exists_cutFamily_of_factors target :: scope.openDecls } }

theorem exists_section34GraphCutFamily_inter_eq_of_nonempty
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (l m : Section34CutLabelOf 𝒦 𝒦')
    (hne : (section34GraphCutFamily 𝒦 𝒦' l ∩ section34GraphCutFamily 𝒦 𝒦' m).Nonempty) :
    ∃ k, section34GraphCutFamily 𝒦 𝒦' l ∩ section34GraphCutFamily 𝒦 𝒦' m =
      section34GraphCutFamily 𝒦 𝒦' k := by
  have hne' := hne
  rw [cutFamily_eq_factors l, cutFamily_eq_factors m] at hne'
  obtain ⟨x, hx, hy⟩ := hne'
  obtain ⟨a, ha, haNone⟩ := graphFactor_inter hsub hmap (graphTag l) (graphTag m)
    ⟨x, hx.1, hy.1⟩
  obtain ⟨b, hb, hbNone⟩ := residualFactor_inter hsub hmap (residualTag l) (residualTag m)
    ⟨x, hx.2, hy.2⟩
  have heq : section34GraphCutFamily 𝒦 𝒦' l ∩ section34GraphCutFamily 𝒦 𝒦' m =
      graphFactor 𝒦 𝒦' a ∩ residualFactor 𝒦 𝒦' b := by
    rw [cutFamily_eq_factors l, cutFamily_eq_factors m, ← ha, ← hb]
    ext y
    simp only [_root_.Set.mem_inter_iff]
    tauto
  have hnot : ¬ (a = _root_.Option.none ∧ b = _root_.Option.none) := fun h =>
    cutFamily_tags_ne_none l ⟨(haNone h.1).1, (hbNone h.2).1⟩
  obtain ⟨k, hk⟩ := exists_cutFamily_of_factors hsub hmap a b hnot (heq ▸ hne)
  exact ⟨k, heq.trans hk⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_section34GraphCutFamily_inter_eq_of_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_section34GraphCutFamily_inter_eq_of_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_section34GraphCutFamily_inter_eq_of_nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_section34GraphCutFamily_inter_eq_of_nonempty

theorem section34GraphCutFamily_inter_eq_iUnion_common_faces
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (l m : Section34CutLabelOf 𝒦 𝒦') :
    section34GraphCutFamily 𝒦 𝒦' l ∩ section34GraphCutFamily 𝒦 𝒦' m =
      ⋃ k ∈ section34Face (section34GraphCutFamily 𝒦 𝒦') l ∩
        section34Face (section34GraphCutFamily 𝒦 𝒦') m, section34GraphCutFamily 𝒦 𝒦' k := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨k, hk⟩ := exists_section34GraphCutFamily_inter_eq_of_nonempty hsub hmap l m ⟨x, hx⟩
    exact mem_iUnion₂.mpr ⟨k, ⟨hk.symm.subset.trans _root_.Set.inter_subset_left,
      hk.symm.subset.trans inter_subset_right⟩, hk.subset hx⟩
  · intro x hx
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
    exact ⟨hk.1 hxk, hk.2 hxk⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34GraphCutFamily_inter_eq_iUnion_common_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34GraphCutFamily_inter_eq_iUnion_common_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34GraphCutFamily_inter_eq_iUnion_common_faces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34GraphCutFamily_inter_eq_iUnion_common_faces

end DifferentialGeometry.Topology.PiecewiseLinear
