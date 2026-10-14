/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCellBoundaries
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphMarkedPoints
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCutFamily
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34ResidualFaceRestriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem IsPLCellOn.not_subset_of_lower_dimension
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {A AB B BB : Set M} {d : ℕ} (hA : IsPLCellOn 3 A AB) (hB : IsPLCellOn d B BB)
    (hd : d < 3) : ¬ A ⊆ B := by
  intro hAB
  have hi : interior A = ∅ := subset_empty_iff.mp
    ((interior_mono hAB).trans (hB.interior_eq_empty_of_lt hd).subset)
  have hAcl : A ⊆ closure (interior A) := hA.subset_closure_interior
  rw [hi, closure_empty] at hAcl
  exact hA.nonempty.ne_empty (subset_empty_iff.mp hAcl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.not_subset_of_lower_dimension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.not_subset_of_lower_dimension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.not_subset_of_lower_dimension ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.not_subset_of_lower_dimension

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

theorem section34GraphVertexCell_subset_iff
    (w z : Section34VertexIndex 𝒦 𝒦') :
    section34GraphVertexCell 𝒦 𝒦' w ⊆ section34GraphVertexCell 𝒦 𝒦' z ↔ w = z := by
  classical
  constructor
  · intro hsub
    let L := restrict 𝒦'.complex (𝒦'.map ⁻¹' graphSkeletonSpace 𝒦)
    let v := w.1.centroid ℝ id
    let u := z.1.centroid ℝ id
    have hv : {v} ∈ L.faces := singleton_centroid_mem_section34GraphCore w
    have hu : {u} ∈ L.faces := singleton_centroid_mem_section34GraphCore z
    have hx := hsub (_root_.Set.mem_image_of_mem 𝒦'.map
      (mem_graphDualCell_space_of_singleton_mem 𝒦'.complex L (restrict_faces_subset _ _) hv))
    obtain ⟨p, hp, hpv⟩ := hx
    have hpK := derivedNeighborhood_space_subset 𝒦'.complex L
      (graphDualCell_space_subset 𝒦'.complex L u hp)
    have hvK : v ∈ 𝒦'.complex.space :=
      𝒦'.complex.convexHull_subset_space hv.1 (by simp)
    have hpv' : p = v := 𝒦'.bijOn.injOn hpK hvK hpv
    have hvu := (mem_graphDualCell_space_iff_of_singleton_mem 𝒦'.complex L
      (restrict_faces_subset _ _) hu hv).mp (hpv' ▸ hp)
    apply Subtype.ext
    rw [section34VertexIndex_eq_singleton_centroid w,
      section34VertexIndex_eq_singleton_centroid z]
    exact congrArg (fun p => ({p} : Finset Ea)) hvu
  · rintro rfl
    exact subset_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34GraphVertexCell_subset_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34GraphVertexCell_subset_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34GraphVertexCell_subset_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34GraphVertexCell_subset_iff

theorem section34GraphSplitCell_subset_iff (e d : Section34EdgeIndex 𝒦 𝒦') :
    section34GraphSplitCell 𝒦 𝒦' e ⊆ section34GraphSplitCell 𝒦 𝒦' d ↔ e = d := by
  classical
  constructor
  · intro hsub
    by_contra hne
    have hp : 𝒦'.map (e.1.centroid ℝ id) ∈ section34GraphSplitCell 𝒦 𝒦' e :=
      _root_.Set.mem_image_of_mem _ (centroid_mem_splittingDisk_space 𝒦'.complex e.2.1)
    exact disjoint_left.mp (pairwise_disjoint_section34GraphSplitCell 𝒦 𝒦' hne) hp (hsub hp)
  · rintro rfl
    exact subset_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34GraphSplitCell_subset_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34GraphSplitCell_subset_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34GraphSplitCell_subset_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34GraphSplitCell_subset_iff

theorem disjoint_section34GraphResidualCell_graphSkeletonSpace
    (hU : IsOpen U) (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (t : Finset Ea) :
    Disjoint (section34GraphResidualCell 𝒦 𝒦' t) (graphSkeletonSpace 𝒦) := by
  let N := ⋃ w : Section34VertexIndex 𝒦 𝒦', section34GraphVertexCell 𝒦 𝒦' w
  have hres : section34GraphResidualCell 𝒦 𝒦' t ⊆ (interior N)ᶜ :=
    closure_minimal (fun x hx hxi => hx.2 (interior_subset hxi)) isOpen_interior.isClosed_compl
  have hΓ : graphSkeletonSpace 𝒦 ⊆ interior N := subset_interior_iff_mem_nhdsSet.mpr
    (iUnion_section34GraphVertexCell_mem_nhdsSet hU hsub hmap)
  exact disjoint_left.mpr fun _ hxR hxΓ => hres hxR (hΓ hxΓ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_section34GraphResidualCell_graphSkeletonSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.disjoint_section34GraphResidualCell_graphSkeletonSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_section34GraphResidualCell_graphSkeletonSpace ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.disjoint_section34GraphResidualCell_graphSkeletonSpace

variable [T2Space M]

theorem section34GraphResidualTriangle_subset_iff [FiniteDimensional ℝ Ea]
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (s t : Section34SimplexIndex 𝒦 3) :
    section34GraphResidualCell 𝒦 𝒦' s.1 ⊆ section34GraphResidualCell 𝒦 𝒦' t.1 ↔ s = t := by
  constructor
  · intro hst
    by_contra hne
    obtain ⟨B, hB⟩ := exists_isPLCellOn_section34GraphResidualTriangle hsub hmap s
    obtain ⟨x, hx⟩ := hB.nonempty
    exact disjoint_left.mp (pairwiseDisjoint_section34GraphResidualTriangle hsub hmap hne)
      hx (hst hx)
  · rintro rfl
    exact subset_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34GraphResidualTriangle_subset_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34GraphResidualTriangle_subset_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34GraphResidualTriangle_subset_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34GraphResidualTriangle_subset_iff

theorem pairwise_disjoint_section34GraphMarkedPoint
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map) :
    Pairwise (Disjoint on fun p : Section34MarkIndex 𝒦 𝒦' =>
      section34GraphCutFamily 𝒦 𝒦' (.markedPoint p)) := by
  intro p q hpq
  apply disjoint_left.mpr
  intro y hyp hyq
  have hs : p.1.1 = q.1.1 := by
    by_contra hs
    exact disjoint_left.mp (pairwiseDisjoint_section34GraphResidualTriangle hsub hmap hs)
      hyp.2 hyq.2
  have he : p.1.2 = q.1.2 := by
    by_contra he
    exact disjoint_left.mp (pairwise_disjoint_section34GraphSplitCell 𝒦 𝒦' he) hyp.1 hyq.1
  exact hpq (Subtype.ext (Prod.ext hs he))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.pairwise_disjoint_section34GraphMarkedPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.pairwise_disjoint_section34GraphMarkedPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.pairwise_disjoint_section34GraphMarkedPoint ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.pairwise_disjoint_section34GraphMarkedPoint

theorem section34GraphMarkedPoint_subset_iff [FiniteDimensional ℝ Ea]
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (p q : Section34MarkIndex 𝒦 𝒦') :
    section34GraphCutFamily 𝒦 𝒦' (.markedPoint p) ⊆
      section34GraphCutFamily 𝒦 𝒦' (.markedPoint q) ↔ p = q := by
  constructor
  · intro hpq
    by_contra hne
    obtain ⟨x, hx⟩ := exists_singleton_section34GraphSplitCell_inter_residualTriangle
      hsub hmap p.1.1 p.1.2 p.2
    have hxp : x ∈ section34GraphCutFamily 𝒦 𝒦' (.markedPoint p) :=
      show x ∈ section34GraphSplitCell 𝒦 𝒦' p.1.2 ∩
        section34GraphResidualCell 𝒦 𝒦' p.1.1.1 from hx.symm ▸ _root_.Set.mem_singleton x
    exact disjoint_left.mp (pairwise_disjoint_section34GraphMarkedPoint hsub hmap hne)
      hxp (hpq hxp)
  · rintro rfl
    exact subset_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34GraphMarkedPoint_subset_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34GraphMarkedPoint_subset_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34GraphMarkedPoint_subset_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34GraphMarkedPoint_subset_iff

theorem section34GraphCutFamily_subset_strict_on_recognized_sources [FiniteDimensional ℝ Ea]
    (hU : IsOpen U) (hsub : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (hK : IsCombinatorialManifold 3 𝒦'.complex) :
    let src := section34GraphCutFamily 𝒦 𝒦'
    (∀ w l, src (.vertexBall w) ⊆ src l →
      (.vertexBall w : Section34CutLabelOf 𝒦 𝒦') = l ∨ 3 < section34Dim l) ∧
    (∀ e l, src (.splitDisk e) ⊆ src l →
      (.splitDisk e : Section34CutLabelOf 𝒦 𝒦') = l ∨ 2 < section34Dim l) ∧
    (∀ s l, src (.faceDisk s) ⊆ src l →
      (.faceDisk s : Section34CutLabelOf 𝒦 𝒦') = l ∨ 2 < section34Dim l) ∧
    ∀ p l, src (.markedPoint p) ⊆ src l →
      (.markedPoint p : Section34CutLabelOf 𝒦 𝒦') = l ∨ 0 < section34Dim l := by
  classical
  let C := section34GraphVertexCell 𝒦 𝒦'
  let E := section34GraphSplitCell 𝒦 𝒦'
  let R := section34GraphResidualCell 𝒦 𝒦'
  let N := ⋃ w, C w
  have hVΓ : ∀ w, (C w ∩ graphSkeletonSpace 𝒦).Nonempty := by
    intro w
    have hp := w.1.centroid_mem_convexHull (R := ℝ)
      (𝒦'.complex.nonempty_of_mem_faces w.2.1)
    have hpb : 𝒦'.map (w.1.centroid ℝ id) ∈ simplexBody 𝒦' w.1 :=
      _root_.Set.mem_image_of_mem _ hp
    exact ⟨_, simplexBody_subset_section34GraphVertexCell w hpb, w.2.2.2 hpb⟩
  have hEΓ : ∀ e, (E e ∩ graphSkeletonSpace 𝒦).Nonempty := by
    intro e
    exact ⟨_, _root_.Set.mem_image_of_mem _ (centroid_mem_splittingDisk_space 𝒦'.complex e.2.1),
      e.2.2.2 (_root_.Set.mem_image_of_mem _ (e.1.centroid_mem_convexHull
        (𝒦'.complex.nonempty_of_mem_faces e.2.1)))⟩
  have hVR : ∀ w t, ¬ C w ⊆ R t := by
    intro w t h
    obtain ⟨x, hxC, hxΓ⟩ := hVΓ w
    exact disjoint_left.mp (disjoint_section34GraphResidualCell_graphSkeletonSpace hU hsub hmap t)
      (h hxC) hxΓ
  have hER : ∀ e t, ¬ E e ⊆ R t := by
    intro e t h
    obtain ⟨x, hxE, hxΓ⟩ := hEΓ e
    exact disjoint_left.mp (disjoint_section34GraphResidualCell_graphSkeletonSpace hU hsub hmap t)
      (h hxE) hxΓ
  have hRN : ∀ s : Section34SimplexIndex 𝒦 3, ¬ R s.1 ⊆ N := by
    intro s h
    obtain ⟨B, hB⟩ := exists_isPLCellOn_section34GraphResidualTriangle hsub hmap s
    obtain ⟨x, hx⟩ := closure_nonempty_iff.mp hB.nonempty
    exact hx.2 (h (subset_closure hx))
  have hEN : ∀ e, E e ⊆ N := by
    intro e
    obtain ⟨w, w', -, -, heq⟩ := exists_section34GraphSplitCell_endpoints hsub hmap e
    exact (heq.subset.trans _root_.Set.inter_subset_left).trans (_root_.Set.subset_iUnion C w)
  have hCV : ∀ w, IsPLCellOn 3 (C w) (section34GraphVertexBoundary 𝒦 𝒦' w) :=
    isPLCellOn_section34GraphVertexCell hsub hmap hK.isCombinatorialManifoldWithBoundary
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w l h
    cases l with
    | vertexBall z => exact Or.inl (congrArg Section34Label.vertexBall
        ((section34GraphVertexCell_subset_iff w z).mp h))
    | tetraBall t => exact (hVR w t.1 h).elim
    | splitDisk e => exact ((hCV w).not_subset_of_lower_dimension
        (isPLCellOn_section34GraphSplitCell hK e) (by omega) h).elim
    | faceDisk s => exact (hVR w s.1 h).elim
    | patch x => exact (hVR w x.1.1.1 (h.trans _root_.Set.inter_subset_left)).elim
    | faceArc a => exact (hVR w a.1.1.1 (h.trans _root_.Set.inter_subset_right)).elim
    | edgeArc i => exact (hVR w i.1.1.1 (h.trans _root_.Set.inter_subset_left)).elim
    | markedPoint p => exact (hVR w p.1.1.1 (h.trans _root_.Set.inter_subset_right)).elim
  · intro e l h
    cases l with
    | vertexBall w => exact Or.inr (by simp only [section34Dim]; omega)
    | tetraBall t => exact Or.inr (by simp only [section34Dim]; omega)
    | splitDisk d => exact Or.inl (congrArg Section34Label.splitDisk
        ((section34GraphSplitCell_subset_iff e d).mp h))
    | faceDisk s => exact (hER e s.1 h).elim
    | patch x => exact (hER e x.1.1.1 (h.trans _root_.Set.inter_subset_left)).elim
    | faceArc a => exact (hER e a.1.1.1 (h.trans _root_.Set.inter_subset_right)).elim
    | edgeArc i => exact (hER e i.1.1.1 (h.trans _root_.Set.inter_subset_left)).elim
    | markedPoint p => exact (hER e p.1.1.1 (h.trans _root_.Set.inter_subset_right)).elim
  · intro s l h
    cases l with
    | vertexBall w => exact Or.inr (by simp only [section34Dim]; omega)
    | tetraBall t => exact Or.inr (by simp only [section34Dim]; omega)
    | splitDisk e => exact (hRN s (h.trans (hEN e))).elim
    | faceDisk t => exact Or.inl (congrArg Section34Label.faceDisk
        ((section34GraphResidualTriangle_subset_iff hsub hmap s t).mp h))
    | patch x => exact (hRN s ((h.trans _root_.Set.inter_subset_right).trans
        (_root_.Set.subset_iUnion C x.1.2))).elim
    | faceArc a => exact (hRN s ((h.trans _root_.Set.inter_subset_left).trans
        (_root_.Set.subset_iUnion C a.1.2))).elim
    | edgeArc i => exact (hRN s ((h.trans _root_.Set.inter_subset_right).trans (hEN i.1.2))).elim
    | markedPoint p => exact (hRN s ((h.trans _root_.Set.inter_subset_left).trans (hEN p.1.2))).elim
  · intro p l h
    cases l with
    | markedPoint q => exact Or.inl (congrArg Section34Label.markedPoint
        ((section34GraphMarkedPoint_subset_iff hsub hmap p q).mp h))
    | _ => exact Or.inr (by simp only [section34Dim]; omega)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34GraphCutFamily_subset_strict_on_recognized_sources then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34GraphCutFamily_subset_strict_on_recognized_sources"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34GraphCutFamily_subset_strict_on_recognized_sources ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34GraphCutFamily_subset_strict_on_recognized_sources

end DifferentialGeometry.Topology.PiecewiseLinear
