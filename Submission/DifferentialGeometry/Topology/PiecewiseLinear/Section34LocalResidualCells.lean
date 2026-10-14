/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualCells
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCoreComplex
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplexSubcomplex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Classical in
theorem closure_convexHull_sdiff_derivedNeighborhood_eq_cells
    {K L : Geometry.SimplicialComplex ℝ E} (hL : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) :
    closure (convexHull ℝ (s : Set E) \ (derivedNeighborhood K L).space) =
      ⋃ t ∈ {t : Finset E | t ⊆ s ∧ t.Nonempty ∧ t ∉ L.faces},
        (derivedNeighborhoodCell (restrict K (convexHull ℝ (s : Set E))) t).space := by
  classical
  let S := restrict K (convexHull ℝ (s : Set E))
  have hfinite : S.faces.Finite := by
    rw [show S = simplexComplex s (K.indep hs) from restrict_convexHull_eq_simplexComplex K hs]
    exact simplexComplex_faces_finite s (K.indep hs)
  let _ : Finite S.faces := hfinite.to_subtype
  have hset : convexHull ℝ (s : Set E) \ (derivedNeighborhood K L).space =
      S.space \ (derivedNeighborhood S L).space := by
    rw [← derivedNeighborhood_space_inter_subcomplex K S L (restrict_faces_subset K _),
      show S.space = convexHull ℝ (s : Set E) from restrict_convexHull_space hs]
    ext x
    simp only [_root_.Set.mem_sdiff, _root_.Set.mem_inter_iff]
    tauto
  rw [hset, closure_space_sdiff_derivedNeighborhood_space (restrict_faces_subset K _) hL]
  have hfaces (t : Finset E) :
      t ∈ (restrict K (convexHull ℝ (s : Set E))).faces ↔ t ⊆ s ∧ t.Nonempty := by
    rw [restrict_convexHull_eq_simplexComplex K hs]
    exact and_comm
  simp_rw [hfaces, and_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.closure_convexHull_sdiff_derivedNeighborhood_eq_cells then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.closure_convexHull_sdiff_derivedNeighborhood_eq_cells"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.closure_convexHull_sdiff_derivedNeighborhood_eq_cells ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.closure_convexHull_sdiff_derivedNeighborhood_eq_cells

open _root_.Classical in
theorem closure_triangle_sdiff_derivedNeighborhood_eq_cell
    {K L : Geometry.SimplicialComplex ℝ E} (hL : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3)
    (hcore : ∀ t ⊆ s, t.Nonempty → (t ∈ L.faces ↔ t.card ≤ 2)) :
    closure (convexHull ℝ (s : Set E) \ (derivedNeighborhood K L).space) =
      (derivedNeighborhoodCell (restrict K (convexHull ℝ (s : Set E))) s).space := by
  rw [closure_convexHull_sdiff_derivedNeighborhood_eq_cells hL hs]
  apply Subset.antisymm
  · refine _root_.Set.iUnion₂_subset fun t ht => ?_
    have heq : t = s := by
      by_contra hne
      have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨ht.1, hne⟩)
      exact ht.2.2 ((hcore t ht.1 ht.2.1).mpr (by omega))
    subst t
    exact subset_rfl
  · exact _root_.Set.subset_biUnion_of_mem (u := fun t =>
      (derivedNeighborhoodCell (restrict K (convexHull ℝ (s : Set E))) t).space)
      ⟨subset_rfl, K.nonempty_of_mem_faces hs, fun hmem => by
        have := (hcore s subset_rfl (K.nonempty_of_mem_faces hs)).mp hmem
        omega⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.closure_triangle_sdiff_derivedNeighborhood_eq_cell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.closure_triangle_sdiff_derivedNeighborhood_eq_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.closure_triangle_sdiff_derivedNeighborhood_eq_cell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.closure_triangle_sdiff_derivedNeighborhood_eq_cell

open _root_.Classical in
theorem closure_tetrahedron_sdiff_derivedNeighborhood_eq_cells
    {K L : Geometry.SimplicialComplex ℝ E} (hL : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 4)
    (hcore : ∀ t ⊆ s, t.Nonempty → (t ∈ L.faces ↔ t.card ≤ 2)) :
    closure (convexHull ℝ (s : Set E) \ (derivedNeighborhood K L).space) =
      (derivedNeighborhoodCell (restrict K (convexHull ℝ (s : Set E))) s).space ∪
        ⋃ t ∈ s.powersetCard 3,
          (derivedNeighborhoodCell (restrict K (convexHull ℝ (s : Set E))) t).space := by
  rw [closure_convexHull_sdiff_derivedNeighborhood_eq_cells hL hs]
  apply Subset.antisymm
  · refine _root_.Set.iUnion₂_subset fun t ht => ?_
    have hlo : 3 ≤ t.card := by
      by_contra hlt
      exact ht.2.2 ((hcore t ht.1 ht.2.1).mpr (by omega))
    by_cases heq : t = s
    · subst t
      exact _root_.Set.subset_union_left
    · have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨ht.1, heq⟩)
      exact _root_.Set.subset_union_of_subset_right (_root_.Set.subset_biUnion_of_mem (u := fun t =>
        (derivedNeighborhoodCell (restrict K (convexHull ℝ (s : Set E))) t).space)
        (Finset.mem_powersetCard.mpr ⟨ht.1, by omega⟩)) _
  · refine _root_.Set.union_subset ?_ (_root_.Set.iUnion₂_subset fun t ht => ?_)
    · exact _root_.Set.subset_biUnion_of_mem (u := fun t =>
        (derivedNeighborhoodCell (restrict K (convexHull ℝ (s : Set E))) t).space)
        ⟨subset_rfl, K.nonempty_of_mem_faces hs, fun hmem => by
          have := (hcore s subset_rfl (K.nonempty_of_mem_faces hs)).mp hmem
          omega⟩
    · obtain ⟨hts, htcard⟩ := Finset.mem_powersetCard.mp ht
      have hne : t.Nonempty := Finset.card_pos.mp (by omega)
      exact _root_.Set.subset_biUnion_of_mem (u := fun t =>
        (derivedNeighborhoodCell (restrict K (convexHull ℝ (s : Set E))) t).space)
        ⟨hts, hne, fun hmem => by
          have := (hcore t hts hne).mp hmem
          omega⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.closure_tetrahedron_sdiff_derivedNeighborhood_eq_cells then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.closure_tetrahedron_sdiff_derivedNeighborhood_eq_cells"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.closure_tetrahedron_sdiff_derivedNeighborhood_eq_cells ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.closure_tetrahedron_sdiff_derivedNeighborhood_eq_cells

variable [FiniteDimensional ℝ E]

open _root_.Classical in
theorem isPLBall_closure_triangle_sdiff_derivedNeighborhood
    {K L : Geometry.SimplicialComplex ℝ E} (hL : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3)
    (hcore : ∀ t ⊆ s, t.Nonempty → (t ∈ L.faces ↔ t.card ≤ 2)) :
    IsPLBall 2 (closure (convexHull ℝ (s : Set E) \ (derivedNeighborhood K L).space)) := by
  rw [closure_triangle_sdiff_derivedNeighborhood_eq_cell hL hs hcard hcore]
  let S := restrict K (convexHull ℝ (s : Set E))
  have hfinite : S.faces.Finite := by
    rw [show S = simplexComplex s (K.indep hs) from restrict_convexHull_eq_simplexComplex K hs]
    exact simplexComplex_faces_finite s (K.indep hs)
  let _ : Finite S.faces := hfinite.to_subtype
  have hball : IsPLBall (1 + 1) S.space := by
    rw [show S.space = convexHull ℝ (s : Set E) from restrict_convexHull_space hs]
    exact isPLBall_convexHull_of_affineIndependent s (K.indep hs) hcard
  exact hball.isCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhoodCell
    ⟨hs, subset_rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_closure_triangle_sdiff_derivedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_closure_triangle_sdiff_derivedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_closure_triangle_sdiff_derivedNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_closure_triangle_sdiff_derivedNeighborhood

open _root_.Classical in
theorem isPLBall_closure_tetrahedron_sdiff_derivedNeighborhood
    {K L : Geometry.SimplicialComplex ℝ E} (hL : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 4)
    (hcore : ∀ t ⊆ s, t.Nonempty → (t ∈ L.faces ↔ t.card ≤ 2)) :
    IsPLBall 3 (closure (convexHull ℝ (s : Set E) \ (derivedNeighborhood K L).space)) := by
  rw [closure_tetrahedron_sdiff_derivedNeighborhood_eq_cells hL hs hcard hcore]
  let S := restrict K (convexHull ℝ (s : Set E))
  have hfinite : S.faces.Finite := by
    rw [show S = simplexComplex s (K.indep hs) from restrict_convexHull_eq_simplexComplex K hs]
    exact simplexComplex_faces_finite s (K.indep hs)
  let _ : Finite S.faces := hfinite.to_subtype
  have hball : IsPLBall (2 + 1) S.space := by
    rw [show S.space = convexHull ℝ (s : Set E) from restrict_convexHull_space hs]
    exact isPLBall_convexHull_of_affineIndependent s (K.indep hs) hcard
  exact hball.isCombinatorialManifoldWithBoundary.isPLBall_union_derivedNeighborhoodCells_of_card
    ⟨hs, subset_rfl⟩ (s.powersetCard 3) (k := 3) (by norm_num) (by omega)
    (fun t ht => (Finset.mem_powersetCard.mp ht).1) (fun t ht => (Finset.mem_powersetCard.mp ht).2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_closure_tetrahedron_sdiff_derivedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_closure_tetrahedron_sdiff_derivedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_closure_tetrahedron_sdiff_derivedNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_closure_tetrahedron_sdiff_derivedNeighborhood

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  {U : Set X}

open _root_.Classical in
theorem LocallyFinitePLPieceIn.isPLBall_graphCut_triangle
    (T : LocallyFinitePLPieceIn E 3 X U) {s : Finset E}
    (hs : s ∈ T.complex.faces) (hcard : s.card = 3) :
    IsPLBall 2 (closure (convexHull ℝ (s : Set E) \ (derivedNeighborhood T.complex
      (restrict T.complex (T.map ⁻¹' graphSkeletonSpace T))).space)) := by
  apply isPLBall_closure_triangle_sdiff_derivedNeighborhood
    (restrict_faces_subset T.complex _) hs hcard
  intro t hts hne
  rw [mem_restrict_preimage_graphSkeletonSpace_iff]
  exact and_iff_right (T.complex.down_closed hs hts hne)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLBall_graphCut_triangle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLBall_graphCut_triangle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLBall_graphCut_triangle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLBall_graphCut_triangle

open _root_.Classical in
theorem LocallyFinitePLPieceIn.isPLBall_graphCut_tetrahedron
    (T : LocallyFinitePLPieceIn E 3 X U) {s : Finset E}
    (hs : s ∈ T.complex.faces) (hcard : s.card = 4) :
    IsPLBall 3 (closure (convexHull ℝ (s : Set E) \ (derivedNeighborhood T.complex
      (restrict T.complex (T.map ⁻¹' graphSkeletonSpace T))).space)) := by
  apply isPLBall_closure_tetrahedron_sdiff_derivedNeighborhood
    (restrict_faces_subset T.complex _) hs hcard
  intro t hts hne
  rw [mem_restrict_preimage_graphSkeletonSpace_iff]
  exact and_iff_right (T.complex.down_closed hs hts hne)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLBall_graphCut_tetrahedron then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLBall_graphCut_tetrahedron"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLBall_graphCut_tetrahedron ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLBall_graphCut_tetrahedron

end DifferentialGeometry.Topology.PiecewiseLinear
