import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandSide

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.lateral_band_subset_of_same_side_of_chart_crossings
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {X S Y B : Set M}
    (hX : IsPLCellOn 3 X S) (hY : IsPLCellOn 3 Y B)
    (hcross : ∀ x ∈ S ∩ B, ∃ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)),
      x ∈ c.source ∧
        HasPLCrossingAt (c '' (B ∩ c.source)) (c '' (S ∩ c.source)) (c x))
    {C D F : Set M} (hC : closure (interior C) = C) (hD : IsClosed D)
    (hfront : frontier C = D ∪ F) (hfirst : S ∩ C = F)
    {f : (Fin 3 → ℝ) × ℝ → M}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hfB : f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ B)
    (hempty : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Ioo (0 : ℝ) 1)) S)
    (hdis : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1)) D)
    (hside : (C ⊆ X ∧ f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Ioo (0 : ℝ) 1) ⊆ interior X) ∨
      (C ∩ X ⊆ S ∧ f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Ioo (0 : ℝ) 1) ⊆ Xᶜ))
    (hmeet : (f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ F).Nonempty) :
    f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ C ∧
      S ∩ f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ F := by
  obtain ⟨x, hxf, hxF⟩ := hmeet
  have hxfirst : x ∈ S ∩ C := hfirst.symm ▸ hxF
  have hxD : x ∉ D := fun hxD => disjoint_left.mp hdis hxf hxD
  obtain ⟨hchart⟩ := hY.nonempty_chartedSpace_boundary
  let _ := hchart
  have hball (N : Set M) (hN : N ∈ 𝓝 x) :=
    exists_ball_chart_of_mem_nhdsWithin_surface (hfB hxf) self_mem_nhdsWithin hN
  obtain ⟨c, hxc, hcross⟩ := hcross x ⟨hxfirst.1, hfB hxf⟩
  have hcross' : HasPLCrossingAt (c '' (B ∩ c.source))
      (c '' (frontier X ∩ c.source)) (c x) := hX.boundary_eq_frontier ▸ hcross
  have hreg : closure (interior X) = X := by
    rw [← hX.sdiff_boundary_eq_interior]
    exact hX.closure_sdiff_boundary
  obtain ⟨V, hV, hxV, hVD, hin, hout⟩ := exists_connected_ambient_sides_of_chart_crossing
    hX.isCompact.isClosed (hreg.symm ▸ hX.boundary_subset hxfirst.1)
    c hxc hcross' hball (hD.isOpen_compl.mem_nhds hxD)
  have hFsub : F ⊆ S := fun _ hy => (hfirst.symm ▸ hy).1
  have hlocal : V ∩ frontier C ⊆ frontier X := by
    rintro y ⟨hyV, hyC⟩
    rw [hfront] at hyC
    rcases hyC with hyD | hyF
    · exact False.elim (hVD hyV hyD)
    · exact hX.boundary_eq_frontier ▸ hFsub hyF
  have havoid : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Ioo (0 : ℝ) 1)) (frontier C) := by
    rw [hfront]
    exact disjoint_union_right.mpr
      ⟨hdis.mono_left (_root_.Set.image_mono (_root_.Set.prod_mono_right _root_.Set.Ioo_subset_Icc_self)),
        hempty.mono_right hFsub⟩
  have hsub : f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ C := by
    apply image_lateral_subset_of_same_side hf (hC ▸ isClosed_closure) hreg
      (hC.symm ▸ hxfirst.2) hxf (hV.mem_nhds hxV) hin hout hlocal havoid
    rcases hside with hside | ⟨hCX, hfX⟩
    · exact Or.inl hside
    · exact Or.inr ⟨fun y hy => hX.boundary_eq_frontier ▸ hCX hy, hfX⟩
  exact ⟨hsub, fun _ hy => hfirst ▸ ⟨hy.1, hsub hy.2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.lateral_band_subset_of_same_side_of_chart_crossings then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.lateral_band_subset_of_same_side_of_chart_crossings"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.lateral_band_subset_of_same_side_of_chart_crossings ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.lateral_band_subset_of_same_side_of_chart_crossings

theorem IsPLCellOn.not_interleaved_of_current_matching_bands
    {M ι : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [Preorder ι]
    {X S Y B : Set M} (hX : IsPLCellOn 3 X S) (hY : IsPLCellOn 3 Y B)
    (hcross : ∀ x ∈ S ∩ B, ∃ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)),
      x ∈ c.source ∧
        HasPLCrossingAt (c '' (B ∩ c.source)) (c '' (S ∩ c.source)) (c x))
    {J : ι → Set M} (hJ : ∀ r, J r ⊆ S)
    (hJdis : Pairwise fun i j => Disjoint (J i) (J j)) {i j k l : ι}
    {f g : (Fin 3 → ℝ) × ℝ → M}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hfi : _root_.Set.InjOn f (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hgi : _root_.Set.InjOn g (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hfB : f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ B)
    (hgB : g '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ B)
    (hfzero : f '' (stdSimplexBoundary 2 ×ˢ {0}) = J k)
    (hfone : f '' (stdSimplexBoundary 2 ×ˢ {1}) = J l)
    (hgzero : g '' (stdSimplexBoundary 2 ×ˢ {0}) = J i)
    (hgone : g '' (stdSimplexBoundary 2 ×ˢ {1}) = J j)
    (hfempty : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Ioo (0 : ℝ) 1)) S)
    (hgempty : Disjoint (g '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Ioo (0 : ℝ) 1)) S)
    {C F : Set M} (hC : closure (interior C) = C)
    (hfront : frontier C = g '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∪ F)
    (hfirst : S ∩ C = F) (hCside : C ⊆ X ∨ C ∩ X ⊆ S)
    (hinterval : ∀ r, J r ⊆ F ↔ i ≤ r ∧ r ≤ j)
    (hbands : (g '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Ioo (0 : ℝ) 1) ⊆ interior X ∧
      f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Ioo (0 : ℝ) 1) ⊆ interior X) ∨
      (g '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Ioo (0 : ℝ) 1) ⊆ Xᶜ ∧
        f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Ioo (0 : ℝ) 1) ⊆ Xᶜ)) :
    ¬ (i < k ∧ k < j ∧ j < l) := by
  rintro ⟨hik, hkj, hjl⟩
  have hendsF : f '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      f '' (stdSimplexBoundary 2 ×ˢ {1}) ⊆ S := by
    rw [hfzero, hfone]
    exact _root_.Set.union_subset (hJ k) (hJ l)
  have hendsG : g '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      g '' (stdSimplexBoundary 2 ×ˢ {1}) ⊆ S := by
    rw [hgzero, hgone]
    exact _root_.Set.union_subset (hJ i) (hJ j)
  have hendsDis : Disjoint (g '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      g '' (stdSimplexBoundary 2 ×ˢ {1}))
      (f '' (stdSimplexBoundary 2 ×ˢ {0}) ∪ f '' (stdSimplexBoundary 2 ×ˢ {1})) := by
    rw [hgzero, hgone, hfzero, hfone, _root_.Set.disjoint_union_left, _root_.Set.disjoint_union_right,
      _root_.Set.disjoint_union_right]
    exact ⟨⟨hJdis hik.ne, hJdis ((hik.trans hkj).trans hjl).ne⟩,
      ⟨hJdis hkj.ne', hJdis hjl.ne⟩⟩
  have hdis := hY.disjoint_lateral_bands_of_disjoint_ends hg hgi hf hfi hgB hfB
    hendsG hendsF hgempty hfempty hendsDis
  have hDclosed : IsClosed (g '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1)) :=
    (isAnnulusOn_stdSimplex_lateral.isCompact.image_of_continuousOn hg).isClosed
  have hODC : g '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Ioo (0 : ℝ) 1) ⊆ C := by
    intro x hx
    apply (hC ▸ isClosed_closure).frontier_subset
    rw [hfront]
    exact Or.inl (_root_.Set.image_mono (_root_.Set.prod_mono_right _root_.Set.Ioo_subset_Icc_self) hx)
  have hOD := ((isConnected_stdSimplexBoundary 0).nonempty.prod
    (nonempty_Ioo.mpr (zero_lt_one : (0 : ℝ) < 1))).image g
  have hside := same_side_of_nonempty_subset
    (hCside.imp id (fun h => h.trans hX.boundary_eq_frontier.subset)) hOD hODC hbands
  have hside' : (C ⊆ X ∧ f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Ioo (0 : ℝ) 1) ⊆ interior X) ∨
      (C ∩ X ⊆ S ∧ f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Ioo (0 : ℝ) 1) ⊆ Xᶜ) :=
    hside.imp id (fun h => ⟨h.1.trans hX.boundary_eq_frontier.symm.subset, h.2⟩)
  obtain ⟨x, hx⟩ : (J k).Nonempty := hfzero ▸
    ((isConnected_stdSimplexBoundary 0).nonempty.prod (_root_.Set.singleton_nonempty (0 : ℝ))).image f
  have hxf : x ∈ f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) :=
    _root_.Set.image_mono (_root_.Set.prod_mono_right (by simp)) (hfzero.symm ▸ hx)
  have hsub := (hX.lateral_band_subset_of_same_side_of_chart_crossings hY hcross hC
    hDclosed hfront hfirst hf hfB hfempty hdis.symm hside'
      ⟨x, hxf, (hinterval k).mpr ⟨hik.le, hkj.le⟩ hx⟩).2
  have hLF : J l ⊆ F := by
    intro y hy
    exact hsub ⟨hJ l hy, _root_.Set.image_mono (_root_.Set.prod_mono_right (by simp)) (hfone.symm ▸ hy)⟩
  exact hjl.not_ge ((hinterval l).mp hLF).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.not_interleaved_of_current_matching_bands then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.not_interleaved_of_current_matching_bands"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.not_interleaved_of_current_matching_bands ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.not_interleaved_of_current_matching_bands

end DifferentialGeometry.Topology.PiecewiseLinear
