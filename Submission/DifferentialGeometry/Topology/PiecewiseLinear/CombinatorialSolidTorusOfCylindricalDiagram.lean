/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CylinderCut
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CylindricalCircle
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusProduct
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldNeighborhood
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallGluing
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Orientation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open _root_.Classical in
private theorem image_slab_ends_subset_boundaryComplex
    {P : Set E} (hP : IsPLBall 2 P) {a b : ℝ} (hab : a < b)
    (K : Geometry.SimplicialComplex ℝ F) [Finite K.faces]
    {f : E × ℝ → F} (hf : IsPLHomeomorphOn f (P ×ˢ _root_.Set.Icc a b) K.space) :
    f '' (P ×ˢ {a}) ⊆ (boundaryComplex 3 K).space ∧
      f '' (P ×ˢ {b}) ⊆ (boundaryComplex 3 K).space := by
  let _ : DecidableEq E := Classical.decEq _
  let _ : DecidableEq F := Classical.decEq _
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  obtain ⟨Q, hQfin, hQspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite Q.faces := hQfin.to_subtype
  have hQ : IsPLBall 2 Q.space := hQspace.symm ▸ hP
  have hprod := isPLBall_three_prod hP (isPLBall_Icc hab)
  obtain ⟨R, hRfin, hRspace⟩ := hprod.isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  have hR : IsPLBall 3 R.space := hRspace.symm ▸ hprod
  have hbd := boundaryComplex_space_prism Q hQ hab R (hQspace.symm ▸ hRspace)
  rw [hQspace] at hbd
  have hfR : IsPLHomeomorphOn f R.space K.space := hRspace.symm ▸ hf
  rw [boundaryComplex_space_of_isPLHomeomorphOn R K hR.isCombinatorialManifoldWithBoundary hfR,
    hbd]
  exact ⟨image_mono (fun _ hx => Or.inl ⟨hx.1, Or.inl hx.2⟩),
    _root_.Set.image_mono (fun _ hx => Or.inl ⟨hx.1, Or.inr hx.2⟩)⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_slab_ends_subset_boundaryComplex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.image_slab_ends_subset_boundaryComplex target :: scope.openDecls } }

namespace IsCylindricalDiagram

variable {f : E × ℝ → F} {P : Set E} {S : Set F}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem image_strip_inter_adjacent (h : IsCylindricalDiagram f P S) {a b c : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ 1) (hac : 0 < a ∨ c < 1) :
    f '' (P ×ˢ _root_.Set.Icc a b) ∩ f '' (P ×ˢ _root_.Set.Icc b c) = f '' (P ×ˢ {b}) := by
  apply Subset.antisymm
  · rintro z ⟨⟨x, hx, rfl⟩, y, hy, hyx⟩
    have hxy := h.injOn_strip ha hc hac ⟨hx.1, hx.2.1, hx.2.2.trans hbc⟩
      ⟨hy.1, hab.trans hy.2.1, hy.2.2⟩ hyx.symm
    have h2 : x.2 = y.2 := congrArg Prod.snd hxy
    exact ⟨x, ⟨hx.1, le_antisymm hx.2.2 (hy.2.1.trans_eq h2.symm)⟩, rfl⟩
  · rintro z ⟨x, hx, rfl⟩
    have hxb : x.2 = b := hx.2
    refine ⟨⟨x, ⟨hx.1, ?_⟩, rfl⟩, ⟨x, ⟨hx.1, ?_⟩, rfl⟩⟩
    · rw [_root_.Set.mem_Icc, hxb]
      exact ⟨hab, le_rfl⟩
    · rw [_root_.Set.mem_Icc, hxb]
      exact ⟨le_rfl, hbc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.image_strip_inter_adjacent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.image_strip_inter_adjacent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.image_strip_inter_adjacent ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.image_strip_inter_adjacent

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem image_strip_inter_ends (h : IsCylindricalDiagram f P S) {b c : ℝ} (hb : 0 ≤ b)
    (hbc : b < c) (hc : c ≤ 1) :
    f '' (P ×ˢ _root_.Set.Icc 0 b) ∩ f '' (P ×ˢ _root_.Set.Icc c 1) = f '' (P ×ˢ {0}) := by
  apply Subset.antisymm
  · rintro z ⟨⟨x, hx, rfl⟩, y, hy, hyx⟩
    rcases h.eq_or_endpoints x ⟨hx.1, hx.2.1, hx.2.2.trans (hbc.le.trans hc)⟩
      y ⟨hy.1, hb.trans (hbc.le.trans hy.2.1), hy.2.2⟩ hyx.symm with hxy | hends | hends
    · have h2 : x.2 = y.2 := congrArg Prod.snd hxy
      linarith [hx.2.2, hy.2.1]
    · exact ⟨x, ⟨hx.1, hends.1⟩, rfl⟩
    · linarith [hx.2.2, hends.1]
  · rintro z ⟨x, hx, rfl⟩
    have hx0 : x.2 = 0 := hx.2
    refine ⟨⟨x, ⟨hx.1, ?_⟩, rfl⟩, ?_⟩
    · rw [_root_.Set.mem_Icc, hx0]
      exact ⟨le_rfl, hb⟩
    · have htop : f x ∈ f '' (P ×ˢ {1}) := by
        rw [h.image_top_eq_bottom]
        exact ⟨x, hx, rfl⟩
      have hsub : P ×ˢ ({1} : Set ℝ) ⊆ P ×ˢ _root_.Set.Icc c 1 := by
        rintro y ⟨hyP, hy1⟩
        refine ⟨hyP, ?_⟩
        rw [_root_.Set.mem_Icc, show y.2 = 1 from hy1]
        exact ⟨hc, le_rfl⟩
      exact _root_.Set.image_mono hsub htop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.image_strip_inter_ends then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.image_strip_inter_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.image_strip_inter_ends ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.image_strip_inter_ends

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem apply_notMem_image_strip (h : IsCylindricalDiagram f P S) {x : E × ℝ}
    (hx : x ∈ P ×ˢ _root_.Set.Icc 0 1) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hxab : x.2 ∉ _root_.Set.Icc a b)
    (hend : 0 ∈ _root_.Set.Icc a b ∨ 1 ∈ _root_.Set.Icc a b → 0 < x.2 ∧ x.2 < 1) : f x ∉ f '' (P ×ˢ _root_.Set.Icc a b) := by
  rintro ⟨y, hy, hyx⟩
  rcases h.eq_or_endpoints y ⟨hy.1, ha.trans hy.2.1, hy.2.2.trans hb⟩ x hx hyx with
    hxy | hends | hends
  · apply hxab
    rw [← hxy]
    exact hy.2
  · have h0 : (0 : ℝ) ∈ _root_.Set.Icc a b := by
      rw [← hends.1]
      exact hy.2
    linarith [hends.2, (hend (Or.inl h0)).2]
  · have h1 : (1 : ℝ) ∈ _root_.Set.Icc a b := by
      rw [← hends.1]
      exact hy.2
    linarith [hends.2, (hend (Or.inr h1)).1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.apply_notMem_image_strip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.apply_notMem_image_strip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.apply_notMem_image_strip ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.apply_notMem_image_strip

omit [FiniteDimensional ℝ F] in
theorem isClosed_image_strip (h : IsCylindricalDiagram f P S) (hP : IsCompact P) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) : IsClosed (f '' (P ×ˢ _root_.Set.Icc a b)) :=
  ((hP.prod _root_.CompactIccSpace.isCompact_Icc).image_of_continuousOn
    (h.isPiecewiseAffineOn.continuousOn.mono fun _ hx =>
      ⟨hx.1, ha.trans hx.2.1, hx.2.2.trans hb⟩)).isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isClosed_image_strip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isClosed_image_strip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isClosed_image_strip ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isClosed_image_strip

open _root_.Classical in
theorem exists_simplicialComplex_slab (h : IsCylindricalDiagram f P S) (hP : IsPLBall 2 P)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hne : 0 < a ∨ b < 1) :
    ∃ C : Geometry.SimplicialComplex ℝ F, C.faces.Finite ∧ C.space = f '' (P ×ˢ _root_.Set.Icc a b) ∧
      IsPLBall 3 C.space ∧ f '' (P ×ˢ {a}) ⊆ (boundaryComplex 3 C).space ∧
        f '' (P ×ˢ {b}) ⊆ (boundaryComplex 3 C).space := by
  have hg := h.isPLHomeomorphOn_strip hP.isPolyhedron ha hb hne
  have hC := (isPLBall_three_prod hP (isPLBall_Icc hab)).of_isPLHomeomorphOn hg
  obtain ⟨C, hCfin, hCsp⟩ := hC.isPolyhedron.exists_simplicialComplex
  let _ : Finite C.faces := hCfin.to_subtype
  have hends := image_slab_ends_subset_boundaryComplex hP hab C (hCsp.symm ▸ hg)
  exact ⟨C, hCfin, hCsp, hCsp.symm ▸ hC, hends.1, hends.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_simplicialComplex_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_simplicialComplex_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_simplicialComplex_slab ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_simplicialComplex_slab

open _root_.Classical in
theorem isCombinatorialSolidTorus (h : IsCylindricalDiagram f P S) (hP : IsPLBall 2 P)
    (hdim : Module.finrank ℝ F = 3) : IsCombinatorialSolidTorus S := by
  have hPc : IsCompact P := hP.isPolyhedron.isCompact
  obtain ⟨C₀, hC₀fin, hC₀sp, hC₀, hC₀lo, hC₀hi⟩ := h.exists_simplicialComplex_slab hP le_rfl
    (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num) (Or.inr (by norm_num))
  obtain ⟨C₁, hC₁fin, hC₁sp, hC₁, hC₁lo, hC₁hi⟩ := h.exists_simplicialComplex_slab hP
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) < 2 / 3) (by norm_num)
    (Or.inl (by norm_num))
  obtain ⟨C₂, hC₂fin, hC₂sp, hC₂, hC₂lo, hC₂hi⟩ := h.exists_simplicialComplex_slab hP
    (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (2 / 3 : ℝ) < 1) le_rfl
    (Or.inl (by norm_num))
  let _ : Finite C₀.faces := hC₀fin.to_subtype
  let _ : Finite C₁.faces := hC₁fin.to_subtype
  let _ : Finite C₂.faces := hC₂fin.to_subtype
  have h01 : C₀.space ∩ C₁.space = f '' (P ×ˢ {1 / 3}) := by
    rw [hC₀sp, hC₁sp]
    exact h.image_strip_inter_adjacent le_rfl (by norm_num) (by norm_num) (by norm_num)
      (Or.inr (by norm_num))
  have h12 : C₁.space ∩ C₂.space = f '' (P ×ˢ {2 / 3}) := by
    rw [hC₁sp, hC₂sp]
    exact h.image_strip_inter_adjacent (by norm_num) (by norm_num) (by norm_num) le_rfl
      (Or.inl (by norm_num))
  have h02 : C₀.space ∩ C₂.space = f '' (P ×ˢ {0}) := by
    rw [hC₀sp, hC₂sp]
    exact h.image_strip_inter_ends (by norm_num) (by norm_num) (by norm_num)
  have hD₀ : IsPLBall 2 (f '' (P ×ˢ {0})) :=
    hP.of_isPLHomeomorphOn (h.isPLHomeomorphOn_slice hP.isPolyhedron (by norm_num))
  have hD₁ : IsPLBall 2 (f '' (P ×ˢ {1 / 3})) :=
    hP.of_isPLHomeomorphOn (h.isPLHomeomorphOn_slice hP.isPolyhedron (by norm_num))
  have hD₂ : IsPLBall 2 (f '' (P ×ˢ {2 / 3})) :=
    hP.of_isPLHomeomorphOn (h.isPLHomeomorphOn_slice hP.isPolyhedron (by norm_num))
  have hC₂top : f '' (P ×ˢ {0}) ⊆ (boundaryComplex 3 C₂).space := by
    rw [← h.image_top_eq_bottom]
    exact hC₂hi
  have hunion : C₀.space ∪ C₁.space ∪ C₂.space = S := by
    rw [hC₀sp, hC₁sp, hC₂sp, ← _root_.Set.image_union, ← _root_.Set.image_union, ← _root_.Set.prod_union, ← _root_.Set.prod_union,
      _root_.Set.Icc_union_Icc_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) ≤ 2 / 3),
      _root_.Set.Icc_union_Icc_eq_Icc (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (2 / 3 : ℝ) ≤ 1),
      h.image_eq]
  have hSpoly : IsPolyhedron S := by
    rw [← hunion]
    exact ((isPolyhedron_space C₀).union (isPolyhedron_space C₁)).union (isPolyhedron_space C₂)
  obtain ⟨M, hMfin, hMsp⟩ := hSpoly.exists_simplicialComplex
  let _ : Finite M.faces := hMfin.to_subtype
  have hseam : IsPLBall 3 (C₀.space ∪ C₂.space) :=
    isPLBall_union_of_boundary_disk C₀ C₂ hC₀ hC₂ (h02 ▸ hD₀) (h02 ▸ hC₀lo) (h02 ▸ hC₂top)
  have hprod := isPLBall_three_prod hP (isPLBall_Icc (by norm_num : (1 / 4 : ℝ) < 3 / 4))
  have hmid : IsPLBall 3 (f '' (P ×ˢ _root_.Set.Icc (1 / 4) (3 / 4))) :=
    hprod.of_isPLHomeomorphOn (h.isPLHomeomorphOn_strip hP.isPolyhedron (by norm_num)
      (by norm_num) (Or.inl (by norm_num)))
  have hM : IsCombinatorialManifoldWithBoundary 3 M := by
    refine isCombinatorialManifoldWithBoundary_of_isPLBall_neighborhoods (n := 2) M ?_
    intro p hp
    rw [hMsp] at hp ⊢
    rw [← h.image_eq] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    by_cases hxm : 1 / 4 < x.2 ∧ x.2 < 3 / 4
    · refine ⟨f '' (P ×ˢ _root_.Set.Icc (1 / 4) (3 / 4)), hmid, ?_, ?_⟩
      · rw [← h.image_eq]
        exact _root_.Set.image_mono (_root_.Set.prod_mono subset_rfl (_root_.Set.Icc_subset_Icc (by norm_num) (by norm_num)))
      · refine mem_nhdsWithin.mpr ⟨(f '' (P ×ˢ _root_.Set.Icc 0 (1 / 4)) ∪ f '' (P ×ˢ _root_.Set.Icc (3 / 4) 1))ᶜ,
          ((h.isClosed_image_strip hPc le_rfl (by norm_num)).union
            (h.isClosed_image_strip hPc (by norm_num) le_rfl)).isOpen_compl, ?_, ?_⟩
        · rw [_root_.Set.mem_compl_iff, _root_.Set.mem_union, not_or]
          exact ⟨h.apply_notMem_image_strip hx le_rfl (by norm_num)
              (fun hmem => by linarith [hmem.2, hxm.1])
              (fun _ => ⟨by linarith [hxm.1], by linarith [hxm.2]⟩),
            h.apply_notMem_image_strip hx (by norm_num) le_rfl
              (fun hmem => by linarith [hmem.1, hxm.2])
              (fun _ => ⟨by linarith [hxm.1], by linarith [hxm.2]⟩)⟩
        · rintro y ⟨hyK, hyS⟩
          rw [_root_.Set.mem_compl_iff, _root_.Set.mem_union, not_or] at hyK
          rw [← h.image_eq] at hyS
          obtain ⟨z, hz, rfl⟩ := hyS
          by_cases hz1 : z.2 ≤ 1 / 4
          · exact (hyK.1 ⟨z, ⟨hz.1, hz.2.1, hz1⟩, rfl⟩).elim
          · by_cases hz2 : 3 / 4 ≤ z.2
            · exact (hyK.2 ⟨z, ⟨hz.1, hz2, hz.2.2⟩, rfl⟩).elim
            · exact ⟨z, ⟨hz.1, (not_le.mp hz1).le, (not_le.mp hz2).le⟩, rfl⟩
    · have hx' : x.2 ∉ _root_.Set.Icc (1 / 3 : ℝ) (2 / 3) := fun hmem =>
        hxm ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
      refine ⟨C₀.space ∪ C₂.space, hseam, ?_, ?_⟩
      · rw [← hunion]
        exact _root_.Set.union_subset (subset_union_left.trans _root_.Set.subset_union_left) _root_.Set.subset_union_right
      · refine mem_nhdsWithin.mpr
          ⟨C₁.spaceᶜ, (isPolyhedron_space C₁).isClosed.isOpen_compl, ?_, ?_⟩
        · rw [_root_.Set.mem_compl_iff, hC₁sp]
          exact h.apply_notMem_image_strip hx (by norm_num) (by norm_num) hx'
            (fun hend => by norm_num at hend)
        · rintro y ⟨hyC, hyS⟩
          rw [← hunion] at hyS
          rcases hyS with (hy | hy) | hy
          · exact Or.inl hy
          · exact (hyC hy).elim
          · exact Or.inr hy
  obtain ⟨T, -, hTcard, hMT⟩ := exists_affineIndependent_openSimplex_superset 3 hdim
    (isPolyhedron_space M).isCompact.isBounded
  have hor : IsOrientable 3 M := isOrientable_of_space_subset_convexHull M hM T hTcard
    (hMT.trans (openSimplex_subset_convexHull T))
  have hfM : IsCylindricalDiagram f P M.space := by
    rw [hMsp]
    exact h
  have htorus : IsTopologicalSolidTorus S := by
    rw [← hMsp]
    exact hfM.isTopologicalSolidTorus_of_isOrientable hP M hM hor
  have key : ∀ (A B : Geometry.SimplicialComplex ℝ F) (D : Set F) (i j : Fin 3), i ≠ j →
      A.space ∩ B.space = D → IsPLBall 2 D → D ⊆ (boundaryComplex 3 A).space →
      D ⊆ (boundaryComplex 3 B).space →
      ((A.space ∩ B.space).Nonempty ↔ (SimpleGraph.cycleGraph 3).Adj i j) ∧
        ((SimpleGraph.cycleGraph 3).Adj i j → IsPLBall 2 (A.space ∩ B.space) ∧
          A.space ∩ B.space ⊆ (boundaryComplex 3 A).space ∧
          A.space ∩ B.space ⊆ (boundaryComplex 3 B).space) := by
    intro A B D i j hij hAB hD hDA hDB
    have hadj : (SimpleGraph.cycleGraph 3).Adj i j := by
      rw [SimpleGraph.cycleGraph_three_eq_top]
      exact hij
    rw [hAB]
    exact ⟨⟨fun _ => hadj, fun _ => hD.nonempty⟩, fun _ => ⟨hD, hDA, hDB⟩⟩
  refine ⟨htorus, 3, le_rfl, ![C₀, C₁, C₂], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hC₀fin
    · exact hC₁fin
    · exact hC₂fin
  · rw [← hunion]
    ext y
    simp only [_root_.Set.mem_iUnion, _root_.Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((hy | hy) | hy)
      · exact ⟨0, hy⟩
      · exact ⟨1, hy⟩
      · exact ⟨2, hy⟩
  · intro i
    fin_cases i
    · exact hC₀
    · exact hC₁
    · exact hC₂
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact key C₀ C₁ _ _ _ hij h01 hD₁ hC₀hi hC₁lo
    · exact key C₀ C₂ _ _ _ hij h02 hD₀ hC₀lo hC₂top
    · exact key C₁ C₀ _ _ _ hij (by rw [_root_.Set.inter_comm]; exact h01) hD₁ hC₁lo hC₀hi
    · exact (hij rfl).elim
    · exact key C₁ C₂ _ _ _ hij h12 hD₂ hC₁hi hC₂lo
    · exact key C₂ C₀ _ _ _ hij (by rw [_root_.Set.inter_comm]; exact h02) hD₀ hC₂top hC₀lo
    · exact key C₂ C₁ _ _ _ hij (by rw [_root_.Set.inter_comm]; exact h12) hD₂ hC₂lo hC₁hi
    · exact (hij rfl).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isCombinatorialSolidTorus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isCombinatorialSolidTorus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isCombinatorialSolidTorus ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.isCombinatorialSolidTorus

end IsCylindricalDiagram

theorem isCombinatorialSolidTorus_of_hasCylindricalDiagram {S : Set (EuclideanSpace ℝ (Fin 3))}
    (hS : HasCylindricalDiagram S) : IsCombinatorialSolidTorus S := by
  obtain ⟨f, hf⟩ := hS
  exact hf.isCombinatorialSolidTorus (isPLBall_stdSimplex 2) (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialSolidTorus_of_hasCylindricalDiagram then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialSolidTorus_of_hasCylindricalDiagram"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialSolidTorus_of_hasCylindricalDiagram ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialSolidTorus_of_hasCylindricalDiagram

end DifferentialGeometry.Topology.PiecewiseLinear
