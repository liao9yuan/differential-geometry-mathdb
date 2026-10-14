/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CollarInwardMap
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CollarNeighborhood
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CollarSectorPolyhedron
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralSeparation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Pasting

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem IsPLHomeomorphOn.exists_injective_piecewiseAffineOn_inward
    {B W R A : Set E} {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (B ×ˢ _root_.Set.Icc (0 : ℝ) 1) W)
    (hW : IsPolyhedron W) (hR : IsPolyhedron R) (hBR : Disjoint B R)
    (hbottom : ∀ x ∈ B, ρ (x, 0) = x) (hA : IsPolyhedron A) (hAB : A ⊆ B) :
    ∃ f : E → E, IsPiecewiseAffineOn f (W ∪ R) ∧ _root_.Set.InjOn f (W ∪ R) ∧
      _root_.Set.MapsTo f (W ∪ R) (W ∪ R) ∧ _root_.Set.EqOn f id (A ∪ R) ∧
      ∀ x ∈ W ∪ R, f x ∈ B ↔ x ∈ A := by
  let U := B ×ˢ _root_.Set.Icc (0 : ℝ) 1
  let τ := Function.invFunOn ρ U
  have hτ : _root_.Set.MapsTo τ W U := hρ.symm.bijOn.mapsTo
  have hleft : _root_.Set.LeftInvOn τ ρ U := hρ.bijOn.invOn_invFunOn.1
  have hright : _root_.Set.RightInvOn τ ρ W := hρ.bijOn.invOn_invFunOn.2
  have hBW : B ⊆ W := fun x hx =>
    hbottom x hx ▸ hρ.bijOn.mapsTo ⟨hx, le_rfl, zero_le_one⟩
  have hτbottom : ∀ x ∈ B, τ x = (x, 0) := by
    intro x hx
    have h : τ (ρ (x, 0)) = (x, 0) := hleft ⟨hx, le_rfl, zero_le_one⟩
    rwa [hbottom x hx] at h
  have hboundary : ∀ z ∈ U, ρ z ∈ B ↔ z.2 = 0 := by
    intro z hz
    constructor
    · intro hB
      have heq : z = (ρ z, 0) := hρ.bijOn.injOn hz
        ⟨hB, le_rfl, zero_le_one⟩ (hbottom _ hB).symm
      exact congrArg Prod.snd heq
    · intro hzero
      have heq : z = (z.1, 0) := Prod.ext rfl hzero
      rw [heq, hbottom _ hz.1]
      exact hz.1
  have hheight : ∀ x ∈ W ∩ R, 0 < (τ x).2 := by
    intro x hx
    have hne : (τ x).2 ≠ 0 := by
      intro hzero
      have hxB : x ∈ B := by
        rw [← hright hx.1]
        exact (hboundary _ (hτ hx.1)).mpr hzero
      exact Set.disjoint_left.mp hBR hxB hx.2
    exact lt_of_le_of_ne (hτ hx.1).2.1 hne.symm
  obtain ⟨r, hr, hrheight⟩ : ∃ r : ℝ, 0 < r ∧ ∀ x ∈ W ∩ R, r ≤ (τ x).2 := by
    by_cases hne : (W ∩ R).Nonempty
    · obtain ⟨x, hx, hmin⟩ := (hW.isCompact.inter_right hR.isClosed).exists_isMinOn hne
        (hρ.isPiecewiseAffineOn_invFunOn.continuousOn.snd.mono _root_.Set.inter_subset_left)
      exact ⟨(τ x).2, hheight x hx, fun y hy => hmin hy⟩
    · exact ⟨1, zero_lt_one, fun x hx => False.elim (hne ⟨x, hx⟩)⟩
  let a := _root_.Min.min r 1
  have ha : 0 < a := lt_min hr zero_lt_one
  have haone : a ≤ 1 := min_le_right _ _
  have hthin : ∀ x ∈ W ∩ R, a ≤ (τ x).2 := fun x hx => (min_le_left _ _).trans (hrheight x hx)
  obtain ⟨g, hg, hgpos, hgzero⟩ := hA.exists_nonneg_piecewiseAffine_zero_set
  let H := collarInwardMap g a
  have hHU : _root_.Set.MapsTo H U U := collarInwardMap_mapsTo_prod_Icc g haone B
  let Q : E → E := ρ ∘ H ∘ τ
  have hQW : _root_.Set.MapsTo Q W W := hρ.bijOn.mapsTo.comp (hHU.comp hτ)
  have hQpl : IsPiecewiseAffineOn Q W := by
    have hHτ : IsPiecewiseAffineOn (H ∘ τ) W := by
      have h := (isPiecewiseAffineOn_collarInwardMap hg a).comp hρ.isPiecewiseAffineOn_invFunOn
      simpa only [_root_.Set.preimage_univ, _root_.Set.inter_univ] using h
    have h := hρ.isPiecewiseAffineOn.comp hHτ
    have hinter : W ∩ (H ∘ τ) ⁻¹' U = W := inter_eq_left.mpr (hHU.comp hτ)
    rwa [hinter] at h
  have hQinj : _root_.Set.InjOn Q W := by
    intro x hx y hy hxy
    apply hρ.symm.bijOn.injOn hx hy
    exact collarInwardMap_injective g a
      (hρ.bijOn.injOn (hHU (hτ hx)) (hHU (hτ hy)) hxy)
  have hQfixed : ∀ x ∈ W, a ≤ (τ x).2 → Q x = x := by
    intro x hx ht
    change ρ (collarInwardMap g a (τ x)) = x
    rw [collarInwardMap_eq_self_of_le g ht]
    exact hright hx
  have hQR : _root_.Set.EqOn Q id (W ∩ R) := fun x hx => hQfixed x hx.1 (hthin x hx)
  have hQpreR : ∀ x ∈ W, Q x ∈ R → Q x = x := by
    intro x hx hRmem
    have heq : τ (Q x) = H (τ x) := hleft (hHU (hτ hx))
    have hhigh : a ≤ (H (τ x)).2 := by
      rw [← heq]
      exact hthin (Q x) ⟨hQW hx, hRmem⟩
    apply hQfixed x hx
    by_contra hlt
    exact (not_lt_of_ge hhigh) (collarInwardMap_snd_lt_of_lt g (lt_of_not_ge hlt))
  have hQA : _root_.Set.EqOn Q id A := by
    intro x hx
    change ρ (collarInwardMap g a (τ x)) = x
    rw [hτbottom x (hAB hx), collarInwardMap_eq_self_of_eq_zero a ((hgzero x).mpr hx)]
    exact hbottom x (hAB hx)
  have hQboundary : ∀ x ∈ W, Q x ∈ B ↔ x ∈ A := by
    intro x hx
    constructor
    · intro hxB
      have hz : (H (τ x)).2 = 0 := (hboundary _ (hHU (hτ hx))).mp hxB
      obtain ⟨ht, hgz⟩ := (collarInwardMap_snd_eq_zero_iff ha (hgpos _) (hτ hx).2.1).mp hz
      have hxeq : x = (τ x).1 := by
        calc
          x = ρ (τ x) := (hright hx).symm
          _ = ρ ((τ x).1, 0) := congrArg ρ (Prod.ext rfl ht)
          _ = (τ x).1 := hbottom _ (hτ hx).1
      rw [hxeq]
      exact (hgzero _).mp hgz
    · intro hxA
      rw [hQA hxA]
      exact hAB hxA
  let f := W.piecewise Q id
  have hfW : _root_.Set.EqOn f Q W := W.piecewise_eqOn Q id
  have hfR : _root_.Set.EqOn f id R := by
    intro x hx
    by_cases hxW : x ∈ W
    · rw [hfW hxW]
      exact hQR ⟨hxW, hx⟩
    · exact _root_.Set.piecewise_eq_of_notMem W Q id hxW
  have hfpl : IsPiecewiseAffineOn f (W ∪ R) :=
    hQpl.piecewise_of_isClosed hR.isPLHomeomorphOn_id.isPiecewiseAffineOn
      hW.isClosed hR.isClosed hQR
  have hfinj : _root_.Set.InjOn f (W ∪ R) := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hfW hx, hfW hy] at hxy
      exact hQinj hx hy hxy
    · rw [hfW hx, hfR hy] at hxy
      exact (hQpreR x hx (hxy.symm ▸ hy)).symm.trans hxy
    · rw [hfR hx, hfW hy] at hxy
      exact hxy.trans (hQpreR y hy (hxy ▸ hx))
    · simpa only [hfR hx, hfR hy, id_eq] using hxy
  refine ⟨f, hfpl, hfinj, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · rw [hfW hx]
      exact Or.inl (hQW hx)
    · rw [hfR hx]
      exact Or.inr hx
  · intro x hx
    rcases hx with hx | hx
    · rw [hfW (hBW (hAB hx))]
      exact hQA hx
    · exact hfR hx
  · intro x hx
    by_cases hxW : x ∈ W
    · rw [hfW hxW]
      exact hQboundary x hxW
    · have hxR := hx.resolve_left hxW
      rw [hfR hxR]
      exact ⟨fun hxB => (hxW (hBW hxB)).elim, fun hxA => hAB hxA⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_injective_piecewiseAffineOn_inward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_injective_piecewiseAffineOn_inward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_injective_piecewiseAffineOn_inward ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_injective_piecewiseAffineOn_inward

open _root_.Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_inward
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {A : Set E}
    (hA : IsPolyhedron A) (hAB : A ⊆ (boundaryComplex 3 K).space) :
    ∃ f : E → E, IsPLHomeomorphOn f K.space (f '' K.space) ∧
      _root_.Set.MapsTo f K.space K.space ∧ _root_.Set.EqOn f id A ∧
      (∀ x ∈ K.space, f x ∈ (boundaryComplex 3 K).space ↔ x ∈ A) ∧
      f '' K.space ∩ (boundaryComplex 3 K).space = A := by
  let B := boundaryComplex 3 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hB := (isCombinatorialManifold_boundaryComplex K hK).isCombinatorialManifoldWithBoundary
  obtain ⟨W, ρ, R, hW, hWK, hρ, hbottom, -, -, hRfinite, -, hRspace, -, -⟩ :=
    hK.exists_isPLHomeomorphOn_surface_prod_Icc K B hB Subset.rfl
      (a := 0) (b := 1) (by norm_num)
  let _ : Finite R.faces := hRfinite.to_subtype
  have hnhds := hρ.mem_nhdsSetWithin_boundaryComplex K hK (by norm_num) hWK hbottom
  obtain ⟨O, hO, hBO, hOW⟩ := mem_nhdsSetWithin.mp hnhds
  have hKR : K.space \ W ⊆ Oᶜ := by
    rintro x ⟨hxK, hxW⟩ hxO
    exact hxW (hOW ⟨hxO, hxK⟩)
  have hRO : R.space ⊆ Oᶜ := by
    rw [hRspace]
    exact closure_minimal hKR hO.isClosed_compl
  have hBR : Disjoint B.space R.space :=
    Set.disjoint_left.mpr fun x hxB hxR => hRO hxR (hBO hxB)
  have hRK : R.space ⊆ K.space := by
    rw [hRspace]
    exact closure_minimal _root_.Set.sdiff_subset (isPolyhedron_space K).isClosed
  have hcover : W ∪ R.space = K.space := by
    apply Subset.antisymm (_root_.Set.union_subset hWK hRK)
    intro x hx
    by_cases hxW : x ∈ W
    · exact Or.inl hxW
    · exact Or.inr (hRspace.symm ▸ subset_closure ⟨hx, hxW⟩)
  obtain ⟨f, hf, hinj, hmap, hfix, hboundary⟩ :=
    hρ.exists_injective_piecewiseAffineOn_inward hW (isPolyhedron_space R) hBR hbottom hA hAB
  rw [hcover] at hf hinj hmap hboundary
  have hfixA : _root_.Set.EqOn f id A := hfix.mono _root_.Set.subset_union_left
  refine ⟨f, isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn (isPolyhedron_space K) hf
    ⟨mapsTo_image _ _, hinj, _root_.Set.surjOn_image _ _⟩, hmap, hfixA, hboundary, ?_⟩
  apply Subset.antisymm
  · rintro y ⟨⟨x, hx, rfl⟩, hyB⟩
    have hxA := (hboundary x hx).mp hyB
    rwa [hfixA hxA]
  · intro x hx
    exact ⟨⟨x, boundaryComplex_space_subset 3 K (hAB hx), hfixA hx⟩, hAB hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_inward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_inward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_inward ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_inward

open _root_.Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_eqOn_preimage_boundary
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {P C : Set F} (hP : IsPolyhedron P) (hC : IsPolyhedron C) (hCP : C ⊆ P)
    {f : F → E} (hf : IsPiecewiseAffineOn f P) (hinj : _root_.Set.InjOn f P)
    (hmap : _root_.Set.MapsTo f P K.space) (hboundary : _root_.Set.MapsTo f C (boundaryComplex 3 K).space) :
    ∃ g : F → E, IsPLHomeomorphOn g P (g '' P) ∧ _root_.Set.MapsTo g P K.space ∧ _root_.Set.EqOn g f C ∧
      P ∩ g ⁻¹' (boundaryComplex 3 K).space = C ∧
      g '' P ∩ (boundaryComplex 3 K).space = f '' C := by
  have hA : IsPolyhedron (f '' C) := hC.image_of_isPiecewiseAffineOn
    (hf.mono_of_isPolyhedron hC hCP) (hinj.mono hCP)
  obtain ⟨q, hq, hqmap, hqfix, hqboundary, -⟩ :=
    hK.exists_isPLHomeomorphOn_inward K hA (image_subset_iff.mpr hboundary)
  have hg : IsPiecewiseAffineOn (q ∘ f) P := by
    have h := hq.isPiecewiseAffineOn.comp hf
    have hinter : P ∩ f ⁻¹' K.space = P := inter_eq_left.mpr hmap
    rwa [hinter] at h
  have hginj : _root_.Set.InjOn (q ∘ f) P := hq.bijOn.injOn.comp hinj hmap
  have hfix : _root_.Set.EqOn (q ∘ f) f C := fun x hx => hqfix ⟨x, hx, rfl⟩
  have hpre : P ∩ (q ∘ f) ⁻¹' (boundaryComplex 3 K).space = C := by
    apply Subset.antisymm
    · rintro x ⟨hxP, hxB⟩
      obtain ⟨y, hy, hxy⟩ := (hqboundary _ (hmap hxP)).mp hxB
      exact hinj (hCP hy) hxP hxy ▸ hy
    · intro x hx
      refine ⟨hCP hx, ?_⟩
      change (q ∘ f) x ∈ (boundaryComplex 3 K).space
      rw [hfix hx]
      exact hboundary hx
  refine ⟨q ∘ f, isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP hg
    ⟨mapsTo_image _ _, hginj, _root_.Set.surjOn_image _ _⟩, hqmap.comp hmap, hfix, hpre, ?_⟩
  apply Subset.antisymm
  · rintro y ⟨⟨x, hxP, rfl⟩, hxB⟩
    have hxC := hpre.subset ⟨hxP, hxB⟩
    exact ⟨x, hxC, (hfix hxC).symm⟩
  · rintro y ⟨x, hxC, rfl⟩
    exact ⟨⟨x, hCP hxC, hfix hxC⟩, hboundary hxC⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_eqOn_preimage_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_eqOn_preimage_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_eqOn_preimage_boundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_eqOn_preimage_boundary

open _root_.Classical in
theorem IsPLHomeomorphOn.exists_piecewiseAffineOn_relative_inward
    {B W R : Set E} {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (B ×ˢ _root_.Set.Icc (0 : ℝ) 1) W)
    (hW : IsPolyhedron W) (hR : IsPolyhedron R) (hBR : Disjoint B R)
    (hbottom : ∀ x ∈ B, ρ (x, 0) = x)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {P A : Set F} (hP : IsPolyhedron P) (hA : IsPolyhedron A) (hAP : A ⊆ P)
    {f : F → E} (hf : IsPiecewiseAffineOn f P) (hmap : _root_.Set.MapsTo f P (W ∪ R))
    (hboundary : _root_.Set.MapsTo f A B) :
    ∃ g : F → E, IsPiecewiseAffineOn g P ∧ _root_.Set.MapsTo g P (W ∪ R) ∧ _root_.Set.EqOn g f A ∧
      P ∩ g ⁻¹' B = A := by
  let U := B ×ˢ _root_.Set.Icc (0 : ℝ) 1
  let τ := Function.invFunOn ρ U
  have hτ : _root_.Set.MapsTo τ W U := hρ.symm.bijOn.mapsTo
  have hright : _root_.Set.RightInvOn τ ρ W := hρ.bijOn.invOn_invFunOn.2
  have hBW : B ⊆ W := fun x hx =>
    hbottom x hx ▸ hρ.bijOn.mapsTo ⟨hx, le_rfl, zero_le_one⟩
  have hzero : ∀ z ∈ U, ρ z ∈ B ↔ z.2 = 0 := by
    intro z hz
    constructor
    · intro hB
      exact congrArg Prod.snd (hρ.bijOn.injOn hz
        ⟨hB, le_rfl, zero_le_one⟩ (hbottom _ hB).symm)
    · intro ht
      rw [show z = (z.1, 0) from Prod.ext rfl ht, hbottom _ hz.1]
      exact hz.1
  have hheight : ∀ x ∈ W ∩ R, 0 < (τ x).2 := by
    intro x hx
    have hne : (τ x).2 ≠ 0 := by
      intro ht
      have hxB : x ∈ B := by
        rw [← hright hx.1]
        exact (hzero _ (hτ hx.1)).mpr ht
      exact Set.disjoint_left.mp hBR hxB hx.2
    exact lt_of_le_of_ne (hτ hx.1).2.1 hne.symm
  obtain ⟨r, hr, hrheight⟩ : ∃ r : ℝ, 0 < r ∧ ∀ x ∈ W ∩ R, r ≤ (τ x).2 := by
    by_cases hne : (W ∩ R).Nonempty
    · obtain ⟨x, hx, hmin⟩ := (hW.isCompact.inter_right hR.isClosed).exists_isMinOn hne
        (hρ.isPiecewiseAffineOn_invFunOn.continuousOn.snd.mono _root_.Set.inter_subset_left)
      exact ⟨(τ x).2, hheight x hx, fun y hy => hmin hy⟩
    · exact ⟨1, zero_lt_one, fun x hx => False.elim (hne ⟨x, hx⟩)⟩
  let a := _root_.Min.min r 1
  have ha : 0 < a := lt_min hr zero_lt_one
  have haone : a ≤ 1 := min_le_right _ _
  have hthin : ∀ x ∈ W ∩ R, a ≤ (τ x).2 := fun x hx => (min_le_left _ _).trans (hrheight x hx)
  obtain ⟨b, hb, hbpos, hbzero⟩ := hA.exists_nonneg_piecewiseAffine_zero_set
  let PW := P ∩ f ⁻¹' W
  let PR := P ∩ f ⁻¹' R
  have hPW : IsPolyhedron PW := hf.isPolyhedron_inter_preimage_of_isPolyhedron hP hW
  have hPR : IsPolyhedron PR := hf.isPolyhedron_inter_preimage_of_isPolyhedron hP hR
  have hcover : PW ∪ PR = P := by
    apply Subset.antisymm (_root_.Set.union_subset _root_.Set.inter_subset_left _root_.Set.inter_subset_left)
    intro x hx
    rcases hmap hx with hxW | hxR
    · exact Or.inl ⟨hx, hxW⟩
    · exact Or.inr ⟨hx, hxR⟩
  let H : F → E × ℝ := fun x => collarInwardMap (fun _ : E => b x) a (τ (f x))
  have hHU : _root_.Set.MapsTo H PW U := fun x hx =>
    collarInwardMap_mapsTo_prod_Icc (fun _ : E => b x) haone B (hτ hx.2)
  have hτf : IsPiecewiseAffineOn (τ ∘ f) PW := by
    have h := hρ.isPiecewiseAffineOn_invFunOn.comp (hf.mono_of_isPolyhedron hPW _root_.Set.inter_subset_left)
    have heq : PW ∩ f ⁻¹' W = PW := inter_eq_left.mpr _root_.Set.inter_subset_right
    rwa [heq] at h
  have hfst : IsPiecewiseAffineOn (fun x => (τ (f x)).1) PW :=
    hτf.affine_comp (LinearMap.fst ℝ E ℝ).toAffineMap
  have hsnd : IsPiecewiseAffineOn (fun x => (τ (f x)).2) PW :=
    hτf.affine_comp (LinearMap.snd ℝ E ℝ).toAffineMap
  have hhalf : IsPiecewiseAffineOn (fun x => ((τ (f x)).2 + a) / 2) PW := by
    let c : ℝ →ᵃ[ℝ] ℝ := (1 / 2 : ℝ) • (AffineMap.id ℝ ℝ + AffineMap.const ℝ ℝ a)
    convert hsnd.affine_comp c using 1
    ext x
    change ((τ (f x)).2 + a) / 2 = (1 / 2 : ℝ) * ((τ (f x)).2 + a)
    ring
  have hH : IsPiecewiseAffineOn H PW :=
    hfst.prod_mk (hsnd.max
      ((hsnd.add (hb.mono_of_isPolyhedron hPW (_root_.Set.subset_univ _))).min hhalf))
  let Q := ρ ∘ H
  have hQ : IsPiecewiseAffineOn Q PW := by
    have h := hρ.isPiecewiseAffineOn.comp hH
    have heq : PW ∩ H ⁻¹' U = PW := inter_eq_left.mpr hHU
    rwa [heq] at h
  have hQmap : _root_.Set.MapsTo Q PW W := hρ.bijOn.mapsTo.comp hHU
  have hQA : _root_.Set.EqOn Q f A := by
    intro x hx
    change ρ (collarInwardMap (fun _ : E => b x) a (τ (f x))) = f x
    rw [collarInwardMap_eq_self_of_eq_zero a ((hbzero x).mpr hx)]
    exact hright (hBW (hboundary hx))
  have hQR : _root_.Set.EqOn Q f (PW ∩ PR) := by
    intro x hx
    change ρ (collarInwardMap (fun _ : E => b x) a (τ (f x))) = f x
    rw [collarInwardMap_eq_self_of_le _ (hthin (f x) ⟨hx.1.2, hx.2.2⟩)]
    exact hright hx.1.2
  have hQB : ∀ x ∈ PW, Q x ∈ B ↔ x ∈ A := by
    intro x hx
    constructor
    · intro hQx
      have ht := (hzero _ (hHU hx)).mp hQx
      have hb0 := ((collarInwardMap_snd_eq_zero_iff ha (hbpos x) (hτ hx.2).2.1).mp ht).2
      exact (hbzero x).mp hb0
    · intro hxA
      rw [hQA hxA]
      exact hboundary hxA
  let g := PW.piecewise Q f
  have hgPW : _root_.Set.EqOn g Q PW := PW.piecewise_eqOn Q f
  have hgPR : _root_.Set.EqOn g f PR := by
    intro x hx
    by_cases hxW : x ∈ PW
    · rw [hgPW hxW]
      exact hQR ⟨hxW, hx⟩
    · exact _root_.Set.piecewise_eq_of_notMem PW Q f hxW
  have hg : IsPiecewiseAffineOn g P := by
    have h := (hQ.congr hgPW).union_of_isClosed
      ((hf.mono_of_isPolyhedron hPR _root_.Set.inter_subset_left).congr hgPR) hPW.isClosed hPR.isClosed
    rwa [hcover] at h
  have hgA : _root_.Set.EqOn g f A := by
    intro x hx
    rw [hgPW ⟨hAP hx, hBW (hboundary hx)⟩]
    exact hQA hx
  refine ⟨g, hg, ?_, hgA, ?_⟩
  · intro x hx
    have hxcover : x ∈ PW ∪ PR := hcover.symm ▸ hx
    rcases hxcover with hxW | hxR
    · rw [hgPW hxW]
      exact Or.inl (hQmap hxW)
    · rw [hgPR hxR]
      exact Or.inr hxR.2
  · apply Subset.antisymm
    · rintro x ⟨hxP, hxB⟩
      change g x ∈ B at hxB
      by_cases hxW : x ∈ PW
      · rw [hgPW hxW] at hxB
        exact (hQB x hxW).mp hxB
      · have hxR : x ∈ PR := (show x ∈ PW ∪ PR from hcover.symm ▸ hxP).resolve_left hxW
        rw [hgPR hxR] at hxB
        exact (Set.disjoint_left.mp hBR hxB hxR.2).elim
    · intro x hx
      refine ⟨hAP hx, ?_⟩
      change g x ∈ B
      rw [hgA hx]
      exact hboundary hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_piecewiseAffineOn_relative_inward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_piecewiseAffineOn_relative_inward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_piecewiseAffineOn_relative_inward ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_piecewiseAffineOn_relative_inward

open _root_.Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPiecewiseAffineOn_eqOn_preimage_boundary
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {P C : Set F} (hP : IsPolyhedron P) (hC : IsPolyhedron C) (hCP : C ⊆ P)
    {f : F → E} (hf : IsPiecewiseAffineOn f P)
    (hmap : _root_.Set.MapsTo f P K.space) (hboundary : _root_.Set.MapsTo f C (boundaryComplex 3 K).space) :
    ∃ g : F → E, IsPiecewiseAffineOn g P ∧ _root_.Set.MapsTo g P K.space ∧ _root_.Set.EqOn g f C ∧
      P ∩ g ⁻¹' (boundaryComplex 3 K).space = C ∧
      g '' P ∩ (boundaryComplex 3 K).space = f '' C := by
  let B := boundaryComplex 3 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hB := (isCombinatorialManifold_boundaryComplex K hK).isCombinatorialManifoldWithBoundary
  obtain ⟨W, ρ, R, hW, hWK, hρ, hbottom, -, -, hRfinite, -, hRspace, -, -⟩ :=
    hK.exists_isPLHomeomorphOn_surface_prod_Icc K B hB Subset.rfl
      (a := 0) (b := 1) (by norm_num)
  let _ : Finite R.faces := hRfinite.to_subtype
  have hnhds := hρ.mem_nhdsSetWithin_boundaryComplex K hK (by norm_num) hWK hbottom
  obtain ⟨O, hO, hBO, hOW⟩ := mem_nhdsSetWithin.mp hnhds
  have hKR : K.space \ W ⊆ Oᶜ := by
    rintro x ⟨hxK, hxW⟩ hxO
    exact hxW (hOW ⟨hxO, hxK⟩)
  have hRO : R.space ⊆ Oᶜ := by
    rw [hRspace]
    exact closure_minimal hKR hO.isClosed_compl
  have hBR : Disjoint B.space R.space :=
    Set.disjoint_left.mpr fun x hxB hxR => hRO hxR (hBO hxB)
  have hRK : R.space ⊆ K.space := by
    rw [hRspace]
    exact closure_minimal _root_.Set.sdiff_subset (isPolyhedron_space K).isClosed
  have hcover : W ∪ R.space = K.space := by
    apply Subset.antisymm (_root_.Set.union_subset hWK hRK)
    intro x hx
    by_cases hxW : x ∈ W
    · exact Or.inl hxW
    · exact Or.inr (hRspace.symm ▸ subset_closure ⟨hx, hxW⟩)
  have hmap' : _root_.Set.MapsTo f P (W ∪ R.space) := hcover.symm ▸ hmap
  obtain ⟨g, hg, hgmap, hgfix, hgpre⟩ :=
    hρ.exists_piecewiseAffineOn_relative_inward hW (isPolyhedron_space R) hBR hbottom
      hP hC hCP hf hmap' hboundary
  rw [hcover] at hgmap
  refine ⟨g, hg, hgmap, hgfix, hgpre, ?_⟩
  apply Subset.antisymm
  · rintro y ⟨⟨x, hxP, rfl⟩, hxB⟩
    have hxC := hgpre.subset ⟨hxP, hxB⟩
    exact ⟨x, hxC, (hgfix hxC).symm⟩
  · rintro y ⟨x, hxC, rfl⟩
    exact ⟨⟨x, hCP hxC, hgfix hxC⟩, hboundary hxC⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isPiecewiseAffineOn_eqOn_preimage_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isPiecewiseAffineOn_eqOn_preimage_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isPiecewiseAffineOn_eqOn_preimage_boundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isPiecewiseAffineOn_eqOn_preimage_boundary

end DifferentialGeometry.Topology.PiecewiseLinear
