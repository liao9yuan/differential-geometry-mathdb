import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BicollarBands

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isCombinatorialManifoldWithBoundary_surface_prism
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    (hL : IsCombinatorialManifoldWithBoundary 2 L) {a b : ℝ} (hab : a < b)
    (T : Geometry.SimplicialComplex ℝ (E × ℝ)) [Finite T.faces]
    (hT : T.space = L.space ×ˢ _root_.Set.Icc a b) :
    IsCombinatorialManifoldWithBoundary 3 T := by
  apply isCombinatorialManifoldWithBoundary_of_isPLBall_neighborhoods T
  intro p hp
  rw [hT] at hp ⊢
  obtain ⟨D, hD, hDL, hDnhds⟩ :=
    hL.exists_isPLBall_subset_of_mem_nhdsWithin hp.1 (U := _root_.Set.univ) Filter.univ_mem
  refine ⟨D ×ˢ _root_.Set.Icc a b, isPLBall_three_prod hD (isPLBall_Icc hab),
    _root_.Set.prod_mono (hDL.trans _root_.Set.inter_subset_left) subset_rfl, ?_⟩
  rw [show p = (p.1, p.2) from rfl, nhdsWithin_prod_eq]
  exact Filter.prod_mem_prod hDnhds self_mem_nhdsWithin

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialManifoldWithBoundary_surface_prism with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialManifoldWithBoundary_surface_prism"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialManifoldWithBoundary_surface_prism ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isCombinatorialManifoldWithBoundary_surface_prism

open _root_.Classical in
theorem boundaryComplex_space_surface_prism [d : DecidableEq (E × ℝ)]
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    (hL : IsCombinatorialManifoldWithBoundary 2 L) {a b : ℝ} (hab : a < b)
    (T : Geometry.SimplicialComplex ℝ (E × ℝ)) [Finite T.faces]
    (hT : T.space = L.space ×ˢ _root_.Set.Icc a b) :
    (boundaryComplex 3 T).space =
      L.space ×ˢ {a, b} ∪ (boundaryComplex 2 L).space ×ˢ _root_.Set.Icc a b := by
  have hd : d = fun x y => Classical.propDecidable (x = y) := Subsingleton.elim _ _
  subst hd
  let _ : DecidableEq (E × ℝ) := fun x y => Classical.propDecidable (x = y)
  have hTm := isCombinatorialManifoldWithBoundary_surface_prism hL hab T hT
  have key : ∀ y ∈ L.space, ∀ t ∈ _root_.Set.Icc a b,
      ((y, t) ∈ (boundaryComplex 3 T).space ↔
        (t = a ∨ t = b) ∨ y ∈ (boundaryComplex 2 L).space) := by
    intro y hy t ht
    obtain ⟨D, hD, hDL, hDnhds⟩ :=
      hL.exists_isPLBall_subset_of_mem_nhdsWithin hy (U := _root_.Set.univ) Filter.univ_mem
    have hDL' : D ⊆ L.space := hDL.trans _root_.Set.inter_subset_left
    have hyD : y ∈ D := mem_of_mem_nhdsWithin hy hDnhds
    obtain ⟨Dc, hDcfin, hDcspace⟩ := hD.isPolyhedron.exists_simplicialComplex
    let _ : Finite Dc.faces := hDcfin.to_subtype
    have hDc : IsPLBall 2 Dc.space := hDcspace.symm ▸ hD
    have hprism : IsPLBall 3 (D ×ˢ _root_.Set.Icc a b) := isPLBall_three_prod hD (isPLBall_Icc hab)
    obtain ⟨TD, hTDfin, hTDspace⟩ := hprism.isPolyhedron.exists_simplicialComplex
    let _ : Finite TD.faces := hTDfin.to_subtype
    have hTD : IsCombinatorialManifoldWithBoundary 3 TD :=
      IsPLBall.isCombinatorialManifoldWithBoundary (hTDspace.symm ▸ hprism)
    have hTDT : TD.space ⊆ T.space := by
      rw [hTDspace, hT]
      exact _root_.Set.prod_mono hDL' subset_rfl
    have hzTD : (y, t) ∈ TD.space := by
      rw [hTDspace]
      exact ⟨hyD, ht⟩
    have hnhds : TD.space ∈ 𝓝[T.space] (y, t) := by
      rw [hTDspace, hT, nhdsWithin_prod_eq]
      exact Filter.prod_mem_prod hDnhds self_mem_nhdsWithin
    have h1 := mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin
      T TD hTm hTD hTDT hzTD hnhds
    have h2 : (boundaryComplex 3 TD).space =
        Dc.space ×ˢ {a, b} ∪ (boundaryComplex 2 Dc).space ×ˢ _root_.Set.Icc a b :=
      boundaryComplex_space_prism Dc hDc hab TD (by rw [hTDspace, hDcspace])
    have hDcL : Dc.space ⊆ L.space := by rw [hDcspace]; exact hDL'
    have hyDc : y ∈ Dc.space := by rw [hDcspace]; exact hyD
    have hDcnhds : Dc.space ∈ 𝓝[L.space] y := by rw [hDcspace]; exact hDnhds
    have hyB := mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin
      L Dc hL hDc.isCombinatorialManifoldWithBoundary hDcL hyDc hDcnhds
    change (y, t) ∈ (boundaryComplex 3 TD).space ↔
      (y, t) ∈ (boundaryComplex 3 T).space at h1
    change y ∈ (boundaryComplex 2 Dc).space ↔ y ∈ (boundaryComplex 2 L).space at hyB
    rw [← h1, h2]
    simp only [_root_.Set.mem_union, _root_.Set.mem_prod, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff,
      hyDc, true_and, ht, and_true, hyB]
  ext ⟨y, t⟩
  constructor
  · intro h
    have hz := boundaryComplex_space_subset 3 T h
    rw [hT] at hz
    rcases (key y hz.1 t hz.2).mp h with ht | hy
    · exact Or.inl ⟨hz.1, ht⟩
    · exact Or.inr ⟨hy, hz.2⟩
  · rintro (⟨hy, ht⟩ | ⟨hy, ht⟩)
    · have htI : t ∈ _root_.Set.Icc a b := by
        rcases ht with rfl | rfl
        · exact ⟨le_rfl, hab.le⟩
        · exact ⟨hab.le, le_rfl⟩
      exact (key y hy t htI).mpr (Or.inl ht)
    · exact (key y (boundaryComplex_space_subset 2 L hy) t ht).mpr (Or.inr hy)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_surface_prism with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_surface_prism"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_surface_prism ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_surface_prism

end DifferentialGeometry.Topology.PiecewiseLinear
