/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CollarGluing
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDiskNeighborhood
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldComplement
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
private theorem exists_collar_extension_of_isPLBall_bottom_union_sides
    (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hK : IsPLBall 2 K.space) (hR : IsCombinatorialManifoldWithBoundary 3 R)
    {B P W U : Set E} (hP : IsPolyhedron P) (hKB : K.space ⊆ B)
    {a b : ℝ} (hab : a < b) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (P ×ˢ _root_.Set.Icc a b) W)
    (hbottom : ∀ x ∈ P, ρ (x, a) = x) (hWB : W ∩ B = P)
    (hmeet : K.space ∩ P ⊆ (boundaryComplex 2 K).space)
    (hpatch : IsPLBall 2 (K.space ×ˢ {a} ∪ (K.space ∩ P) ×ˢ _root_.Set.Icc a b))
    (hattach : K.space ∪ ρ '' ((K.space ∩ P) ×ˢ _root_.Set.Icc a b) ⊆ (boundaryComplex 3 R).space)
    (hWR : W ∩ R.space ⊆ (boundaryComplex 3 R).space)
    (hBR : B ∩ R.space ⊆ (boundaryComplex 3 R).space)
    (hU : U ∈ 𝓝ˢ[R.space] (K.space ∪ ρ '' ((K.space ∩ P) ×ˢ _root_.Set.Icc a b))) :
    ∃ (C : Set E) (σ : E × ℝ → E) (R' : Geometry.SimplicialComplex ℝ E),
      IsPLBall 3 C ∧ C ⊆ R.space ∧ C ⊆ U ∧
      IsPLHomeomorphOn σ ((P ∪ K.space) ×ˢ _root_.Set.Icc a b) (W ∪ C) ∧
      _root_.Set.EqOn σ ρ (P ×ˢ _root_.Set.Icc a b) ∧ (∀ x ∈ P ∪ K.space, σ (x, a) = x) ∧
      (W ∪ C) ∩ B = P ∪ K.space ∧
      _root_.Set.MapsTo σ ((P ∪ K.space) ×ˢ _root_.Set.Ioc a b) ((W ∪ C) \ B) ∧
      R'.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R' ∧
      R'.space = closure (R.space \ C) ∧
      (W ∪ C) ∩ R'.space ⊆ (boundaryComplex 3 R').space ∧
      B ∩ R'.space ⊆ (boundaryComplex 3 R').space ∧
      IsPLHomeomorphOn σ (K.space ×ˢ _root_.Set.Icc a b) C ∧
      C ∩ (boundaryComplex 3 R).space =
        σ '' (K.space ×ˢ {a} ∪ (K.space ∩ P) ×ˢ _root_.Set.Icc a b) ∧
      C ∩ B = K.space ∧ W ∩ C = ρ '' ((K.space ∩ P) ×ˢ _root_.Set.Icc a b) := by
  obtain ⟨g, hg, -, -⟩ := exists_isPLHomeomorphOn_bottom_union_collar_sides
    hP hK.isPolyhedron hKB hab hρ hbottom hWB
  have hmodified := hpatch.of_isPLHomeomorphOn hg
  obtain ⟨L, hLfin, hL, hLR, hLU, hLmeet, hattachL⟩ :=
    hR.exists_isPLBall_inter_boundaryComplex_eq_subset hmodified hattach hU
  let _ : Finite L.faces := hLfin.to_subtype
  obtain ⟨G, hG, hGb, hGs⟩ := exists_isPLHomeomorphOn_prism_eqOn_collar_sides_of_isPLBall
    K hK hP hKB hab hρ hbottom hWB hmeet hpatch L hL hattachL
  have hsideW : ρ '' ((K.space ∩ P) ×ˢ _root_.Set.Icc a b) ⊆ W :=
    (_root_.Set.image_mono (_root_.Set.prod_mono _root_.Set.inter_subset_right Subset.rfl)).trans hρ.image_eq.subset
  have hWL : W ∩ L.space = ρ '' ((K.space ∩ P) ×ˢ _root_.Set.Icc a b) := by
    apply Subset.antisymm
    · rintro x ⟨hxW, hxL⟩
      have hx := hLmeet.subset ⟨hxL, hWR ⟨hxW, hLR hxL⟩⟩
      rcases hx with hxK | hxside
      · have hxP : x ∈ P := hWB ▸ ⟨hxW, hKB hxK⟩
        exact ⟨(x, a), ⟨⟨hxK, hxP⟩, le_rfl, hab.le⟩, hbottom x hxP⟩
      · exact hxside
    · intro x hx
      exact ⟨hsideW hx, (hLmeet.symm.subset (Or.inr hx)).1⟩
  have hLB : L.space ∩ B = K.space := by
    apply Subset.antisymm
    · rintro x ⟨hxL, hxB⟩
      have hx := hLmeet.subset ⟨hxL, hBR ⟨hxB, hLR hxL⟩⟩
      rcases hx with hxK | hxside
      · exact hxK
      · obtain ⟨z, hz, hzx⟩ := hxside
        have hxP : x ∈ P := hWB ▸ ⟨hsideW ⟨z, hz, hzx⟩, hxB⟩
        have hzEq : z = (x, a) := hρ.bijOn.injOn ⟨hz.1.2, hz.2⟩
          ⟨hxP, le_rfl, hab.le⟩ (hzx.trans (hbottom x hxP).symm)
        simpa only [hzEq] using hz.1.1
    · intro x hx
      exact ⟨(hLmeet.symm.subset (Or.inl hx)).1, hKB hx⟩
  have hprodinter : (P ×ˢ _root_.Set.Icc a b) ∩ (K.space ×ˢ _root_.Set.Icc a b) =
      (K.space ∩ P) ×ˢ _root_.Set.Icc a b := by
    rw [← _root_.Set.inter_prod, _root_.Set.inter_comm P K.space]
  have hagree : _root_.Set.EqOn ρ G ((P ×ˢ _root_.Set.Icc a b) ∩ (K.space ×ˢ _root_.Set.Icc a b)) := by
    rw [hprodinter]
    exact hGs.symm
  have hsurj : _root_.Set.SurjOn ρ ((P ×ˢ _root_.Set.Icc a b) ∩ (K.space ×ˢ _root_.Set.Icc a b)) (W ∩ L.space) := by
    rw [hprodinter, hWL]
    rintro y ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  have hI := (isPLBall_Icc hab).isPolyhedron
  obtain ⟨σ, hσ, hσρ, hσG⟩ := exists_isPLHomeomorphOn_union
    (hP.prod hI) (hK.isPolyhedron.prod hI) hρ hG hagree hsurj
  rw [← _root_.Set.union_prod] at hσ
  have hbase : ∀ x ∈ P ∪ K.space, σ (x, a) = x := by
    intro x hx
    rcases hx with hx | hx
    · exact (hσρ ⟨hx, le_rfl, hab.le⟩).trans (hbottom x hx)
    · exact (hσG ⟨hx, le_rfl, hab.le⟩).trans (hGb ⟨hx, rfl⟩)
  have htrace : (W ∪ L.space) ∩ B = P ∪ K.space := by
    rw [_root_.Set.union_inter_distrib_right, hWB, hLB]
  have hpositive : _root_.Set.MapsTo σ ((P ∪ K.space) ×ˢ _root_.Set.Ioc a b) ((W ∪ L.space) \ B) := by
    intro z hz
    have hzW := hσ.bijOn.mapsTo ⟨hz.1, hz.2.1.le, hz.2.2⟩
    refine ⟨hzW, ?_⟩
    intro hzB
    have hxbase : σ z ∈ P ∪ K.space := htrace ▸ ⟨hzW, hzB⟩
    have heq : z = (σ z, a) := hσ.bijOn.injOn ⟨hz.1, hz.2.1.le, hz.2.2⟩
      ⟨hxbase, le_rfl, hab.le⟩ (hbase (σ z) hxbase).symm
    exact hz.2.1.ne' (congrArg Prod.snd heq)
  have hLdisk : IsPLBall 2 (L.space ∩ (boundaryComplex 3 R).space) :=
    hLmeet.symm ▸ hmodified
  obtain ⟨R', hR'fin, hR', hR'space⟩ :=
    hR.exists_isCombinatorialManifoldWithBoundary_closure_sdiff hL hLR hLdisk
  let _ : Finite R'.faces := hR'fin.to_subtype
  have hR'sub : R'.space ⊆ R.space := by
    rw [hR'space]
    exact closure_minimal _root_.Set.sdiff_subset (isPolyhedron_space R).isClosed
  have hboundary := inter_boundaryComplex_space_subset_of_subset R R' hR hR' hR'sub
  have hLR' := inter_space_complement_subset_boundaryComplex R L R' hR
    hL.isCombinatorialManifoldWithBoundary hLR hR' hR'space
  have hWR' : (W ∪ L.space) ∩ R'.space ⊆ (boundaryComplex 3 R').space := by
    rintro x ⟨hxW | hxL, hxR'⟩
    · exact hboundary ⟨hxR', hWR ⟨hxW, hR'sub hxR'⟩⟩
    · exact hLR' ⟨hxL, hxR'⟩
  have hBR' : B ∩ R'.space ⊆ (boundaryComplex 3 R').space := by
    rintro x ⟨hxB, hxR'⟩
    exact hboundary ⟨hxR', hBR ⟨hxB, hR'sub hxR'⟩⟩
  have hbottomImage : σ '' (K.space ×ˢ {a}) = K.space := by
    apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      have heq : z = (z.1, a) := Prod.ext rfl hz.2
      rw [heq, hbase z.1 (Or.inr hz.1)]
      exact hz.1
    · intro x hx
      exact ⟨(x, a), ⟨hx, rfl⟩, hbase x (Or.inr hx)⟩
  have hsideImage : σ '' ((K.space ∩ P) ×ˢ _root_.Set.Icc a b) =
      ρ '' ((K.space ∩ P) ×ˢ _root_.Set.Icc a b) :=
    (hσρ.mono (_root_.Set.prod_mono _root_.Set.inter_subset_right Subset.rfl)).image_eq
  have hattachImage : L.space ∩ (boundaryComplex 3 R).space =
      σ '' (K.space ×ˢ {a} ∪ (K.space ∩ P) ×ˢ _root_.Set.Icc a b) := by
    rw [_root_.Set.image_union, hbottomImage, hsideImage]
    exact hLmeet
  exact ⟨L.space, σ, R', hL, hLR, hLU, hσ, hσρ, hbase, htrace, hpositive,
    hR'fin, hR', hR'space, hWR', hBR', hG.congr hσG, hattachImage, hLB, hWL⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_collar_extension_of_isPLBall_bottom_union_sides
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.exists_collar_extension_of_isPLBall_bottom_union_sides target :: scope.openDecls } }

open _root_.Classical in
theorem exists_collar_extension_of_boundary_arcs {ι : Type*}
    (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hK : IsPLBall 2 K.space) (hR : IsCombinatorialManifoldWithBoundary 3 R)
    {B P W U : Set E} (hP : IsPolyhedron P) (hKB : K.space ⊆ B)
    {a b : ℝ} (hab : a < b) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (P ×ˢ _root_.Set.Icc a b) W)
    (hbottom : ∀ x ∈ P, ρ (x, a) = x) (hWB : W ∩ B = P)
    (d : Finset ι) (A : ι → Set E) (hA : ∀ i ∈ d, IsPLBall 1 (A i))
    (hAB : ∀ i ∈ d, A i ⊆ (boundaryComplex 2 K).space)
    (hcover : (⋃ i ∈ d, A i) = K.space ∩ P)
    (hattach : K.space ∪ ρ '' ((K.space ∩ P) ×ˢ _root_.Set.Icc a b) ⊆ (boundaryComplex 3 R).space)
    (hWR : W ∩ R.space ⊆ (boundaryComplex 3 R).space)
    (hBR : B ∩ R.space ⊆ (boundaryComplex 3 R).space)
    (hU : U ∈ 𝓝ˢ[R.space] (K.space ∪ ρ '' ((K.space ∩ P) ×ˢ _root_.Set.Icc a b))) :
    ∃ (C : Set E) (σ : E × ℝ → E) (R' : Geometry.SimplicialComplex ℝ E),
      IsPLBall 3 C ∧ C ⊆ R.space ∧ C ⊆ U ∧
      IsPLHomeomorphOn σ ((P ∪ K.space) ×ˢ _root_.Set.Icc a b) (W ∪ C) ∧
      _root_.Set.EqOn σ ρ (P ×ˢ _root_.Set.Icc a b) ∧ (∀ x ∈ P ∪ K.space, σ (x, a) = x) ∧
      (W ∪ C) ∩ B = P ∪ K.space ∧
      _root_.Set.MapsTo σ ((P ∪ K.space) ×ˢ _root_.Set.Ioc a b) ((W ∪ C) \ B) ∧
      R'.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R' ∧
      R'.space = closure (R.space \ C) ∧
      (W ∪ C) ∩ R'.space ⊆ (boundaryComplex 3 R').space ∧
      B ∩ R'.space ⊆ (boundaryComplex 3 R').space ∧
      IsPLHomeomorphOn σ (K.space ×ˢ _root_.Set.Icc a b) C ∧
      C ∩ (boundaryComplex 3 R).space =
        σ '' (K.space ×ˢ {a} ∪ (K.space ∩ P) ×ˢ _root_.Set.Icc a b) ∧
      C ∩ B = K.space ∧ W ∩ C = ρ '' ((K.space ∩ P) ×ˢ _root_.Set.Icc a b) := by
  have hmeet : K.space ∩ P ⊆ (boundaryComplex 2 K).space := by
    rw [← hcover]
    exact _root_.Set.iUnion₂_subset hAB
  have hpatch := isPLBall_prism_bottom_union_strips K hK hab d A hA hAB
  rw [hcover] at hpatch
  exact exists_collar_extension_of_isPLBall_bottom_union_sides K R hK hR hP hKB hab
    hρ hbottom hWB hmeet hpatch hattach hWR hBR hU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_collar_extension_of_boundary_arcs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_collar_extension_of_boundary_arcs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_collar_extension_of_boundary_arcs ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_collar_extension_of_boundary_arcs

open _root_.Classical in
theorem exists_collar_extension_of_boundary
    (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite R.faces]
    (hK : IsPLBall 2 K.space) (hR : IsCombinatorialManifoldWithBoundary 3 R)
    {B P W U : Set E} (hP : IsPolyhedron P) (hKB : K.space ⊆ B)
    {a b : ℝ} (hab : a < b) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (P ×ˢ _root_.Set.Icc a b) W)
    (hbottom : ∀ x ∈ P, ρ (x, a) = x) (hWB : W ∩ B = P)
    (hmeet : K.space ∩ P = (boundaryComplex 2 K).space)
    (hattach : K.space ∪ ρ '' ((K.space ∩ P) ×ˢ _root_.Set.Icc a b) ⊆ (boundaryComplex 3 R).space)
    (hWR : W ∩ R.space ⊆ (boundaryComplex 3 R).space)
    (hBR : B ∩ R.space ⊆ (boundaryComplex 3 R).space)
    (hU : U ∈ 𝓝ˢ[R.space] (K.space ∪ ρ '' ((K.space ∩ P) ×ˢ _root_.Set.Icc a b))) :
    ∃ (C : Set E) (σ : E × ℝ → E) (R' : Geometry.SimplicialComplex ℝ E),
      IsPLBall 3 C ∧ C ⊆ R.space ∧ C ⊆ U ∧
      IsPLHomeomorphOn σ ((P ∪ K.space) ×ˢ _root_.Set.Icc a b) (W ∪ C) ∧
      _root_.Set.EqOn σ ρ (P ×ˢ _root_.Set.Icc a b) ∧ (∀ x ∈ P ∪ K.space, σ (x, a) = x) ∧
      (W ∪ C) ∩ B = P ∪ K.space ∧
      _root_.Set.MapsTo σ ((P ∪ K.space) ×ˢ _root_.Set.Ioc a b) ((W ∪ C) \ B) ∧
      R'.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 R' ∧
      R'.space = closure (R.space \ C) ∧
      (W ∪ C) ∩ R'.space ⊆ (boundaryComplex 3 R').space ∧
      B ∩ R'.space ⊆ (boundaryComplex 3 R').space ∧
      IsPLHomeomorphOn σ (K.space ×ˢ _root_.Set.Icc a b) C ∧
      C ∩ (boundaryComplex 3 R).space =
        σ '' (K.space ×ˢ {a} ∪ (K.space ∩ P) ×ˢ _root_.Set.Icc a b) ∧
      C ∩ B = K.space ∧ W ∩ C = ρ '' ((K.space ∩ P) ×ˢ _root_.Set.Icc a b) := by
  have hpatch : IsPLBall 2 (K.space ×ˢ {a} ∪ (K.space ∩ P) ×ˢ _root_.Set.Icc a b) := by
    rw [hmeet]
    exact isPLBall_prism_bottom_union_side K hK hab
  exact exists_collar_extension_of_isPLBall_bottom_union_sides K R hK hR hP hKB hab
    hρ hbottom hWB hmeet.subset hpatch hattach hWR hBR hU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_collar_extension_of_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_collar_extension_of_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_collar_extension_of_boundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_collar_extension_of_boundary

end DifferentialGeometry.Topology.PiecewiseLinear
