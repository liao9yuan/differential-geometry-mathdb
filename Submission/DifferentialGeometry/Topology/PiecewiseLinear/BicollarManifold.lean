/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Bicollar
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PieceParametrization
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ExhaustionGeneral
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open _root_.Classical in
theorem PLPieceIn.exists_bicollar_of_subset_interior {S Y : Set X}
    (T : PLPieceIn E 3 X S) (P : PLPieceIn F 3 X Y)
    (hT : IsCombinatorialManifold 2 T.complex)
    (hP : IsCombinatorialManifoldWithBoundary 3 P.complex)
    (hSY : S ⊆ interior Y) (htwo : Topology.IsTwoSided S) :
    ∃ (W : Set X) (C : PLPieceIn (E × ℝ) 3 X W), W ⊆ interior Y ∧ W ∈ 𝓝ˢ S ∧
      C.complex.space = T.complex.space ×ˢ _root_.Set.Icc (-1 : ℝ) 1 ∧
      ∀ x ∈ T.complex.space, C.map (x, 0) = T.map x := by
  classical
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  let _ : Finite P.complex.faces := P.finite_faces.to_subtype
  let g := Function.invFunOn P.map P.complex.space ∘ T.map
  have hg : IsPLHomeomorphOn g T.complex.space (P.complex.space ∩ P.map ⁻¹' S) :=
    T.isPLHomeomorphOn_transition_of_subset P (hSY.trans interior_subset)
  have hQ : IsPolyhedron (P.complex.space ∩ P.map ⁻¹' S) := by
    rw [← hg.image_eq]
    exact T.isPolyhedron_space.image_of_isPiecewiseAffineOn hg.isPiecewiseAffineOn hg.bijOn.injOn
  obtain ⟨L, hLfin, hLspace⟩ := hQ.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hgL : IsPLHomeomorphOn g T.complex.space L.space := by
    rw [hLspace]
    exact hg
  have hL : IsCombinatorialManifold 2 L := hT.of_isPLHomeomorphOn hgL
  have hLP : L.space ⊆ P.complex.space := hLspace.subset.trans _root_.Set.inter_subset_left
  have hLS : _root_.Set.MapsTo P.map L.space S := fun _ hx => (hLspace.subset hx).2
  have hBd : Disjoint L.space (boundaryComplex 3 P.complex).space := by
    apply disjoint_left.mpr
    intro x hx
    exact (P.mem_interior_iff_not_mem_boundaryComplex_space hP (hLP hx)).mp (hSY (hLS hx))
  have hrange : _root_.Set.range (fun x : P.complex.space => P.map x) = Y := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact P.bijOn.mapsTo x.2
    · intro hy
      obtain ⟨x, hx, rfl⟩ := P.bijOn.surjOn hy
      exact ⟨⟨x, hx⟩, rfl⟩
  have htwoP := htwo.preimage_of_isInducing P.isClosedEmbedding.isEmbedding.isInducing
    (show _root_.Set.range (fun x : P.complex.space => P.map x) ∈ 𝓝ˢ S by
      rw [hrange]
      exact subset_interior_iff_mem_nhdsSet.mp hSY)
  have hpre : ((↑) : P.complex.space → F) ⁻¹' L.space =
      (fun x : P.complex.space => P.map x) ⁻¹' S := by
    ext x
    change (x : F) ∈ L.space ↔ P.map x ∈ S
    rw [hLspace]
    exact and_iff_right x.2
  rw [← hpre] at htwoP
  obtain ⟨A, ρ, hA, hAint, -, hAnhds, hρ, hcenter⟩ :=
    hP.exists_bicollar hL hLP hBd htwoP (U := _root_.Set.univ) Filter.univ_mem
  obtain ⟨B, hBspace, hBmap⟩ := P.exists_restrict_of_isPolyhedron hA
    (hAint.trans _root_.Set.sdiff_subset)
  have hprod := hgL.prodMap (isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id
    (P := _root_.Set.Icc (-1 : ℝ) 1))
  have hcombined := hprod.trans hρ
  obtain ⟨J, hJfin, hJspace⟩ :=
    (T.isPolyhedron_space.prod (isHPolytope_Icc (a := (-1 : ℝ)) (b :=
        1)).isPolyhedron).exists_simplicialComplex
  have hparam : IsPLHomeomorphOn (ρ ∘ Prod.map g id) J.space B.complex.space := by
    rw [hJspace, hBspace]
    exact hcombined
  let C := B.precomp J hJfin hparam
  refine ⟨P.map '' A, C, ?_, ?_, hJspace, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    exact (P.mem_interior_iff_not_mem_boundaryComplex_space hP (hAint hx).1).mpr (hAint hx).2
  · apply mem_nhdsSet_iff_forall.mpr
    intro y hy
    obtain ⟨x, hx, rfl⟩ := P.bijOn.surjOn (interior_subset (hSY hy))
    have hxL : x ∈ L.space := hLspace.symm.subset ⟨hx, hy⟩
    obtain ⟨O, hO, hLO, hOA⟩ := mem_nhdsSetWithin.mp hAnhds
    exact P.image_mem_nhds_of_mem_nhds hx (mem_interior_iff_mem_nhds.mp (hSY hy))
      (mem_nhdsWithin.mpr ⟨O, hO, hLO hxL, hOA⟩)
  · intro x hx
    change B.map (ρ (g x, 0)) = T.map x
    rw [hBmap, hcenter (g x) (hgL.bijOn.mapsTo hx)]
    exact P.bijOn.invOn_invFunOn.2 (interior_subset (hSY (T.bijOn.mapsTo hx)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_bicollar_of_subset_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_bicollar_of_subset_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_bicollar_of_subset_interior ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_bicollar_of_subset_interior

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
open _root_.Classical in
theorem PLPieceIn.exists_bicollar [HasGroupoid X (plGroupoid 3)] {S U : Set X}
    (T : PLPieceIn E 3 X S) (hT : IsCombinatorialManifold 2 T.complex)
    (htwo : Topology.IsTwoSided S) (hU : U ∈ 𝓝ˢ S) :
    ∃ (W : Set X) (C : PLPieceIn (E × ℝ) 3 X W), W ⊆ U ∧ W ∈ 𝓝ˢ S ∧
      C.complex.space = T.complex.space ×ˢ _root_.Set.Icc (-1 : ℝ) 1 ∧
      ∀ x ∈ T.complex.space, C.map (x, 0) = T.map x := by
  let _ : Nonempty X := ⟨T.map 0⟩
  obtain ⟨O, hO, hSO, hOU⟩ := mem_nhdsSet_iff_exists.mp hU
  obtain ⟨Y, -, ⟨P, hP⟩, hSY, hYO⟩ :=
    PiecewiseLinear.exists_isPolyhedralManifoldWithBoundary_neighborhood (m := 2) T.isCompact hO hSO
  obtain ⟨W, C, hWY, hWS, hC, hcenter⟩ :=
    T.exists_bicollar_of_subset_interior P.piece hT hP hSY htwo
  exact ⟨W, C, hWY.trans (interior_subset.trans (hYO.trans hOU)), hWS, hC, hcenter⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_bicollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_bicollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_bicollar ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_bicollar

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
open _root_.Classical in
theorem PLPieceIn.exists_bicollar_homeomorph [HasGroupoid X (plGroupoid 3)] {S U : Set X}
    (T : PLPieceIn E 3 X S) (hT : IsCombinatorialManifold 2 T.complex)
    (htwo : Topology.IsTwoSided S) (hU : U ∈ 𝓝ˢ S) :
    ∃ (W : Set X) (C : PLPieceIn (E × ℝ) 3 X W) (ρ : S × _root_.Set.Icc (-1 : ℝ) 1 ≃ₜ W),
      W ⊆ U ∧ W ∈ 𝓝ˢ S ∧ C.complex.space = T.complex.space ×ˢ _root_.Set.Icc (-1 : ℝ) 1 ∧
      (∀ (x : T.complex.space) (t : _root_.Set.Icc (-1 : ℝ) 1),
        (ρ (⟨T.map x, T.bijOn.mapsTo x.2⟩, t) : X) = C.map (x, t)) ∧
      ∀ x : S, (ρ (x, ⟨0, by norm_num⟩) : X) = x := by
  obtain ⟨W, C, hWU, hWS, hC, hcenter⟩ := T.exists_bicollar hT htwo hU
  let ρ : S × _root_.Set.Icc (-1 : ℝ) 1 ≃ₜ W :=
    (T.homeomorph.symm.prodCongr (Homeomorph.refl _)).trans
      ((Homeomorph.Set.prod T.complex.space (_root_.Set.Icc (-1 : ℝ) 1)).symm.trans
        ((Homeomorph.setCongr hC.symm).trans C.homeomorph))
  refine ⟨W, C, ρ, hWU, hWS, hC, ?_, ?_⟩
  · intro x t
    change C.map ((T.homeomorph.symm (T.homeomorph x) : E), (t : ℝ)) = C.map (x, t)
    rw [T.homeomorph.symm_apply_apply]
  · intro x
    change C.map ((T.homeomorph.symm x : E), 0) = (x : X)
    rw [hcenter _ (T.homeomorph.symm x).2]
    exact congrArg Subtype.val (T.homeomorph.apply_symm_apply x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_bicollar_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_bicollar_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_bicollar_homeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.exists_bicollar_homeomorph

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
open _root_.Classical in
theorem IsPolyhedralManifold.exists_bicollar [HasGroupoid X (plGroupoid 3)] {S U : Set X}
    (hS : IsPolyhedralManifold (n := 3) 2 S) (htwo : Topology.IsTwoSided S) (hU : U ∈ 𝓝ˢ S) :
    ∃ (T : PLPiece 3 X S) (W : Set X)
      (C : PLPieceIn ((EuclideanSpace ℝ (Fin T.ambientDim)) × ℝ) 3 X W)
      (ρ : S × _root_.Set.Icc (-1 : ℝ) 1 ≃ₜ W),
      W ⊆ U ∧ W ∈ 𝓝ˢ S ∧ C.complex.space = T.piece.complex.space ×ˢ _root_.Set.Icc (-1 : ℝ) 1 ∧
      (∀ (x : T.piece.complex.space) (t : _root_.Set.Icc (-1 : ℝ) 1),
        (ρ (⟨T.piece.map x, T.piece.bijOn.mapsTo x.2⟩, t) : X) = C.map (x, t)) ∧
      ∀ x : S, (ρ (x, ⟨0, by norm_num⟩) : X) = x := by
  obtain ⟨T, hT⟩ := hS
  obtain ⟨W, C, ρ, hWU, hWS, hC, hρ, hcenter⟩ := T.piece.exists_bicollar_homeomorph hT htwo hU
  exact ⟨T, W, C, ρ, hWU, hWS, hC, hρ, hcenter⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_bicollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_bicollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_bicollar ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_bicollar
end DifferentialGeometry.Topology.PiecewiseLinear
