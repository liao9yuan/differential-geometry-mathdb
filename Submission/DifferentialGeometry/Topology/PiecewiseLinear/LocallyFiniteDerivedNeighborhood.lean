/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteGraphDualCells
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CutExhaustion
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexBallStar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {U : Set X}

theorem LocallyFinitePLPieceIn.isOpen_preimage_openStar
    (T : LocallyFinitePLPieceIn E 3 X U) (v : E) :
    IsOpen ((Subtype.val : T.complex.space → E) ⁻¹' openStar T.complex v) := by
  have heq : (Subtype.val : T.complex.space → E) ⁻¹' openStar T.complex v =
      ((Subtype.val : T.complex.space → E) ⁻¹' avoidingUnion T.complex v)ᶜ := by
    ext x
    exact ⟨fun hx => hx.2, fun hx => ⟨x.2, hx⟩⟩
  rw [heq]
  exact (T.isClosed_preimage_avoidingUnion v).isOpen_compl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isOpen_preimage_openStar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isOpen_preimage_openStar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isOpen_preimage_openStar ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isOpen_preimage_openStar

theorem LocallyFinitePLPieceIn.exists_finite_subcomplex_neighborhood
    (T : LocallyFinitePLPieceIn E 3 X U) {x : E} (hx : x ∈ T.complex.space) :
    ∃ S : Geometry.SimplicialComplex ℝ E, S.faces.Finite ∧ S.faces ⊆ T.complex.faces ∧
      S.space ∈ 𝓝[T.complex.space] x := by
  classical
  obtain ⟨v, hv, hxv⟩ := exists_vertex_mem_openStar T.complex hx
  refine ⟨starComplex T.complex v, T.starComplex_faces_finite hv,
    starComplex_faces_subset T.complex v, ?_⟩
  rw [starComplex_space T.complex v hv]
  have hpre : (Subtype.val : T.complex.space → E) ⁻¹' closedStar T.complex v ∈
      𝓝 (⟨x, hx⟩ : T.complex.space) :=
    Filter.mem_of_superset ((T.isOpen_preimage_openStar v).mem_nhds hxv)
      (_root_.Set.preimage_mono (openStar_subset_closedStar T.complex hv))
  exact preimage_coe_mem_nhds_subtype.mp hpre

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.exists_finite_subcomplex_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.exists_finite_subcomplex_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.exists_finite_subcomplex_neighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.exists_finite_subcomplex_neighborhood

open _root_.Classical in
theorem LocallyFinitePLPieceIn.derivedNeighborhood_mem_nhdsWithin
    (T : LocallyFinitePLPieceIn E 3 X U) {L : Geometry.SimplicialComplex ℝ E}
    (hL : L.faces ⊆ T.complex.faces) {x : E} (hx : x ∈ L.space) :
    (derivedNeighborhood T.complex L).space ∈ 𝓝[T.complex.space] x := by
  have hxT := space_mono_of_faces_subset hL hx
  obtain ⟨S, hfin, hS, hnbhd⟩ := T.exists_finite_subcomplex_neighborhood hxT
  let _ : Finite S.faces := hfin.to_subtype
  have hLS : (restrict L S.space).faces ⊆ S.faces := fun s hs =>
    ((mem_restrict_faces_iff_of_faces_subset T.complex L S hL hS).mp hs).2
  have hxS : x ∈ S.space := mem_of_mem_nhdsWithin hxT hnbhd
  have hxLS : x ∈ (restrict L S.space).space := by
    rw [restrict_space_eq_inter_of_faces_subset T.complex L S hL hS]
    exact ⟨hx, hxS⟩
  have hlocal := PiecewiseLinear.derivedNeighborhood_mem_nhdsWithin hLS hxLS
  have hmem := nhdsWithin_le_of_mem hnbhd hlocal
  exact Filter.mem_of_superset hmem (space_mono_of_faces_subset
    (derivedNeighborhood_faces_mono hS (restrict_faces_subset L S.space)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.derivedNeighborhood_mem_nhdsWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.derivedNeighborhood_mem_nhdsWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.derivedNeighborhood_mem_nhdsWithin ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.derivedNeighborhood_mem_nhdsWithin

open _root_.Classical in
theorem LocallyFinitePLPieceIn.image_derivedNeighborhood_mem_nhdsSet
    (T : LocallyFinitePLPieceIn E 3 X U) (hU : IsOpen U)
    {L : Geometry.SimplicialComplex ℝ E} (hL : L.faces ⊆ T.complex.faces) :
    T.map '' (derivedNeighborhood T.complex L).space ∈ nhdsSet (T.map '' L.space) := by
  apply mem_nhdsSet_iff_forall.mpr
  rintro _ ⟨x, hx, rfl⟩
  have hxT := space_mono_of_faces_subset hL hx
  have hpre : (Subtype.val : T.complex.space → E) ⁻¹'
      (derivedNeighborhood T.complex L).space ∈ 𝓝 (⟨x, hxT⟩ : T.complex.space) :=
    preimage_coe_mem_nhds_subtype.mpr (T.derivedNeighborhood_mem_nhdsWithin hL hx)
  have himage := T.isEmbedding.isInducing.image_mem_nhdsWithin hpre
  have hrange : _root_.Set.range (fun z : T.complex.space => T.map z) = U := by
    change _root_.Set.range (T.map ∘ (Subtype.val : T.complex.space → E)) = U
    rw [_root_.Set.range_comp, Subtype.range_coe, T.bijOn.image_eq]
  rw [hrange, nhdsWithin_eq_nhds.mpr (hU.mem_nhds (T.bijOn.mapsTo hxT))] at himage
  exact Filter.mem_of_superset himage (by rintro _ ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.image_derivedNeighborhood_mem_nhdsSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.image_derivedNeighborhood_mem_nhdsSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.image_derivedNeighborhood_mem_nhdsSet ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.image_derivedNeighborhood_mem_nhdsSet

end DifferentialGeometry.Topology.PiecewiseLinear
