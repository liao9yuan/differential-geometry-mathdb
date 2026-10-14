/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34PatchEnumeration
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34TetraCarriers
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteManifoldCofaces
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DiskBallNeighborhoodImage

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M}

omit [FiniteDimensional ℝ Ea] in
theorem LocallyFinitePLPieceIn.finite_simplexIndices_incident
    (K : LocallyFinitePLPieceIn Ea 3 M U) {s : Finset Ea} (hs : s.Nonempty) (n : ℕ) :
    {t : Section34SimplexIndex K n | Section34Incident s t.1}.Finite := by
  obtain ⟨p, hps⟩ := hs
  by_cases hp : p ∈ K.complex.space
  · have hfin : {r : K.complex.faces | p ∈ convexHull ℝ (r.1 : Set Ea)}.Finite := by
      simpa using K.locallyFinite.point_finite ⟨p, hp⟩
    let _ : Finite {r : K.complex.faces | p ∈ convexHull ℝ (r.1 : Set Ea)} := hfin.to_subtype
    let f : {t : Section34SimplexIndex K n | Section34Incident s t.1} →
        {r : K.complex.faces | p ∈ convexHull ℝ (r.1 : Set Ea)} :=
      fun t => ⟨⟨t.1.1, t.1.2.1⟩, t.2 hps⟩
    have hf : Function.Injective f := by
      intro t₁ t₂ h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun r => r.1.1) h
    let _ := Finite.of_injective f hf
    exact Set.toFinite _
  · have heq : {t : Section34SimplexIndex K n | Section34Incident s t.1} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact hp (K.complex.convexHull_subset_space t.2.1 (ht hps))
    rw [heq]
    exact _root_.Set.finite_empty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.finite_simplexIndices_incident then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.finite_simplexIndices_incident"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.finite_simplexIndices_incident ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.finite_simplexIndices_incident

theorem Section34CutFrame.exists_edgeIndex_of_vertex
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (w : Section34VertexIndex 𝒦 𝒦') :
    ∃ e : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ e.1 := by
  obtain ⟨t, hwt⟩ := hcut.exists_tetrahedron_of_subdivision_face w.2.1
  obtain ⟨m, _, eK, _, _, hwe, _⟩ := hcut.exists_patchEnum t hwt
  exact ⟨eK 0, hwe 0⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CutFrame.exists_edgeIndex_of_vertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CutFrame.exists_edgeIndex_of_vertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CutFrame.exists_edgeIndex_of_vertex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CutFrame.exists_edgeIndex_of_vertex

theorem Section34CutFrame.exists_tetra_pair_of_triangle
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (s : Section34SimplexIndex 𝒦 3) :
    ∃ t u : Section34SimplexIndex 𝒦 4, t ≠ u ∧
      Section34Incident s.1 t.1 ∧ Section34Incident s.1 u.1 := by
  classical
  have hlink := 𝒦.isPLSphere_geometricLink hcut.1 s.2.1 (k := 2) s.2.2 (by omega)
  have heq := geometricLink_space_eq_coface_vertices_of_card_le 𝒦.complex s.1
    (fun r hr _ => by simpa only [s.2.2] using 𝒦.card_le_four hcut.1 hr)
  obtain ⟨v, w, hvw, hpair⟩ := isPLSphere_zero_iff.mp hlink
  rw [heq] at hpair
  have hv : v ∉ s.1 ∧ _root_.Insert.insert v s.1 ∈ 𝒦.complex.faces :=
    hpair.symm.subset (_root_.Set.mem_insert v {w})
  have hw : w ∉ s.1 ∧ _root_.Insert.insert w s.1 ∈ 𝒦.complex.faces :=
    hpair.symm.subset (_root_.Set.mem_insert_of_mem v (_root_.Set.mem_singleton w))
  let t : Section34SimplexIndex 𝒦 4 :=
    ⟨insert v s.1, hv.2, by rw [Finset.card_insert_of_notMem hv.1, s.2.2]⟩
  let u : Section34SimplexIndex 𝒦 4 :=
    ⟨insert w s.1, hw.2, by rw [Finset.card_insert_of_notMem hw.1, s.2.2]⟩
  refine ⟨t, u, ?_, ?_, ?_⟩
  · intro htu
    have hvu : v ∈ _root_.Insert.insert w s.1 := by
      change v ∈ u.1
      rw [← htu]
      exact Finset.mem_insert_self v s.1
    exact hvw ((Finset.mem_insert.mp hvu).resolve_right hv.1)
  · exact (Finset.coe_subset.mpr (Finset.subset_insert v s.1)).trans (subset_convexHull ℝ _)
  · exact (Finset.coe_subset.mpr (Finset.subset_insert w s.1)).trans (subset_convexHull ℝ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CutFrame.exists_tetra_pair_of_triangle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CutFrame.exists_tetra_pair_of_triangle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CutFrame.exists_tetra_pair_of_triangle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CutFrame.exists_tetra_pair_of_triangle

end DifferentialGeometry.Topology.PiecewiseLinear
