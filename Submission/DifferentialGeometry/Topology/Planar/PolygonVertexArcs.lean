import Submission.DifferentialGeometry.Topology.Planar.PolygonVertexCharts
import Mathlib.Analysis.Convex.Segment
import Submission.DifferentialGeometry.Topology.Compactness.FiniteReplacement

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set

namespace Schoenflies.PrePolygon

variable {m : ℕ}

noncomputable def vertexArc (P : PrePolygon m) (i : ZMod (m + 3)) : Set Plane :=
  segment ℝ (midpoint ℝ (P.vertex (i - 1)) (P.vertex i)) (P.vertex i) ∪
    segment ℝ (P.vertex i) (midpoint ℝ (P.vertex i) (P.vertex (i + 1)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PrePolygon.vertexArc then
    throwError "Refusing to shadow existing declaration Schoenflies.PrePolygon.vertexArc"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PrePolygon.vertexArc ``Submission.Schoenflies.PrePolygon.vertexArc

theorem isCompact_vertexArc (P : PrePolygon m) (i : ZMod (m + 3)) :
    IsCompact (P.vertexArc i) :=
  (isCompact_segment _ _).union (isCompact_segment _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PrePolygon.isCompact_vertexArc then
    throwError "Refusing to shadow existing declaration Schoenflies.PrePolygon.isCompact_vertexArc"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PrePolygon.isCompact_vertexArc ``Submission.Schoenflies.PrePolygon.isCompact_vertexArc

theorem vertex_mem_vertexArc (P : PrePolygon m) (i : ZMod (m + 3)) :
    P.vertex i ∈ P.vertexArc i := Or.inl (right_mem_segment ℝ _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PrePolygon.vertex_mem_vertexArc then
    throwError "Refusing to shadow existing declaration Schoenflies.PrePolygon.vertex_mem_vertexArc"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PrePolygon.vertex_mem_vertexArc ``Submission.Schoenflies.PrePolygon.vertex_mem_vertexArc

theorem vertexArc_subset_incident_edges (P : PrePolygon m) (i : ZMod (m + 3)) :
    P.vertexArc i ⊆ P.edge (i - 1) ∪ P.edge i := by
  apply _root_.Set.union_subset_union
  · simpa only [edge, sub_add_cancel] using
      (convex_segment (P.vertex (i - 1)) (P.vertex i)).segment_subset
        (midpoint_mem_segment _ _) (right_mem_segment ℝ _ _)
  · exact (convex_segment (P.vertex i) (P.vertex (i + 1))).segment_subset
      (left_mem_segment ℝ _ _) (midpoint_mem_segment _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PrePolygon.vertexArc_subset_incident_edges then
    throwError "Refusing to shadow existing declaration Schoenflies.PrePolygon.vertexArc_subset_incident_edges"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PrePolygon.vertexArc_subset_incident_edges ``Submission.Schoenflies.PrePolygon.vertexArc_subset_incident_edges

theorem vertexArc_subset_carrier (P : PrePolygon m) (i : ZMod (m + 3)) :
    P.vertexArc i ⊆ P.carrier :=
  (P.vertexArc_subset_incident_edges i).trans
    (_root_.Set.union_subset (P.edge_subset_carrier _) (P.edge_subset_carrier _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PrePolygon.vertexArc_subset_carrier then
    throwError "Refusing to shadow existing declaration Schoenflies.PrePolygon.vertexArc_subset_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PrePolygon.vertexArc_subset_carrier ``Submission.Schoenflies.PrePolygon.vertexArc_subset_carrier

theorem vertex_mem_vertexArc_iff (P : PrePolygon m) (i j : ZMod (m + 3)) :
    P.vertex j ∈ P.vertexArc i ↔ j = i := by
  refine ⟨?_, fun h => h ▸ P.vertex_mem_vertexArc i⟩
  intro hj
  rcases hj with hj | hj
  · have hseg : P.vertex j ∈ P.edge (i - 1) := by
      simpa only [edge, sub_add_cancel] using
        (convex_segment (P.vertex (i - 1)) (P.vertex i)).segment_subset
          (midpoint_mem_segment _ _) (right_mem_segment ℝ _ _) hj
    rcases vertex_mem_edge_elim hseg with he | he
    · have hne : P.vertex (i - 1) ≠ P.vertex i := by
        simpa only [sub_add_cancel] using P.vertex_ne_succ (i - 1)
      exact False.elim (left_notMem_right_half hne (midpoint_mem_openSegment _ _) (he ▸ hj))
    · exact P.vertex_inj (by simpa only [sub_add_cancel, _root_.Set.mem_singleton_iff] using he)
  · have hseg : P.vertex j ∈ P.edge i :=
      (convex_segment (P.vertex i) (P.vertex (i + 1))).segment_subset
        (left_mem_segment ℝ _ _) (midpoint_mem_segment _ _) hj
    rcases vertex_mem_edge_elim hseg with he | he
    · exact P.vertex_inj he
    · exact False.elim (right_notMem_left_half (P.vertex_ne_succ i)
        (midpoint_mem_openSegment _ _) (he ▸ hj))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PrePolygon.vertex_mem_vertexArc_iff then
    throwError "Refusing to shadow existing declaration Schoenflies.PrePolygon.vertex_mem_vertexArc_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PrePolygon.vertex_mem_vertexArc_iff ``Submission.Schoenflies.PrePolygon.vertex_mem_vertexArc_iff

theorem iUnion_vertexArc (P : PrePolygon m) : (⋃ i, P.vertexArc i) = P.carrier := by
  apply Subset.antisymm
  · exact _root_.Set.iUnion_subset (P.vertexArc_subset_carrier)
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    change p ∈ segment ℝ (P.vertex i) (P.vertex (i + 1)) at hi
    rw [segment_split (midpoint_mem_segment _ _)] at hi
    rcases hi with hi | hi
    · exact mem_iUnion.mpr ⟨i, Or.inr hi⟩
    · exact mem_iUnion.mpr ⟨i + 1, Or.inl (by simpa only [add_sub_cancel_right] using hi)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PrePolygon.iUnion_vertexArc then
    throwError "Refusing to shadow existing declaration Schoenflies.PrePolygon.iUnion_vertexArc"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PrePolygon.iUnion_vertexArc ``Submission.Schoenflies.PrePolygon.iUnion_vertexArc

theorem affine_image_vertexArc (P : PrePolygon m) (i : ZMod (m + 3))
    (e : Plane ≃ᵃ[ℝ] Plane) {r d : ℝ} (hr : 0 < r)
    (ha : e (P.vertex (i - 1)) = Plane.mk (-1) 0)
    (hp : e (P.vertex i) = 0)
    (hb : e (P.vertex (i + 1)) = Plane.mk r (d * r)) :
    e '' P.vertexArc i = {q : Plane | q 0 ∈ _root_.Set.Icc (-(1 / 2 : ℝ)) (r / 2) ∧
      q 1 = d * _root_.Max.max (q 0) 0} := by
  have heleft : e (midpoint ℝ (P.vertex (i - 1)) (P.vertex i)) =
      Plane.mk (-(1 / 2 : ℝ)) 0 := by
    rw [e.map_midpoint, ha, hp]
    ext j
    fin_cases j <;> norm_num [midpoint, AffineMap.lineMap_apply_module, Plane.mk, PiLp.add_apply]
  have heright : e (midpoint ℝ (P.vertex i) (P.vertex (i + 1))) =
      Plane.mk (r / 2) (d * (r / 2)) := by
    rw [e.map_midpoint, hp, hb]
    ext j
    fin_cases j <;> simp [midpoint, AffineMap.lineMap_apply_module, Plane.mk] <;> ring
  rw [vertexArc, _root_.Set.image_union]
  change e.toAffineMap '' _ ∪ e.toAffineMap '' _ = _
  rw [image_segment ℝ e.toAffineMap, image_segment ℝ e.toAffineMap]
  change segment ℝ (e (midpoint ℝ (P.vertex (i - 1)) (P.vertex i))) (e (P.vertex i)) ∪
    segment ℝ (e (P.vertex i)) (e (midpoint ℝ (P.vertex i) (P.vertex (i + 1)))) = _
  rw [heleft, heright, hp]
  ext q
  have hzero : Plane.mk 0 0 = 0 := by ext j; fin_cases j <;> rfl
  simpa only [hzero, _root_.Set.mem_ofPred_eq] using
    (mem_union_segments_iff_max (a := (1 / 2 : ℝ)) (r := r / 2) (d := d) (p := q)
      (by norm_num) (half_pos hr))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PrePolygon.affine_image_vertexArc then
    throwError "Refusing to shadow existing declaration Schoenflies.PrePolygon.affine_image_vertexArc"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PrePolygon.affine_image_vertexArc ``Submission.Schoenflies.PrePolygon.affine_image_vertexArc

theorem exists_disjoint_open_vertexArc_neighborhoods (P : PrePolygon m)
    (O : ZMod (m + 3) → Set Plane) (hO : ∀ i, IsOpen (O i))
    (hiO : ∀ i, P.vertex i ∈ O i) :
    ∃ U : ZMod (m + 3) → Set Plane,
      (∀ i, IsOpen (U i) ∧ P.vertex i ∈ U i ∧ U i ⊆ O i) ∧
      (Pairwise fun i j => Disjoint (U i) (U j)) ∧
      ∀ i j, i ≠ j → Disjoint (U i) (P.vertexArc j) := by
  let C := fun i : ZMod (m + 3) => ⋃ j : {j : ZMod (m + 3) // j ≠ i}, P.vertexArc j
  have hC (i) : IsClosed (C i) := (isCompact_iUnion fun j : {j : ZMod (m + 3) // j ≠ i} =>
    P.isCompact_vertexArc j).isClosed
  have hiC (i) : P.vertex i ∉ C i := by
    intro hi
    obtain ⟨j, hj⟩ := mem_iUnion.mp hi
    exact j.property ((P.vertex_mem_vertexArc_iff j i).mp hj).symm
  obtain ⟨U, hU, hdisj⟩ := Set.exists_pairwise_disjoint_open_neighborhoods
    P.vertex P.vertex_inj (fun i => O i \ C i)
    (fun i => (hO i).sdiff (hC i)) (fun i => ⟨hiO i, hiC i⟩)
  refine ⟨U, fun i => ⟨(hU i).1, (hU i).2.1,
    fun p hp => ((hU i).2.2 hp).1⟩, hdisj, ?_⟩
  intro i j hij
  apply disjoint_left.mpr
  intro p hp hpj
  exact ((hU i).2.2 hp).2 (mem_iUnion.mpr ⟨⟨j, hij.symm⟩, hpj⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PrePolygon.exists_disjoint_open_vertexArc_neighborhoods then
    throwError "Refusing to shadow existing declaration Schoenflies.PrePolygon.exists_disjoint_open_vertexArc_neighborhoods"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PrePolygon.exists_disjoint_open_vertexArc_neighborhoods ``Submission.Schoenflies.PrePolygon.exists_disjoint_open_vertexArc_neighborhoods

end Schoenflies.PrePolygon
