import Submission.DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import Submission.DifferentialGeometry.Topology.SimplicialComplex.EdgeGraph
import Mathlib.Order.Interval.Set.Infinite

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem linearMap_injOn_segment_of_ne (ℓ : E →ₗ[ℝ] ℝ) {a b : E}
    (hab : ℓ a ≠ ℓ b) : _root_.Set.InjOn ℓ (segment ℝ a b) := by
  rintro x hx y hy hxy
  rw [segment_eq_image'] at hx hy
  obtain ⟨s, -, rfl⟩ := hx
  obtain ⟨t, -, rfl⟩ := hy
  have hst : s = t := by
    simp only [map_add, map_smul, map_sub, smul_eq_mul] at hxy
    exact (mul_right_cancel₀ (sub_ne_zero.mpr hab.symm)) (by linarith)
  rw [hst]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.linearMap_injOn_segment_of_ne
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.linearMap_injOn_segment_of_ne target :: scope.openDecls } }

open _root_.Classical in
theorem finite_fiber_of_notMem_vertex_image
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hcard : ∀ s ∈ K.faces, s.card ≤ 2) (ℓ : E →ₗ[ℝ] ℝ) {r : ℝ}
    (hr : r ∉ ℓ '' K.vertices) : (K.space ∩ {x | ℓ x = r}).Finite := by
  have hface : ∀ s ∈ K.faces, (convexHull ℝ (s : Set E) ∩ {x | ℓ x = r}).Finite := by
    intro s hs
    have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
    have hbound := hcard s hs
    have hv (a : E) (ha : a ∈ s) : ℓ a ≠ r := fun h =>
      hr ⟨a, K.down_closed hs (Finset.singleton_subset_iff.mpr ha)
        (Finset.singleton_nonempty a), h⟩
    rcases (show s.card = 1 ∨ s.card = 2 by omega) with hone | htwo
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hone
      exact (_root_.Set.finite_singleton a).subset (by simp)
    · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp htwo
      rw [Finset.coe_pair, convexHull_pair]
      by_cases hl : ℓ a = ℓ b
      · have hempty : segment ℝ a b ∩ {x | ℓ x = r} = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          rintro x ⟨hx, hxr⟩
          rw [segment_eq_image'] at hx
          obtain ⟨t, -, rfl⟩ := hx
          have : ℓ a = r := by
            simpa only [_root_.Set.mem_ofPred_eq, map_add, map_smul, map_sub, hl, sub_self, smul_zero,
              add_zero] using hxr
          exact hv a (by simp) this
        rw [hempty]
        exact _root_.Set.finite_empty
      · exact (show (segment ℝ a b ∩ {x | ℓ x = r}).Subsingleton from
          fun x hx y hy => linearMap_injOn_segment_of_ne ℓ hl hx.1 hy.1
            (hx.2.trans hy.2.symm)).finite
  apply ((Set.toFinite K.faces).biUnion hface).subset
  rintro x ⟨hx, hxr⟩
  obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
  exact mem_iUnion₂.mpr ⟨s, hs, hxs, hxr⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.finite_fiber_of_notMem_vertex_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.finite_fiber_of_notMem_vertex_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.finite_fiber_of_notMem_vertex_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.finite_fiber_of_notMem_vertex_image

open _root_.Classical in
theorem exists_edge_of_mem_fiber_of_notMem_vertex_image [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hcard : ∀ s ∈ K.faces, s.card ≤ 2) (ℓ : E →ₗ[ℝ] ℝ) {r : ℝ}
    (hr : r ∉ ℓ '' K.vertices) {x : E} (hx : x ∈ K.space ∩ {y | ℓ y = r}) :
    ∃ a b : E, a ≠ b ∧ ({a, b} : Finset E) ∈ K.faces ∧ ℓ a ≠ ℓ b ∧
      x ∈ openSimplex ({a, b} : Finset E) ∧
      ∀ᶠ y in 𝓝 x, y ∈ K.space ↔ ∃ t : ℝ, y = x + t • (b - a) := by
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hx.1
  have hnot : x ∉ K.vertices := fun hxv => hr ⟨x, hxv, hx.2⟩
  have htwo : s.card = 2 := by
    have := one_lt_card_of_mem_openSimplex_of_notMem_vertices K hs hxs hnot
    have := hcard s hs
    omega
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp htwo
  have hℓ : ℓ a ≠ ℓ b := by
    intro heq
    have hseg : x ∈ segment ℝ a b := by
      simpa only [Finset.coe_pair, convexHull_pair] using openSimplex_subset_convexHull _ hxs
    rw [segment_eq_image'] at hseg
    obtain ⟨t, -, htx⟩ := hseg
    have hax : ℓ a = r := by
      rw [← htx] at hx
      simpa only [_root_.Set.mem_ofPred_eq, map_add, map_smul, map_sub, heq, sub_self, smul_zero,
        add_zero] using hx.2
    exact hr ⟨a, K.down_closed hs (by simp) (Finset.singleton_nonempty a), hax⟩
  refine ⟨a, b, hab, hs, hℓ, hxs, ?_⟩
  have hgerm := eventually_mem_space_iff_sub_mem_vectorSpan K hs
    (fun t ht _ => (hcard t ht).trans_eq htwo.symm) hxs
  filter_upwards [hgerm] with y hy
  rw [hy, Finset.coe_pair,
    vectorSpan_eq_span_vsub_set_right ℝ (by simp : a ∈ ({a, b} : Set E))]
  simp only [_root_.Set.image_insert_eq, _root_.Set.image_singleton, vsub_eq_sub, sub_self, Submodule.span_insert_zero]
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, by rw [ht]; abel⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, by abel⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_edge_of_mem_fiber_of_notMem_vertex_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_edge_of_mem_fiber_of_notMem_vertex_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_edge_of_mem_fiber_of_notMem_vertex_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_edge_of_mem_fiber_of_notMem_vertex_image

open _root_.Classical in
theorem exists_regular_height_of_card_le_two [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hcard : ∀ s ∈ K.faces, s.card ≤ 2) (ℓ : E →ₗ[ℝ] ℝ) {a b : ℝ} (hab : a < b) :
    ∃ r ∈ _root_.Set.Ioo a b, r ∉ ℓ '' K.vertices ∧ (K.space ∩ {x | ℓ x = r}).Finite ∧
      ∀ x ∈ K.space ∩ {y | ℓ y = r},
        ∃ p q : E, p ≠ q ∧ ({p, q} : Finset E) ∈ K.faces ∧ ℓ p ≠ ℓ q ∧
          x ∈ openSimplex ({p, q} : Finset E) ∧
          ∀ᶠ y in 𝓝 x, y ∈ K.space ↔ ∃ t : ℝ, y = x + t • (q - p) := by
  obtain ⟨r, hrab, hr⟩ := (_root_.Set.Ioo_infinite hab).exists_notMem_finite
    ((SimplicialComplex.finite_vertices K).image ℓ)
  exact ⟨r, hrab, hr, finite_fiber_of_notMem_vertex_image K hcard ℓ hr,
    fun _ hx => exists_edge_of_mem_fiber_of_notMem_vertex_image K hcard ℓ hr hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_regular_height_of_card_le_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_regular_height_of_card_le_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_regular_height_of_card_le_two ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_regular_height_of_card_le_two

end DifferentialGeometry.Topology.PiecewiseLinear
