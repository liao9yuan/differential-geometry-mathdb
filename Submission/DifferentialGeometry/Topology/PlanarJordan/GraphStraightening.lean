/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PlanarJordan.ArcFamilyStraightening
import Submission.DifferentialGeometry.Topology.PlanarJordan.VertexNeighborhood

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace Graph
open _root_.Graph

open _root_.Submission.Schoenflies _root_.Submission.DifferentialGeometry.Topology.PlanarJordan
open scoped _root_.Graph _root_.Submission.Graph _root_.Submission.Schoenflies.Graph

open _root_.Classical in
theorem IsDrawing.exists_homeomorph_polygonal_edges_of_diam_lt
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing) {ε : ℝ} (hε : 0 < ε)
    (hdiam : ∀ d ∈ E(G), Metric.diam (edgeArc drawing d) < ε / 8)
    {U : Set Plane} (hU : IsOpen U) (hGU : pointSet G drawing ⊆ U) :
    ∃ e : Plane ≃ₜ Plane, (∀ d ∈ E(G), IsPolygonal (e '' edgeArc drawing d)) ∧
      EqOn e id V(G) ∧ _root_.Set.EqOn e id Uᶜ ∧ ∀ x, _root_.Dist.dist (e x) x < ε := by
  let s := (finite_vertexSet (G := G)).toFinset.filter fun v => (G.incidenceSet v).Nonempty
  have hs : ∀ v ∈ s, (G.incidenceSet v).Nonempty :=
    fun _ hv => (Finset.mem_filter.mp hv).2
  have hsU : (s : Set Plane) ⊆ U := fun _ hv =>
    hGU (Or.inl ((finite_vertexSet (G := G)).mem_toFinset.mp (Finset.mem_filter.mp hv).1))
  obtain ⟨r, p, e₀, hr, _, hp, _, _, _, heV, heU, he₀dist⟩ :=
    h.exists_homeomorph_radial_vertex_neighborhoods s hs hU hsU
      (continuous_const : Continuous fun _ : Plane => ε / 8) (fun _ => by positivity)
  let I := {d // d ∈ E(G)}
  let _ : _root_.Finite I := (finite_edgeSet (G := G)).to_subtype
  have hlink (d : I) := (h.edge_param d.2).2.2
  have hleft (d : I) : drawing d 0 ∈ s := Finset.mem_filter.mpr
    ⟨(finite_vertexSet (G := G)).mem_toFinset.mpr (hlink d).left_mem,
      ⟨d, (hlink d).inc_left⟩⟩
  have hright (d : I) : drawing d 1 ∈ s := Finset.mem_filter.mpr
    ⟨(finite_vertexSet (G := G)).mem_toFinset.mpr (hlink d).right_mem,
      ⟨d, (hlink d).inc_right⟩⟩
  have hne (v : {v // v ∈ s}) (d : {d // G.Inc d v.1}) : v.1 ≠ p v d := by
    have hbd : Plane.supDist (p v d) v.1 = r v := by
      simpa only [Plane.frontier_closedSquare, _root_.Set.mem_ofPred_eq] using (hp v d).1
    intro heq
    rw [← heq, Plane.supDist_self] at hbd
    exact (hr v).1.ne' hbd.symm
  have hsegment (v : {v // v ∈ s}) (d : {d // G.Inc d v.1}) :
      segment ℝ v.1 (p v d) ⊆ e₀ '' edgeArc drawing d := by
    rw [← (hp v d).2]
    exact _root_.Set.inter_subset_right
  let f (d : I) (t : ℝ) := e₀ (drawing d t)
  have hf (d : I) : ContinuousOn (f d) unitInterval :=
    e₀.continuous.comp_continuousOn (h.edge_param d.2).1
  have hi (d : I) : _root_.Set.InjOn (f d) unitInterval := e₀.injective.injOn.comp
    (h.edge_param d.2).2.1 (_root_.Set.mapsTo_univ _ _)
  have himage (d : I) : f d '' unitInterval = e₀ '' edgeArc drawing d := by
    rw [edgeArc, _root_.Set.image_image]
  have hends (d : I) : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧
      IsPolygonal (f d '' _root_.Set.Icc 0 a) ∧ IsPolygonal (f d '' _root_.Set.Icc b 1) := by
    let v : {v // v ∈ s} := ⟨drawing d 0, hleft d⟩
    let w : {v // v ∈ s} := ⟨drawing d 1, hright d⟩
    let dl : {e // G.Inc e v.1} := ⟨d, (hlink d).inc_left⟩
    let dr : {e // G.Inc e w.1} := ⟨d, (hlink d).inc_right⟩
    have hf0 : f d 0 = v.1 := heV (hlink d).left_mem
    have hf1 : f d 1 = w.1 := heV (hlink d).right_mem
    apply exists_polygonal_subarcs_of_segment_subsets (hf d) (hi d)
      (hf0.symm ▸ hne v dl) (hf1.symm ▸ hne w dr)
    · rw [hf0, himage]
      exact hsegment v dl
    · rw [hf1, himage]
      exact hsegment w dr
  choose a b ha hab hb hlpoly hrpoly using hends
  have hmeet (d j : I) (hdj : d ≠ j) :
      (f d '' unitInterval) ∩ (f j '' unitInterval) ⊆ {f d 0, f d 1} := by
    rintro x ⟨⟨t, ht, rfl⟩, ⟨u, hu, heq⟩⟩
    have hdraw : drawing j u = drawing d t := e₀.injective heq
    have hxV := h.arcs_meet_at_vertex d.2 j.2 (fun heq => hdj (Subtype.ext heq))
      (_root_.Set.mem_image_of_mem (drawing d) ht) (hdraw ▸ _root_.Set.mem_image_of_mem (drawing j) hu)
    exact (h.vertex_mem_edgeArc (hlink d) hxV (_root_.Set.mem_image_of_mem (drawing d) ht)).elim
      (fun heq => Or.inl (congrArg e₀ heq)) (fun heq => Or.inr (congrArg e₀ heq))
  have hmaps : _root_.Set.MapsTo e₀ U U := by
    intro x hx
    by_contra hnot
    exact hnot ((e₀.injective (heU hnot)).symm ▸ hx)
  have hcore (d : I) : f d '' _root_.Set.Icc (a d) (b d) ⊆ U \ V(G) := by
    rintro x ⟨t, ht, rfl⟩
    have htI : t ∈ unitInterval := ⟨(ha d).le.trans ht.1, ht.2.trans (hb d).le⟩
    have hxA : drawing d t ∈ edgeArc drawing d := _root_.Set.mem_image_of_mem _ htI
    refine ⟨hmaps (hGU (edgeArc_subset_pointSet d.2 hxA)), ?_⟩
    intro hxV
    have hx : e₀ (drawing d t) = drawing d t := e₀.injective (heV hxV)
    have htV : drawing d t ∈ V(G) := hx ▸ hxV
    rcases h.vertex_mem_edgeArc (hlink d) htV hxA with h0 | h1
    · have heq := (h.edge_param d.2).2.1 htI zero_mem_I h0
      linarith [ht.1, ha d]
    · have heq := (h.edge_param d.2).2.1 htI one_mem_I h1
      linarith [ht.2, hb d]
  have hball (d : I) : f d '' _root_.Set.Icc (a d) (b d) ⊆ Metric.ball (drawing d 0) (ε / 4) := by
    rintro x ⟨t, ht, rfl⟩
    have htI : t ∈ unitInterval := ⟨(ha d).le.trans ht.1, ht.2.trans (hb d).le⟩
    have hdist := Metric.dist_le_diam_of_mem (h.isCompact_edgeArc d.2).isBounded
      (_root_.Set.mem_image_of_mem (drawing d) htI) (_root_.Set.mem_image_of_mem (drawing d) zero_mem_I)
    have hvertex := he₀dist (drawing d t)
    have hedge := hdiam d d.2
    change _root_.Dist.dist (e₀ (drawing d t)) (drawing d 0) < ε / 4
    linarith [dist_triangle (e₀ (drawing d t)) (drawing d t) (drawing d 0)]
  have hN (d : I) : (U \ V(G)) ∩ Metric.ball (drawing d 0) (ε / 4) ∈
      𝓝ˢ (f d '' _root_.Set.Icc (a d) (b d)) :=
    ((hU.sdiff (finite_vertexSet (G := G)).isClosed).inter Metric.isOpen_ball).mem_nhdsSet.mpr
      (_root_.Set.subset_inter (hcore d) (hball d))
  obtain ⟨D, e₁, hD, _, _, hpoly, hfix, hdist⟩ :=
    exists_homeomorph_polygonal_arc_family_of_polygonal_ends hf hi ha hab hb
      hlpoly hrpoly hmeet hN
  have he₁V : _root_.Set.EqOn e₁ id V(G) := by
    intro x hx
    apply hfix
    intro hmem
    obtain ⟨d, hd⟩ := mem_iUnion.mp hmem
    exact ((hD d).2.2.1 (interior_subset hd)).1.2 hx
  have he₁U : _root_.Set.EqOn e₁ id Uᶜ := by
    intro x hx
    apply hfix
    intro hmem
    obtain ⟨d, hd⟩ := mem_iUnion.mp hmem
    exact hx ((hD d).2.2.1 (interior_subset hd)).1.1
  refine ⟨e₀.trans e₁, ?_, ?_, ?_, ?_⟩
  · intro d hd
    have hpolyd := hpoly ⟨d, hd⟩
    rw [himage] at hpolyd
    change IsPolygonal ((e₁ ∘ e₀) '' edgeArc drawing d)
    simpa only [_root_.Set.image_image, Function.comp_def] using hpolyd
  · intro x hx
    change e₁ (e₀ x) = x
    rw [heV hx, id_eq, he₁V hx]
    rfl
  · intro x hx
    change e₁ (e₀ x) = x
    rw [heU hx, id_eq, he₁U hx]
    rfl
  · intro x
    have hsmall : _root_.Dist.dist (e₁ (e₀ x)) (e₀ x) ≤ ε / 2 := by
      by_cases hx : e₀ x ∈ ⋃ d, interior (D d)
      · obtain ⟨d, hd⟩ := mem_iUnion.mp hx
        have hDbound : Metric.diam (D d) ≤ 2 * (ε / 4) :=
          Metric.diam_le_of_subset_closedBall (by positivity) fun y hy =>
            Metric.ball_subset_closedBall ((hD d).2.2.1 hy).2
        exact (hdist d (e₀ x) (interior_subset hd)).trans (by linarith)
      · rw [hfix hx, id_eq, dist_self]
        positivity
    change _root_.Dist.dist (e₁ (e₀ x)) x < ε
    have hvertex := he₀dist x
    linarith [dist_triangle (e₁ (e₀ x)) (e₀ x) x]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.exists_homeomorph_polygonal_edges_of_diam_lt then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.exists_homeomorph_polygonal_edges_of_diam_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.exists_homeomorph_polygonal_edges_of_diam_lt ``Submission.Graph.IsDrawing.exists_homeomorph_polygonal_edges_of_diam_lt

theorem IsDrawing.exists_homeomorph_polygonal_edges
    {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane} [G.Finite]
    (h : IsDrawing G drawing)
    {U : Set Plane} (hU : IsOpen U) (hGU : pointSet G drawing ⊆ U) :
    ∃ e : Plane ≃ₜ Plane, (∀ d ∈ E(G), IsPolygonal (e '' edgeArc drawing d)) ∧
      EqOn e id V(G) ∧ _root_.Set.EqOn e id Uᶜ := by
  let ε := 8 * (Metric.diam (pointSet G drawing) + 1)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hdiam (d : β) (hd : d ∈ E(G)) : Metric.diam (edgeArc drawing d) < ε / 8 := by
    have hle := Metric.diam_mono (edgeArc_subset_pointSet hd) h.isCompact_pointSet.isBounded
    dsimp only [ε]
    linarith
  obtain ⟨e, hpoly, heV, heU, _⟩ := h.exists_homeomorph_polygonal_edges_of_diam_lt hε hdiam hU hGU
  exact ⟨e, hpoly, heV, heU⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Graph.IsDrawing.exists_homeomorph_polygonal_edges then
    throwError "Refusing to shadow existing declaration Graph.IsDrawing.exists_homeomorph_polygonal_edges"
  Lean.modifyEnv fun env => Lean.addAlias env `Graph.IsDrawing.exists_homeomorph_polygonal_edges ``Submission.Graph.IsDrawing.exists_homeomorph_polygonal_edges

end Graph
