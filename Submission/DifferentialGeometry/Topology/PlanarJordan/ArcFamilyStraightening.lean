/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PlanarJordan.ArcStraightening
import Submission.DifferentialGeometry.Topology.Homeomorph.DisjointGluing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PlanarJordan

open _root_.Submission.Schoenflies _root_.Submission.DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_homeomorph_polygonal_images_of_disjoint_supports
    {ι : Type*} (g : ι → Plane ≃ₜ Plane) (A D : ι → Set Plane)
    (hpoly : ∀ i, IsPolygonal (g i '' A i))
    (hfix : ∀ i, _root_.Set.EqOn (g i) id (interior (D i))ᶜ)
    (hdist : ∀ i x, _root_.Dist.dist (g i x) x ≤ Metric.diam (D i))
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (havoid : ∀ i j, i ≠ j → Disjoint (D i) (A j))
    (hbounded : ∀ i, Bornology.IsBounded (D i))
    (hcontract : Filter.Tendsto (fun i => Metric.diam (D i)) Filter.cofinite (𝓝 0)) :
    ∃ e : Plane ≃ₜ Plane, (∀ i, IsPolygonal (e '' A i)) ∧
      _root_.Set.EqOn e id (⋃ i, interior (D i))ᶜ ∧
      ∀ i x, x ∈ D i → _root_.Dist.dist (e x) x ≤ Metric.diam (D i) := by
  have hgfix (i : ι) : _root_.Set.EqOn (g i) id (D i)ᶜ :=
    (hfix i).mono (compl_subset_compl.mpr interior_subset)
  obtain ⟨e, he, hefix⟩ := Homeomorph.exists_gluing_of_pairwise_disjoint_of_tendsto_diam
    g D hgfix hdis hbounded hcontract
  have heA (i : ι) : _root_.Set.EqOn e (g i) (A i) := by
    intro x hx
    by_cases hxD : x ∈ D i
    · exact he i hxD
    have hxall : x ∉ ⋃ j, D j := by
      intro hxall
      obtain ⟨j, hj⟩ := mem_iUnion.mp hxall
      by_cases hji : j = i
      · exact hxD (hji ▸ hj)
      exact disjoint_left.mp (havoid j i hji) hj hx
    rw [hefix hxall, hgfix i hxD]
  refine ⟨e, fun i => (heA i).image_eq ▸ hpoly i, ?_, ?_⟩
  · intro x hx
    by_cases hxD : x ∈ ⋃ i, D i
    · obtain ⟨i, hiD⟩ := mem_iUnion.mp hxD
      rw [he i hiD]
      exact hfix i (fun h => hx (mem_iUnion.mpr ⟨i, h⟩))
    · exact hefix hxD
  · intro i x hx
    rw [he i hx]
    exact hdist i x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_polygonal_images_of_disjoint_supports
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_polygonal_images_of_disjoint_supports target :: scope.openDecls } }

theorem exists_homeomorph_polygonal_arc_family_of_disjoint_neighborhoods
    {ι : Type*} {f : ι → ℝ → Plane}
    (hf : ∀ i, ContinuousOn (f i) unitInterval) (hi : ∀ i, _root_.Set.InjOn (f i) unitInterval)
    {a b : ι → ℝ} (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i) (hb : ∀ i, b i < 1)
    (hl : ∀ i, IsPolygonal (f i '' _root_.Set.Icc 0 (a i)))
    (hr : ∀ i, IsPolygonal (f i '' _root_.Set.Icc (b i) 1))
    {U : ι → Set Plane} (hU : ∀ i, U i ∈ 𝓝ˢ (f i '' _root_.Set.Icc (a i) (b i)))
    (hdis : Pairwise fun i j => Disjoint (U i) (U j))
    (havoid : ∀ i j, i ≠ j → Disjoint (U i) (f j '' unitInterval))
    (hbounded : ∀ i, Bornology.IsBounded (U i))
    (hcontract : Filter.Tendsto (fun i => Metric.diam (U i)) Filter.cofinite (𝓝 0)) :
    ∃ (D : ι → Set Plane) (e : Plane ≃ₜ Plane),
      (∀ i, IsPLBall 2 (D i) ∧ f i '' _root_.Set.Icc (a i) (b i) ⊆ interior (D i) ∧
        D i ⊆ U i ∧ Disjoint (D i) {f i 0, f i 1}) ∧
      (Pairwise fun i j => Disjoint (D i) (D j)) ∧
      Filter.Tendsto (fun i => Metric.diam (D i)) Filter.cofinite (𝓝 0) ∧
      (∀ i, IsPolygonal (e '' (f i '' unitInterval))) ∧
      _root_.Set.EqOn e id (⋃ i, interior (D i))ᶜ ∧
      ∀ i x, x ∈ D i → _root_.Dist.dist (e x) x ≤ Metric.diam (D i) := by
  choose D hD hCD hDU hDends g hg hfix hdist using fun i =>
    exists_homeomorph_polygonal_arc_of_polygonal_ends (hf i) (hi i)
      (ha i) (hab i) (hb i) (hl i) (hr i) (hU i)
  have hDdis : Pairwise fun i j => Disjoint (D i) (D j) :=
    fun i j hij => (hdis hij).mono (hDU i) (hDU j)
  have hDavoid (i j : ι) (hij : i ≠ j) : Disjoint (D i) (f j '' unitInterval) :=
    (havoid i j hij).mono_left (hDU i)
  have hDcontract : Filter.Tendsto (fun i => Metric.diam (D i)) Filter.cofinite (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcontract
      (fun _ => Metric.diam_nonneg) (fun i => Metric.diam_mono (hDU i) (hbounded i))
  obtain ⟨e, hepoly, hefix, hesmall⟩ := exists_homeomorph_polygonal_images_of_disjoint_supports
    g (fun i => f i '' unitInterval) D hg hfix hdist hDdis hDavoid
      (fun i => (hD i).isPolyhedron.isCompact.isBounded) hDcontract
  exact ⟨D, e, fun i => ⟨hD i, hCD i, hDU i, hDends i⟩, hDdis, hDcontract, hepoly, hefix, hesmall⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_polygonal_arc_family_of_disjoint_neighborhoods then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_polygonal_arc_family_of_disjoint_neighborhoods"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_polygonal_arc_family_of_disjoint_neighborhoods ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_polygonal_arc_family_of_disjoint_neighborhoods

open _root_.Classical in
theorem exists_homeomorph_polygonal_arc_family_of_polygonal_ends
    {ι : Type*} [Finite ι] {f : ι → ℝ → Plane}
    (hf : ∀ i, ContinuousOn (f i) unitInterval) (hi : ∀ i, _root_.Set.InjOn (f i) unitInterval)
    {a b : ι → ℝ} (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i) (hb : ∀ i, b i < 1)
    (hl : ∀ i, IsPolygonal (f i '' _root_.Set.Icc 0 (a i)))
    (hr : ∀ i, IsPolygonal (f i '' _root_.Set.Icc (b i) 1))
    (hmeet : ∀ i j, i ≠ j → (f i '' unitInterval) ∩ (f j '' unitInterval) ⊆ {f i 0, f i 1})
    {U : ι → Set Plane} (hU : ∀ i, U i ∈ 𝓝ˢ (f i '' _root_.Set.Icc (a i) (b i))) :
    ∃ (D : ι → Set Plane) (e : Plane ≃ₜ Plane),
      (∀ i, IsPLBall 2 (D i) ∧ f i '' _root_.Set.Icc (a i) (b i) ⊆ interior (D i) ∧
        D i ⊆ U i ∧ Disjoint (D i) {f i 0, f i 1}) ∧
      (Pairwise fun i j => Disjoint (D i) (D j)) ∧
      (∀ i j, i ≠ j → Disjoint (D i) (f j '' unitInterval)) ∧
      (∀ i, IsPolygonal (e '' (f i '' unitInterval))) ∧
      _root_.Set.EqOn e id (⋃ i, interior (D i))ᶜ ∧
      ∀ i x, x ∈ D i → _root_.Dist.dist (e x) x ≤ Metric.diam (D i) := by
  let A (i : ι) := f i '' unitInterval
  let C (i : ι) := f i '' _root_.Set.Icc (a i) (b i)
  have hCA (i : ι) : C i ⊆ A i := _root_.Set.image_mono (_root_.Set.Icc_subset_Icc (ha i).le (hb i).le)
  have hA (i : ι) : IsArc (A i) := ⟨f i, hf i, hi i, rfl⟩
  have hC (i : ι) : IsCompact (C i) := isCompact_Icc.image_of_continuousOn
    ((hf i).mono (_root_.Set.Icc_subset_Icc (ha i).le (hb i).le))
  have hCends (i : ι) : Disjoint (C i) ({f i 0, f i 1} : Set Plane) := by
    refine disjoint_left.mpr ?_
    rintro x ⟨t, ht, rfl⟩ (h0 | h1)
    · have heq := hi i ⟨(ha i).le.trans ht.1, ht.2.trans (hb i).le⟩ zero_mem_I h0
      linarith [ht.1, ha i]
    · have heq := hi i ⟨(ha i).le.trans ht.1, ht.2.trans (hb i).le⟩ one_mem_I h1
      linarith [ht.2, hb i]
  have hCA_dis (i j : ι) (hij : i ≠ j) : Disjoint (C i) (A j) := disjoint_left.mpr fun x hx hy =>
    disjoint_left.mp (hCends i) hx (hmeet i j hij ⟨hCA i hx, hy⟩)
  have hfilters : Pairwise fun i j => Disjoint (𝓝ˢ (C i)) (𝓝ˢ (C j)) := by
    intro i j hij
    exact separatedNhds_iff_disjoint.mp (SeparatedNhds.of_isCompact_isCompact_isClosed
      (hC i) (hC j) (hC j).isClosed ((hCA_dis i j hij).mono_right (hCA j)))
  obtain ⟨V, hV, hVdis⟩ := hfilters.exists_mem_filter_of_disjoint
  let K (i : ι) := ⋃ j : {j // j ≠ i}, A j.1
  have hK (i : ι) : IsClosed (K i) := isClosed_iUnion_of_finite fun j => (hA j.1).isClosed
  have hCK (i : ι) : C i ⊆ (K i)ᶜ := by
    intro x hx hmem
    obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
    exact disjoint_left.mp (hCA_dis i j.1 j.2.symm) hx hj
  have hN (i : ι) : U i ∩ V i ∩ (K i)ᶜ ∈ 𝓝ˢ (C i) :=
    Filter.inter_mem (Filter.inter_mem (hU i) (hV i))
      ((hK i).isOpen_compl.mem_nhdsSet.mpr (hCK i))
  choose D hD hCD hDN hDends g hg hfix hdist using fun i =>
    exists_homeomorph_polygonal_arc_of_polygonal_ends (hf i) (hi i)
      (ha i) (hab i) (hb i) (hl i) (hr i) (hN i)
  have hDU (i : ι) : D i ⊆ U i := fun _ hx => (hDN i hx).1.1
  have hDV (i : ι) : D i ⊆ V i := fun _ hx => (hDN i hx).1.2
  have hdis : Pairwise fun i j => Disjoint (D i) (D j) :=
    fun i j hij => (hVdis hij).mono (hDV i) (hDV j)
  have havoid (i j : ι) (hij : i ≠ j) : Disjoint (D i) (A j) := by
    refine disjoint_left.mpr fun x hx hy => ?_
    exact (hDN i hx).2 (mem_iUnion.mpr ⟨⟨j, hij.symm⟩, hy⟩)
  obtain ⟨e, hepoly, hefix, hesmall⟩ := exists_homeomorph_polygonal_images_of_disjoint_supports
    g A D hg hfix hdist hdis havoid (fun i => (hD i).isPolyhedron.isCompact.isBounded)
      (by simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot])
  exact ⟨D, e, fun i => ⟨hD i, hCD i, hDU i, hDends i⟩, hdis, havoid, hepoly, hefix, hesmall⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_polygonal_arc_family_of_polygonal_ends then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_polygonal_arc_family_of_polygonal_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_polygonal_arc_family_of_polygonal_ends ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_polygonal_arc_family_of_polygonal_ends

end DifferentialGeometry.Topology.PlanarJordan
