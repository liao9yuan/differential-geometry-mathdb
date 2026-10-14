import Submission.DifferentialGeometry.Topology.PlanarJordan.BandCut
import Submission.DifferentialGeometry.Topology.PlanarJordan.BandCollar
import Submission.DifferentialGeometry.Topology.PlanarJordan.Regions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Topology.PlanarJordan

private theorem region_mem_iff_of_inside_mem_iff
    {C Ω : Set Schoenflies.Plane} (hΩ : Schoenflies.IsRegionOf C Ω)
    {x y : Schoenflies.Plane} (hx : x ∈ Ω) (hy : y ∉ C) :
    (y ∈ Ω ↔ (y ∈ Schoenflies.inside C ↔ x ∈ Schoenflies.inside C)) := by
  rcases hΩ with rfl | rfl
  · simp only [hx, iff_true]
  · have hxnot : x ∉ Schoenflies.inside C := fun h =>
      disjoint_left.mp Schoenflies.disjoint_inside_outside h hx
    simp only [hxnot, iff_false]
    constructor
    · exact fun hy' hi => disjoint_left.mp Schoenflies.disjoint_inside_outside hi hy'
    · intro hi
      have hc : y ∈ Schoenflies.inside C ∪ Schoenflies.outside C := by
        rw [Schoenflies.inside_union_outside]
        exact hy
      exact hc.resolve_left hi

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.region_mem_iff_of_inside_mem_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.region_mem_iff_of_inside_mem_iff target :: scope.openDecls } }

theorem exists_band_region_collars
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane) {h k : ℝ} (hk : 0 < k) (hkh : k < h)
    (hedges : ∀ a ∈ ({-1, 1} : Set ℝ), (fun u => B (a, u)) '' _root_.Set.Ioo (-h) h ⊆ _root_.Set.range γ)
    {Ω : Set Schoenflies.Plane} (hΩ : Schoenflies.IsRegionOf (_root_.Set.range γ) Ω)
    (hband : B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Ioo (-h) h) ⊆ Ω) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ a ∈ ({-1, 1} : Set ℝ),
      ∀ z ∈ _root_.Set.Ioo (a - ε) (a + ε) ×ˢ _root_.Set.Ioo (-k) k,
        B z ∈ Ω ↔ a * z.1 < 1 := by
  obtain ⟨ε, hε, hεlt, hc₀, hc₁, hs⟩ := exists_band_attaching_collars hγ B hk hkh
    (hedges (-1) (by simp)) (hedges 1 (by simp)) (fun z hz => hΩ.subset_compl (hband ⟨z, hz, rfl⟩))
  let p : ℝ × ℝ := (-1 + ε / 2, 0)
  have hpR : p ∈ _root_.Set.Ioo (-1 - ε) (-1 + ε) ×ˢ _root_.Set.Ioo (-k) k := by
    exact ⟨⟨by dsimp [p]; linarith, by dsimp [p]; linarith⟩, neg_neg_of_pos hk, hk⟩
  have hpΩ : B p ∈ Ω := hband ⟨p, ⟨⟨by dsimp [p]; linarith,
    by dsimp [p]; linarith⟩, by dsimp [p]; linarith, by dsimp [p]; linarith⟩, rfl⟩
  have hpt : -1 < p.1 := by dsimp [p]; linarith
  refine ⟨ε, hε, hεlt, ?_⟩
  intro a ha z hz
  have hza : B z ∈ _root_.Set.range γ ↔ z.1 = a := by
    rcases mem_insert_iff.mp ha with rfl | ha
    · exact hc₀ z hz
    · obtain rfl := mem_singleton_iff.mp ha
      exact hc₁ z hz
  by_cases hzc : B z ∈ _root_.Set.range γ
  · have hnΩ : B z ∉ Ω := fun h => hΩ.subset_compl h hzc
    have heq := hza.mp hzc
    rcases mem_insert_iff.mp ha with rfl | ha
    · simp [hnΩ, heq]
    · obtain rfl := mem_singleton_iff.mp ha
      simp [hnΩ, heq]
  rw [region_mem_iff_of_inside_mem_iff hΩ hpΩ hzc]
  rcases hs with hs | hs
  · have hpI : B p ∈ Schoenflies.inside (_root_.Set.range γ) := (hs.1 p hpR).mpr hpt
    simp only [hpI, iff_true]
    rcases mem_insert_iff.mp ha with rfl | ha
    · rw [hs.1 z hz]
      simp only [neg_one_mul]
      constructor <;> intro hx <;> linarith
    · obtain rfl := mem_singleton_iff.mp ha
      simpa using hs.2 z hz
  · have hpI : B p ∉ Schoenflies.inside (_root_.Set.range γ) := fun hp =>
      (not_lt_of_ge hpt.le) ((hs.1 p hpR).mp hp)
    simp only [hpI, iff_false]
    have hne : z.1 ≠ a := fun he => hzc (hza.mpr he)
    rcases mem_insert_iff.mp ha with rfl | ha
    · rw [hs.1 z hz]
      simp only [not_lt, neg_one_mul]
      constructor <;> intro hx <;> rcases hne.lt_or_gt with hlt | hgt <;> linarith
    · obtain rfl := mem_singleton_iff.mp ha
      rw [hs.2 z hz]
      simp only [not_lt, one_mul]
      exact ⟨fun hx => lt_of_le_of_ne hx hne, fun hx => hx.le⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_band_region_collars then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_band_region_collars"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_band_region_collars ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_band_region_collars

private theorem mem_cut_regions_iff
    (B : (ℝ × ℝ) ≃ₜ Schoenflies.Plane) {h k ε a : ℝ} (ha : a ∈ ({-1, 1} : Set ℝ))
    (hε : ε < 1) (hkh : k < h)
    {Ω V₀ V₁ : Set Schoenflies.Plane}
    (hcover : Ω \ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0}) = V₀ ∪ V₁)
    (hdisj : Disjoint V₀ V₁)
    (hupper : B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Ioo 0 h) ⊆ V₀)
    (hlower : B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Ioo (-h) 0) ⊆ V₁)
    (hΩ : ∀ z ∈ _root_.Set.Ioo (a - ε) (a + ε) ×ˢ _root_.Set.Ioo (-k) k, B z ∈ Ω ↔ a * z.1 < 1) :
    ∀ z ∈ _root_.Set.Ioo (a - ε) (a + ε) ×ˢ _root_.Set.Ioo (-k) k,
      (B z ∈ V₀ ↔ a * z.1 < 1 ∧ 0 < z.2) ∧
      (B z ∈ V₁ ↔ a * z.1 < 1 ∧ z.2 < 0) := by
  intro z hz
  have hmid : a * z.1 < 1 → z.1 ∈ _root_.Set.Ioo (-1 : ℝ) 1 := by
    intro hx
    rcases mem_insert_iff.mp ha with rfl | ha
    · simp only [neg_one_mul] at hx
      exact ⟨by linarith, by linarith [hz.1.2]⟩
    · obtain rfl := mem_singleton_iff.mp ha
      simp only [one_mul] at hx
      exact ⟨by linarith [hz.1.1], hx⟩
  have hdata (i : Set Schoenflies.Plane) (hi : i ⊆ V₀ ∪ V₁) (hzi : B z ∈ i) :
      a * z.1 < 1 ∧ z.2 ≠ 0 := by
    have hm : B z ∈ Ω \ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0}) := hcover.symm ▸ hi hzi
    have hax := (hΩ z hz).mp hm.1
    refine ⟨hax, ?_⟩
    intro heq
    exact hm.2 ⟨z, ⟨⟨(hmid hax).1.le, (hmid hax).2.le⟩, heq⟩, rfl⟩
  constructor
  · constructor
    · intro hzi
      obtain ⟨hax, hy⟩ := hdata V₀ _root_.Set.subset_union_left hzi
      refine ⟨hax, ?_⟩
      rcases hy.lt_or_gt with hn | hp
      · exact (disjoint_left.mp hdisj hzi (hlower ⟨z,
          ⟨hmid hax, by linarith [hz.2.1], hn⟩, rfl⟩)).elim
      · exact hp
    · rintro ⟨hax, hy⟩
      exact hupper ⟨z, ⟨hmid hax, hy, by linarith [hz.2.2]⟩, rfl⟩
  · constructor
    · intro hzi
      obtain ⟨hax, hy⟩ := hdata V₁ _root_.Set.subset_union_right hzi
      refine ⟨hax, ?_⟩
      rcases hy.lt_or_gt with hn | hp
      · exact hn
      · exact (disjoint_left.mp hdisj (hupper ⟨z,
          ⟨hmid hax, hp, by linarith [hz.2.2]⟩, rfl⟩) hzi).elim
    · rintro ⟨hax, hy⟩
      exact hlower ⟨z, ⟨hmid hax, by linarith [hz.2.1], hy⟩, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.mem_cut_regions_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.mem_cut_regions_iff target :: scope.openDecls } }

private theorem cut_quadrant_closure {a b : ℝ}
    (ha : a ∈ ({-1, 1} : Set ℝ)) (hb : b ∈ ({-1, 1} : Set ℝ)) :
    closure {z : ℝ × ℝ | a * z.1 < 1 ∧ 0 < b * z.2} =
      {z : ℝ × ℝ | a * z.1 ≤ 1 ∧ 0 ≤ b * z.2} ∧
    interior {z : ℝ × ℝ | a * z.1 ≤ 1 ∧ 0 ≤ b * z.2} =
      {z : ℝ × ℝ | a * z.1 < 1 ∧ 0 < b * z.2} := by
  simp only [_root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp only [neg_one_mul, one_mul, neg_pos, neg_nonneg]
  · have hlt (x : ℝ) : -x < 1 ↔ -1 < x := by constructor <;> intro h <;> linarith
    have hle (x : ℝ) : -x ≤ 1 ↔ -1 ≤ x := by constructor <;> intro h <;> linarith
    simp only [hlt, hle]
    change closure (_root_.Set.Ioi (-1 : ℝ) ×ˢ _root_.Set.Iio (0 : ℝ)) = _root_.Set.Ici (-1) ×ˢ _root_.Set.Iic 0 ∧
      interior (_root_.Set.Ici (-1 : ℝ) ×ˢ _root_.Set.Iic (0 : ℝ)) = _root_.Set.Ioi (-1) ×ˢ _root_.Set.Iio 0
    simp only [closure_prod_eq, interior_prod_eq, closure_Ioi, closure_Iio, interior_Ici, interior_Iic, and_self]
  · have hlt (x : ℝ) : -x < 1 ↔ -1 < x := by constructor <;> intro h <;> linarith
    have hle (x : ℝ) : -x ≤ 1 ↔ -1 ≤ x := by constructor <;> intro h <;> linarith
    simp only [hlt, hle]
    change closure (_root_.Set.Ioi (-1 : ℝ) ×ˢ _root_.Set.Ioi (0 : ℝ)) = _root_.Set.Ici (-1) ×ˢ _root_.Set.Ici 0 ∧
      interior (_root_.Set.Ici (-1 : ℝ) ×ˢ _root_.Set.Ici (0 : ℝ)) = _root_.Set.Ioi (-1) ×ˢ _root_.Set.Ioi 0
    simp only [closure_prod_eq, interior_prod_eq, closure_Ioi, interior_Ici, and_self]
  · change closure (_root_.Set.Iio (1 : ℝ) ×ˢ _root_.Set.Iio (0 : ℝ)) = _root_.Set.Iic 1 ×ˢ _root_.Set.Iic 0 ∧
      interior (_root_.Set.Iic (1 : ℝ) ×ˢ _root_.Set.Iic (0 : ℝ)) = _root_.Set.Iio 1 ×ˢ _root_.Set.Iio 0
    simp only [closure_prod_eq, interior_prod_eq, closure_Iio, interior_Iic, and_self]
  · change closure (_root_.Set.Iio (1 : ℝ) ×ˢ _root_.Set.Ioi (0 : ℝ)) = _root_.Set.Iic 1 ×ˢ _root_.Set.Ici 0 ∧
      interior (_root_.Set.Iic (1 : ℝ) ×ˢ _root_.Set.Ici (0 : ℝ)) = _root_.Set.Iio 1 ×ˢ _root_.Set.Ioi 0
    simp only [closure_prod_eq, interior_prod_eq, closure_Ioi, closure_Iio, interior_Ici, interior_Iic, and_self]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.cut_quadrant_closure
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.cut_quadrant_closure target :: scope.openDecls } }

private theorem corner_closure_equations
    (B : (ℝ × ℝ) ≃ₜ Schoenflies.Plane) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {V : Set Schoenflies.Plane} {a b : ℝ}
    (ha : a ∈ ({-1, 1} : Set ℝ)) (hb : b ∈ ({-1, 1} : Set ℝ))
    (hV : ∀ z ∈ U, B z ∈ V ↔ a * z.1 < 1 ∧ 0 < b * z.2) :
    ∀ z ∈ U,
      (B z ∈ closure V ↔ a * z.1 ≤ 1 ∧ 0 ≤ b * z.2) ∧
      (B z ∈ (closure V)ᶜ ↔ 1 < a * z.1 ∨ b * z.2 < 0) ∧
      (B z ∈ closure ((closure V)ᶜ) ↔ 1 ≤ a * z.1 ∨ b * z.2 ≤ 0) := by
  let e := B.toOpenPartialHomeomorph.restrOpen U hU
  have he : e.source = U := by simp [e]
  have hI : e.IsImage {z : ℝ × ℝ | a * z.1 < 1 ∧ 0 < b * z.2} V := by
    intro z hz
    exact hV z (he ▸ hz)
  obtain ⟨hcl, hint⟩ := cut_quadrant_closure ha hb
  have hJ := hI.closure
  rw [hcl] at hJ
  have hK := hJ.compl.closure
  rw [closure_compl, hint] at hK
  intro z hz
  have hze : z ∈ e.source := he.symm ▸ hz
  refine ⟨hJ hze, ?_, ?_⟩
  · change ¬(B z ∈ closure V) ↔ _
    simpa only [_root_.Set.mem_compl_iff, _root_.Set.mem_ofPred_eq, not_and_or, not_le] using
      (show B z ∈ (closure V)ᶜ ↔ z ∈ {z : ℝ × ℝ | a * z.1 ≤ 1 ∧ 0 ≤ b * z.2}ᶜ from hJ.compl hze)
  · simpa only [_root_.Set.mem_compl_iff, _root_.Set.mem_ofPred_eq, not_and_or, not_lt] using
      (show B z ∈ closure ((closure V)ᶜ) ↔ z ∈ {z : ℝ × ℝ | a * z.1 < 1 ∧ 0 < b * z.2}ᶜ from hK hze)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PlanarJordan.corner_closure_equations
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PlanarJordan.corner_closure_equations target :: scope.openDecls } }

theorem exists_cut_region_corner_charts
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane) {h : ℝ} (hh : 0 < h)
    (hedges : ∀ a ∈ ({-1, 1} : Set ℝ), (fun u => B (a, u)) '' _root_.Set.Ioo (-h) h ⊆ _root_.Set.range γ)
    {Ω V₀ V₁ : Set Schoenflies.Plane} (hΩ : Schoenflies.IsRegionOf (_root_.Set.range γ) Ω)
    (hband : B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Ioo (-h) h) ⊆ Ω)
    (hcover : Ω \ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0}) = V₀ ∪ V₁)
    (hdisj : Disjoint V₀ V₁)
    (hupper : B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Ioo 0 h) ⊆ V₀)
    (hlower : B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Ioo (-h) 0) ⊆ V₁) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∃ k : ℝ, 0 < k ∧ k < h ∧
      ∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ _root_.Set.Ioo (a - ε) (a + ε) ×ˢ _root_.Set.Ioo (-k) k,
        (B z ∈ V₀ ↔ a * z.1 < 1 ∧ 0 < z.2) ∧
        (B z ∈ closure V₀ ↔ a * z.1 ≤ 1 ∧ 0 ≤ z.2) ∧
        (B z ∈ (closure V₀)ᶜ ↔ 1 < a * z.1 ∨ z.2 < 0) ∧
        (B z ∈ closure ((closure V₀)ᶜ) ↔ 1 ≤ a * z.1 ∨ z.2 ≤ 0) ∧
        (B z ∈ V₁ ↔ a * z.1 < 1 ∧ z.2 < 0) ∧
        (B z ∈ closure V₁ ↔ a * z.1 ≤ 1 ∧ z.2 ≤ 0) ∧
        (B z ∈ (closure V₁)ᶜ ↔ 1 < a * z.1 ∨ 0 < z.2) ∧
        (B z ∈ closure ((closure V₁)ᶜ) ↔ 1 ≤ a * z.1 ∨ 0 ≤ z.2) := by
  let k := h / 2
  have hk : 0 < k := half_pos hh
  have hkh : k < h := half_lt_self hh
  obtain ⟨ε, hε, hεlt, hcollar⟩ := exists_band_region_collars hγ B hk hkh hedges hΩ hband
  refine ⟨ε, hε, hεlt, k, hk, hkh, ?_⟩
  intro a ha
  have hm := mem_cut_regions_iff B.toHomeomorph ha hεlt hkh hcover hdisj hupper hlower (hcollar a ha)
  have hc₀ := corner_closure_equations B.toHomeomorph (isOpen_Ioo.prod isOpen_Ioo) ha
    (show (1 : ℝ) ∈ ({-1, 1} : Set ℝ) by simp) (fun z hz => by simpa using (hm z hz).1)
  have hc₁ := corner_closure_equations B.toHomeomorph (isOpen_Ioo.prod isOpen_Ioo) ha
    (show (-1 : ℝ) ∈ ({-1, 1} : Set ℝ) by simp) (fun z hz => by simpa using (hm z hz).2)
  intro z hz
  refine ⟨(hm z hz).1, ?_, ?_, ?_, (hm z hz).2, ?_, ?_, ?_⟩
  · simpa using (hc₀ z hz).1
  · simpa using (hc₀ z hz).2.1
  · simpa using (hc₀ z hz).2.2
  · simpa using (hc₁ z hz).1
  · simpa using (hc₁ z hz).2.1
  · simpa using (hc₁ z hz).2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_cut_region_corner_charts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_cut_region_corner_charts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_cut_region_corner_charts ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_cut_region_corner_charts

theorem exists_cut_regions_with_corner_charts_of_attached_band
    {γ : AddCircle (1 : ℝ) → Schoenflies.Plane}
    (hγ : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Schoenflies.Plane) ∞ γ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Schoenflies.Plane)
    {h : ℝ} (hh : 0 < h)
    (hedges : ∀ a ∈ ({-1, 1} : Set ℝ), (fun u => B (a, u)) '' _root_.Set.Ioo (-h) h ⊆ _root_.Set.range γ)
    (havoid : B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Ioo (-h) h) ⊆ (_root_.Set.range γ)ᶜ) :
    ∃ A₀ A₁ : Set Schoenflies.Plane, Schoenflies.IsCutPair (_root_.Set.range γ) (B (-1, 0)) (B (1, 0)) A₀ A₁ ∧
      Schoenflies.IsJordanCurve (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
      Schoenflies.IsJordanCurve (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
      ∃ Ω V₀ V₁ : Set Schoenflies.Plane,
        B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Ioo (-h) h) ⊆ Ω ∧
        Ω \ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0}) = V₀ ∪ V₁ ∧ Disjoint V₀ V₁ ∧
        V₀.Nonempty ∧ V₁.Nonempty ∧
        (∀ z ∈ V₀, connectedComponentIn (Ω \ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) z = V₀) ∧
        (∀ z ∈ V₁, connectedComponentIn (Ω \ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) z = V₁) ∧
        closure V₀ ∩ _root_.Set.range γ = A₀ ∧ closure V₁ ∩ _root_.Set.range γ = A₁ ∧
        B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Ioo 0 h) ⊆ V₀ ∧
        B '' (_root_.Set.Ioo (-1 : ℝ) 1 ×ˢ _root_.Set.Ioo (-h) 0) ⊆ V₁ ∧
        (∀ a ∈ ({-1, 1} : Set ℝ),
          (fun u => B (a, u)) '' _root_.Set.Ioo 0 h ⊆ A₀ ∧
          (fun u => B (a, u)) '' _root_.Set.Ioo (-h) 0 ⊆ A₁) ∧
        ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∃ k : ℝ, 0 < k ∧ k < h ∧
          (((Ω = Schoenflies.inside (_root_.Set.range γ) ∧
              V₀ = Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
              V₁ = Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0}))) ∧
            ∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ _root_.Set.Ioo (a - ε) (a + ε) ×ˢ _root_.Set.Ioo (-k) k,
              (B z ∈ Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ↔
                a * z.1 < 1 ∧ 0 < z.2) ∧
              (B z ∈ closure (Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0}))) ↔
                a * z.1 ≤ 1 ∧ 0 ≤ z.2) ∧
              (B z ∈ Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ↔
                a * z.1 < 1 ∧ z.2 < 0) ∧
              (B z ∈ closure (Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0}))) ↔
                a * z.1 ≤ 1 ∧ z.2 ≤ 0)) ∨
          (((Ω = Schoenflies.outside (_root_.Set.range γ) ∧
              V₀ = Schoenflies.outside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
              V₁ = Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
              Schoenflies.inside (_root_.Set.range γ) ⊆
                Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})))) ∧
            ∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ _root_.Set.Ioo (a - ε) (a + ε) ×ˢ _root_.Set.Ioo (-k) k,
              (B z ∈ Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ↔
                1 < a * z.1 ∨ z.2 < 0) ∧
              (B z ∈ closure (Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0}))) ↔
                1 ≤ a * z.1 ∨ z.2 ≤ 0) ∧
              (B z ∈ Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ↔
                a * z.1 < 1 ∧ z.2 < 0) ∧
              (B z ∈ closure (Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0}))) ↔
                a * z.1 ≤ 1 ∧ z.2 ≤ 0)) ∨
          (((Ω = Schoenflies.outside (_root_.Set.range γ) ∧
              V₀ = Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
              V₁ = Schoenflies.outside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ∧
              Schoenflies.inside (_root_.Set.range γ) ⊆
                Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})))) ∧
            ∀ a ∈ ({-1, 1} : Set ℝ), ∀ z ∈ _root_.Set.Ioo (a - ε) (a + ε) ×ˢ _root_.Set.Ioo (-k) k,
              (B z ∈ Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ↔
                a * z.1 < 1 ∧ 0 < z.2) ∧
              (B z ∈ closure (Schoenflies.inside (A₀ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0}))) ↔
                a * z.1 ≤ 1 ∧ 0 ≤ z.2) ∧
              (B z ∈ Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0})) ↔
                1 < a * z.1 ∨ 0 < z.2) ∧
              (B z ∈ closure (Schoenflies.inside (A₁ ∪ B '' (_root_.Set.Icc (-1 : ℝ) 1 ×ˢ {0}))) ↔
                1 ≤ a * z.1 ∨ 0 ≤ z.2))) := by
  have hC := isJordanCurve_range_of_isEmbedding_addCircle one_ne_zero hγ.isEmbedding
  obtain ⟨A₀, A₁, hcut, hJ₀, hJ₁, Ω, V₀, V₁, hband, hcover, hdisj,
    hn₀, hn₁, hcomp₀, hcomp₁, hcl₀, hcl₁, hupper, hlower, hedgearcs, hcases⟩ :=
      exists_cut_regions_of_attached_band hC B.toHomeomorph hh hedges havoid
  have hΩ : Schoenflies.IsRegionOf (_root_.Set.range γ) Ω := by
    rcases hcases with hc | hc | hc
    · exact Or.inl hc.1
    · exact Or.inr hc.1
    · exact Or.inr hc.1
  obtain ⟨ε, hε, hεlt, k, hk, hkh, hcorners⟩ := exists_cut_region_corner_charts hγ B hh hedges
    hΩ hband hcover hdisj hupper hlower
  refine ⟨A₀, A₁, hcut, hJ₀, hJ₁, Ω, V₀, V₁, hband, hcover, hdisj,
    hn₀, hn₁, hcomp₀, hcomp₁, hcl₀, hcl₁, hupper, hlower, hedgearcs, ε, hε, hεlt, k, hk, hkh, ?_⟩
  rcases hcases with hc | hc | hc
  · refine Or.inl ⟨hc, ?_⟩
    intro a ha z hz
    obtain ⟨h₀, hc₀, _, _, h₁, hc₁, _, _⟩ := hcorners a ha z hz
    exact ⟨hc.2.1 ▸ h₀, hc.2.1 ▸ hc₀, hc.2.2 ▸ h₁, hc.2.2 ▸ hc₁⟩
  · refine Or.inr (Or.inl ⟨hc, ?_⟩)
    have heq := (Schoenflies.jordan_curve_theorem hJ₀).inside_eq_compl_closure_outside
    rw [← hc.2.1] at heq
    intro a ha z hz
    obtain ⟨_, _, hr₀, hrc₀, h₁, hc₁, _, _⟩ := hcorners a ha z hz
    exact ⟨heq.symm ▸ hr₀, heq.symm ▸ hrc₀, hc.2.2.1 ▸ h₁, hc.2.2.1 ▸ hc₁⟩
  · refine Or.inr (Or.inr ⟨hc, ?_⟩)
    have heq := (Schoenflies.jordan_curve_theorem hJ₁).inside_eq_compl_closure_outside
    rw [← hc.2.2.1] at heq
    intro a ha z hz
    obtain ⟨h₀, hc₀, _, _, _, _, hr₁, hrc₁⟩ := hcorners a ha z hz
    exact ⟨hc.2.1 ▸ h₀, hc.2.1 ▸ hc₀, heq.symm ▸ hr₁, heq.symm ▸ hrc₁⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_cut_regions_with_corner_charts_of_attached_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_cut_regions_with_corner_charts_of_attached_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_cut_regions_with_corner_charts_of_attached_band ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_cut_regions_with_corner_charts_of_attached_band

end DifferentialGeometry.Topology.PlanarJordan
