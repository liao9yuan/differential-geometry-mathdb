/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.OneManifoldBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open _root_.Classical in
private theorem singleton_mem_preimage_faces_of_mem_boundary
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    (G : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (φ : E → F) {m n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (m + 1) K)
    (hL : IsCombinatorialManifold (n + 1) L) (hdim : Module.finrank ℝ F = m + n + 1)
    (hcarrier : ∀ u ∈ G.faces, ∃ s ∈ K.faces, ∃ t ∈ L.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (s : Set E) ∩
        simplicialMap K φ ⁻¹' convexHull ℝ (t : Set F))
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ v))
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t : Set F)).Nonempty →
        vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t : Set F) = ⊤)
    {x : E} (hx : x ∈ G.space) (hxB : x ∈ (boundaryComplex (m + 1) K).space) :
    {x} ∈ G.faces := by
  obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex G hx
  obtain ⟨s, hs, t, ht, hsub⟩ := hcarrier u hu
  obtain ⟨b, hb, hxb⟩ := (boundaryComplex (m + 1) K).mem_space_iff.mp hxB
  have hbK := boundaryComplex_faces_subset (m + 1) K hb
  have hxc := openSimplex_subset_convexHull u hxu
  have hxw : x ∈ convexHull ℝ ((s ∩ b : Finset E) : Set E) := by
    simpa only [Finset.coe_inter] using K.inter_subset_convexHull hs hbK ⟨(hsub hxc).1, hxb⟩
  have hwne : (s ∩ b).Nonempty := by
    by_contra h
    have hempty := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [hempty, Finset.coe_empty, convexHull_empty, Set.mem_empty_iff_false] at hxw
  have hw := K.down_closed hs Finset.inter_subset_left hwne
  have huw : (u : Set E) ⊆ convexHull ℝ ((s ∩ b : Finset E) : Set E) :=
    subset_convexHull_of_mem_openSimplex (K.indep hs) Finset.inter_subset_left
      (fun z hz => (hsub (subset_convexHull ℝ _ hz)).1) hxu hxw
  have hbound := card_add_finrank_le_of_preimage_transverse_faces K L φ hw ht
    (G.indep hu) (G.nonempty_of_mem_faces hu) (hind _ hw)
    (fun z hz => ⟨huw hz, (hsub (subset_convexHull ℝ _ hz)).2⟩)
    (htrans _ hw _ ht ⟨simplicialMap K φ x,
      simplicialMap_mem_convexHull_image K φ hw hxw, (hsub hxc).2⟩)
  have hbcard := ((hK.mem_boundaryComplex_faces_iff K).mp hb).2.1
  have hwcard := Finset.card_le_card (Finset.inter_subset_right (s₁ := s) (s₂ := b))
  have htcard := hL.card_le L ht
  have hup := Finset.card_pos.mpr (G.nonempty_of_mem_faces hu)
  have hucard : u.card = 1 := by omega
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hucard
  have hxv : x = v := by
    simpa only [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] using hxc
  rwa [hxv]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.singleton_mem_preimage_faces_of_mem_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.singleton_mem_preimage_faces_of_mem_boundary target :: scope.openDecls } }

open _root_.Classical in
theorem boundaryComplex_space_preimage_of_transverse_faces
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    (G : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces] [Finite G.faces]
    (φ : E → F) {m n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (m + 1) K)
    (hL : IsCombinatorialManifold (n + 1) L) (hdim : Module.finrank ℝ F = m + n + 1)
    (hspace : G.space = K.space ∩ simplicialMap K φ ⁻¹' L.space)
    (hcarrier : ∀ u ∈ G.faces, ∃ s ∈ K.faces, ∃ t ∈ L.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (s : Set E) ∩
        simplicialMap K φ ⁻¹' convexHull ℝ (t : Set F))
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ v))
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t : Set F)).Nonempty →
        vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t : Set F) = ⊤) :
    (boundaryComplex 1 G).space = (boundaryComplex (m + 1) K).space ∩
      simplicialMap K φ ⁻¹' L.space := by
  have hG := isCombinatorialManifoldWithBoundary_preimage_of_transverse_faces K L G φ
    hK hL hdim hspace hcarrier hind htrans
  have hcard : ∀ u ∈ G.faces, u.card ≤ 2 := fun u hu => hG.card_le G hu
  have hdegree := fun {x : E} (hx : {x} ∈ G.faces) =>
    neighbors_singleton_or_pair_of_preimage_transverse_faces K L G φ
      hK hL hdim hcard hspace hcarrier hind htrans hx
  ext x
  constructor
  · intro hx
    have hxspace := boundaryComplex_space_subset 1 G hx
    rw [hspace] at hxspace
    obtain ⟨hxv, hs⟩ := (mem_boundaryComplex_one_space_iff G hcard).mp hx
    refine ⟨?_, hxspace.2⟩
    rcases hdegree hxv with ⟨hxb, _⟩ | ⟨_, hp⟩
    · exact hxb
    · have h1 := Set.ncard_eq_one.mpr hs
      have h2 := Set.ncard_eq_two.mpr hp
      omega
  · rintro ⟨hxB, hxL⟩
    have hxG : x ∈ G.space := hspace.symm ▸
      ⟨boundaryComplex_space_subset (m + 1) K hxB, hxL⟩
    have hxv := singleton_mem_preimage_faces_of_mem_boundary K L G φ hK hL hdim
      hcarrier hind htrans hxG hxB
    apply (mem_boundaryComplex_one_space_iff G hcard).mpr
    refine ⟨hxv, ?_⟩
    rcases hdegree hxv with ⟨_, hs⟩ | ⟨hxb, _⟩
    · exact hs
    · exact (hxb hxB).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_preimage_of_transverse_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_preimage_of_transverse_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_preimage_of_transverse_faces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_preimage_of_transverse_faces

open _root_.Classical in
theorem even_ncard_boundary_preimage_of_transverse_faces
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces] [Finite L.faces] (φ : E → F) {m n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (m + 1) K)
    (hL : IsCombinatorialManifold (n + 1) L) (hdim : Module.finrank ℝ F = m + n + 1)
    (hind : ∀ s ∈ K.faces, AffineIndependent ℝ (fun v : s => φ v))
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t : Set F)).Nonempty →
        vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t : Set F) = ⊤) :
    Even ((boundaryComplex (m + 1) K).space ∩ simplicialMap K φ ⁻¹' L.space).ncard := by
  obtain ⟨G, hfinite, hspace, hcarrier⟩ := exists_triangulation_preimage_of_transverse_faces
    K L φ hind htrans
  let _ : Finite G.faces := hfinite.to_subtype
  have hcar : ∀ u ∈ G.faces, ∃ s ∈ K.faces, ∃ t ∈ L.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (s : Set E) ∩
        simplicialMap K φ ⁻¹' convexHull ℝ (t : Set F) := by
    intro u hu
    obtain ⟨s, hs, t, ht, hsub, _⟩ := hcarrier u hu
    exact ⟨s, hs, t, ht, hsub⟩
  have hG := isCombinatorialManifoldWithBoundary_preimage_of_transverse_faces K L G φ
    hK hL hdim hspace hcar hind htrans
  rw [← boundaryComplex_space_preimage_of_transverse_faces K L G φ hK hL hdim
    hspace hcar hind htrans]
  exact hG.even_ncard_boundaryComplex_one_space G

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.even_ncard_boundary_preimage_of_transverse_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.even_ncard_boundary_preimage_of_transverse_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.even_ncard_boundary_preimage_of_transverse_faces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.even_ncard_boundary_preimage_of_transverse_faces

open _root_.Classical in
theorem even_ncard_boundary_preimage_of_transverse_boundary
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces] [Finite L.faces] (φ : E → F) {m n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (m + 1) K)
    (hL : IsCombinatorialManifold (n + 1) L) (hdim : Module.finrank ℝ F = m + n + 1)
    (hB : ∀ s ∈ (boundaryComplex (m + 1) K).faces,
      AffineIndependent ℝ (fun v : s => φ v) ∧
        ∀ t ∈ L.faces,
          (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t : Set F)).Nonempty →
            vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t : Set F) = ⊤) :
    Even ((boundaryComplex (m + 1) K).space ∩ simplicialMap K φ ⁻¹' L.space).ncard := by
  obtain ⟨R, ψ, G, hR, hfinite, _, _, _, hfix, hgood, _⟩ :=
    exists_small_simplicialMap_preimage_manifold_relative K (boundaryComplex (m + 1) K) L
      (boundaryComplex_faces_subset (m + 1) K) hK hL hdim φ hB (by norm_num : (0 : ℝ) < 1)
  let _ : Finite R.faces := hfinite.to_subtype
  have heven := even_ncard_boundary_preimage_of_transverse_faces R L ψ
    (hK.of_isSubdivision hR) hL hdim (fun s hs => (hgood s hs).1)
    (fun s hs => (hgood s hs).2.2)
  have hboundary := boundaryComplex_space_of_isSubdivision K R hK hR
  rw [hboundary] at heven
  have heq : (boundaryComplex (m + 1) K).space ∩ simplicialMap R ψ ⁻¹' L.space =
      (boundaryComplex (m + 1) K).space ∩ simplicialMap K φ ⁻¹' L.space := by
    ext x
    constructor
    · rintro ⟨hx, hfx⟩
      exact ⟨hx, by simpa only [Set.mem_preimage, hfix hx] using hfx⟩
    · rintro ⟨hx, hfx⟩
      exact ⟨hx, by simpa only [Set.mem_preimage, hfix hx] using hfx⟩
  rwa [heq] at heven

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.even_ncard_boundary_preimage_of_transverse_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.even_ncard_boundary_preimage_of_transverse_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.even_ncard_boundary_preimage_of_transverse_boundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.even_ncard_boundary_preimage_of_transverse_boundary
end DifferentialGeometry.Topology.PiecewiseLinear
