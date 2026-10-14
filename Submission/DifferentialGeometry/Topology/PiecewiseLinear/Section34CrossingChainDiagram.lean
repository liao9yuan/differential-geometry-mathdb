import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCellChain
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedCellPageAlignment
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34PageCellGluing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem inter_eq_of_subset_of_inter_eq {E : Type*} {C N A B : Set E}
    (hCN : C ⊆ N) (hN : N ∩ A = N ∩ B) : C ∩ A = C ∩ B := by
  have h := congrArg (fun S => C ∩ S) hN
  rwa [← _root_.Set.inter_assoc, inter_eq_left.mpr hCN, ← _root_.Set.inter_assoc, inter_eq_left.mpr hCN] at h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.inter_eq_of_subset_of_inter_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.inter_eq_of_subset_of_inter_eq target :: scope.openDecls } }

open _root_.Classical in
theorem Section34CrossingCellChain.exists_untwisted_page_diagram
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {R Γ : Geometry.SimplicialComplex ℝ E} [Finite R.faces]
    {S₀ S₁ N X Y W₀ W₁ : Set E} {P : Fin 4 → Set E}
    (chain : Section34CrossingCellChain R Γ S₀ S₁ N)
    (hΓR : Γ.faces ⊆ R.faces) (hΓint : Γ.space ⊆ interior R.space)
    (hNX : N ∩ S₀ = N ∩ frontier X) (hNY : N ∩ S₁ = N ∩ frontier Y)
    (hNW₀ : N ∩ S₀ = N ∩ W₀) (hNW₁ : N ∩ S₁ = N ∩ W₁)
    (hP₀ : P 0 = W₀ ∩ Y) (hP₂ : P 2 = W₀ \ interior Y)
    (hP₁ : P 1 = W₁ ∩ X) (hP₃ : P 3 = W₁ \ interior X)
    (hcross : ∀ x ∈ Γ.space, HasPLCrossingAt S₀ S₁ x)
    (hball₀ : ∀ x ∈ Γ.space, ∀ O ∈ 𝓝 x,
      ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (g : EuclideanSpace ℝ (Fin 2) → E),
        0 < r ∧ ContinuousOn g (Metric.ball c r) ∧ _root_.Set.InjOn g (Metric.ball c r) ∧
          _root_.Set.MapsTo g (Metric.ball c r) (S₀ ∩ O) ∧ g c = x)
    (hball₁ : ∀ x ∈ Γ.space, ∀ O ∈ 𝓝 x,
      ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (g : EuclideanSpace ℝ (Fin 2) → E),
        0 < r ∧ ContinuousOn g (Metric.ball c r) ∧ _root_.Set.InjOn g (Metric.ball c r) ∧
          _root_.Set.MapsTo g (Metric.ball c r) (S₁ ∩ O) ∧ g c = x)
    (hX : IsClosed X) (hY : IsClosed Y)
    (hregX : closure (interior X) = X) (hregY : closure (interior Y) = Y) :
    ∃ f : (ℝ × ℝ) × ℝ → E,
      IsCylindricalDiagram f spliceSquare (derivedNeighborhood R Γ).space ∧
      (∀ x ∈ spliceSquare, f (x, 0) = f (x, 1)) ∧
      (∀ i, f '' section34MarkedRibbon i = (derivedNeighborhood R Γ).space ∩ P i) ∧
      f '' section34MarkedAxis = Γ.space ∧
      f '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2) =
        (derivedNeighborhood R Γ).space ∩ S₀ ∧
      f '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3) =
        (derivedNeighborhood R Γ).space ∩ S₁ ∧
      (derivedNeighborhood R Γ).space ⊆ N ∧
      Γ.space ⊆ interior (derivedNeighborhood R Γ).space := by
  have hcenter (k : ℕ) : chain.cellMap k (0, 1 / 2) ∈ Γ.space := by
    rw [chain.centerValue]
    exact Γ.convexHull_subset_space (chain.faceMem k)
      ((chain.face k).centroid_mem_convexHull (Γ.nonempty_of_mem_faces (chain.faceMem k)))
  have hlocal (k : ℕ) : ∃ H : (ℝ × ℝ) × ℝ → E,
      IsPLHomeomorphOn H spliceCylinder (derivedNeighborhoodCell R (chain.face k)).space ∧
      (∀ t, H (0, t) = chain.cellMap k (0, t)) ∧
      (∀ T : Set ℝ, H '' (spliceSquare ×ˢ T) = chain.cellMap k '' (spliceSquare ×ˢ T)) ∧
      ∀ i, H '' section34MarkedRibbon i =
        (derivedNeighborhoodCell R (chain.face k)).space ∩ P i := by
    exact exists_marked_cell_page_alignment (chain.cellChart k)
      (chain.firstSheet k) (chain.secondSheet k)
      (inter_eq_of_subset_of_inter_eq (chain.cellInside k) hNX)
      (inter_eq_of_subset_of_inter_eq (chain.cellInside k) hNY)
      (chain.centerValue k ▸ chain.centerInterior k) (hcross _ (hcenter k))
      (hball₀ _ (hcenter k)) (hball₁ _ (hcenter k)) hX hY hregX hregY
      (chain.cellInside k) hNW₀ hNW₁ hP₀ hP₂ hP₁ hP₃
  choose H hH haxis hfaces hpages using hlocal
  have hcore (k : ℕ) : H k '' section34MarkedAxis =
      (derivedNeighborhoodCell R (chain.face k)).space ∩ Γ.space := by
    rw [← chain.coreTrace]
    apply _root_.Set.image_congr
    rintro ⟨v, t⟩ ⟨hv, -⟩
    have hv0 : v = 0 := hv
    subst v
    exact haxis k t
  obtain ⟨f, hf, hends, -, hstrips, hcoref⟩ :=
    exists_untwisted_diagram_of_cyclic_page_cells chain.countGe
      (fun k _ => hH k)
      (fun k hk => (hfaces k {1}).trans
        ((chain.capMatch k hk).trans (hfaces (k + 1) {0}).symm))
      (fun k hk => (chain.adjacent k hk).trans (hfaces k {1}).symm)
      (chain.closing.trans (hfaces 0 {0}).symm) chain.farDisjoint
      ((hfaces chain.count {1}).trans (chain.capClose.trans (hfaces 0 {0}).symm))
      (fun k _ => hpages k) (fun k _ => hcore k)
  have hRN : (derivedNeighborhood R Γ).space ⊆ N := by
    rw [← chain.cellCover]
    exact _root_.Set.iUnion₂_subset fun k _ => chain.cellInside k
  have hΓRN : Γ.space ⊆ interior (derivedNeighborhood R Γ).space := by
    intro x hx
    apply mem_interior_iff_mem_nhds.mpr
    have h := derivedNeighborhood_mem_nhdsWithin hΓR hx
    rwa [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp (hΓint hx))] at h
  have hW₀ : P 0 ∪ P 2 = W₀ := by
    rw [hP₀, hP₂]
    ext x
    simp only [_root_.Set.mem_union, _root_.Set.mem_inter_iff, _root_.Set.mem_sdiff]
    constructor
    · exact fun h => h.elim And.left And.left
    · intro hx
      by_cases hxi : x ∈ interior Y
      · exact Or.inl ⟨hx, interior_subset hxi⟩
      · exact Or.inr ⟨hx, hxi⟩
  have hW₁ : P 1 ∪ P 3 = W₁ := by
    rw [hP₁, hP₃]
    ext x
    simp only [_root_.Set.mem_union, _root_.Set.mem_inter_iff, _root_.Set.mem_sdiff]
    constructor
    · exact fun h => h.elim And.left And.left
    · intro hx
      by_cases hxi : x ∈ interior X
      · exact Or.inl ⟨hx, interior_subset hxi⟩
      · exact Or.inr ⟨hx, hxi⟩
  rw [chain.cellCover] at hf hcoref
  have hstrips' (i : Fin 4) : f '' section34MarkedRibbon i =
      (derivedNeighborhood R Γ).space ∩ P i := by
    simpa only [section34MarkedRibbon, chain.cellCover] using hstrips i
  refine ⟨f, hf, hends, hstrips', ?_, ?_, ?_, hRN, hΓRN⟩
  · exact hcoref.trans (inter_eq_right.mpr (hΓRN.trans interior_subset))
  · rw [_root_.Set.image_union, hstrips' 0, hstrips' 2, ← _root_.Set.inter_union_distrib_left, hW₀]
    exact (inter_eq_of_subset_of_inter_eq hRN hNW₀).symm
  · rw [_root_.Set.image_union, hstrips' 1, hstrips' 3, ← _root_.Set.inter_union_distrib_left, hW₁]
    exact (inter_eq_of_subset_of_inter_eq hRN hNW₁).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCellChain.exists_untwisted_page_diagram then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCellChain.exists_untwisted_page_diagram"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCellChain.exists_untwisted_page_diagram ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingCellChain.exists_untwisted_page_diagram

end DifferentialGeometry.Topology.PiecewiseLinear
