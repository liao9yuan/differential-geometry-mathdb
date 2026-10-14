import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandComponents

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsAnnulusOn.mem_nhdsWithin_of_not_mem_ends
    {M : Type*} [TopologicalSpace M] [T2Space M] {S A A₀ A₁ : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (hA : IsAnnulusOn A A₀ A₁) (hAS : A ⊆ S) {x : M}
    (hx : x ∈ A) (hxend : x ∉ A₀ ∪ A₁) : A ∈ 𝓝[S] x := by
  have hann := hA.preimage_subtype hAS
  have hint : (⟨x, hAS hx⟩ : S) ∈ interior ((Subtype.val : S → M) ⁻¹' A) := by
    apply (mem_interior_iff_notMem_frontier
      (show (⟨x, hAS hx⟩ : S) ∈ (Subtype.val : S → M) ⁻¹' A from hx)).mpr
    intro hf
    exact hxend (hann.frontier_subset hf)
  exact preimage_coe_mem_nhds_subtype.mp (mem_interior_iff_mem_nhds.mp hint)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOn.mem_nhdsWithin_of_not_mem_ends then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOn.mem_nhdsWithin_of_not_mem_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOn.mem_nhdsWithin_of_not_mem_ends ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsAnnulusOn.mem_nhdsWithin_of_not_mem_ends

theorem IsPLCellOn.annulus_mem_nhdsWithin_of_not_mem_ends
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {S B A A₀ A₁ : Set M}
    (hS : IsPLCellOn 3 S B) (hA : IsAnnulusOn A A₀ A₁) (hAB : A ⊆ B) {x : M}
    (hx : x ∈ A) (hxend : x ∉ A₀ ∪ A₁) : A ∈ 𝓝[B] x := by
  obtain ⟨hc⟩ := hS.nonempty_chartedSpace_boundary
  let _ := hc
  exact hA.mem_nhdsWithin_of_not_mem_ends hAB hx hxend

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.annulus_mem_nhdsWithin_of_not_mem_ends then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.annulus_mem_nhdsWithin_of_not_mem_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.annulus_mem_nhdsWithin_of_not_mem_ends ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.annulus_mem_nhdsWithin_of_not_mem_ends

theorem inter_caps_eq_union_of_ordered_caps
    {X ι : Type*} [Preorder ι] {S : Set X} {D₀ D₁ : ι → Set X}
    (hU : ∀ i, D₀ i ∪ D₁ i = S) (h₀ : Monotone D₀) (h₁ : Antitone D₁)
    {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) :
    D₁ i ∩ D₀ k = (D₁ i ∩ D₀ j) ∪ (D₁ j ∩ D₀ k) := by
  apply Subset.antisymm
  · rintro x ⟨hxi, hxk⟩
    rcases (hU j).superset ((hU k).subset (Or.inl hxk)) with hxj | hxj
    · exact Or.inl ⟨hxi, hxj⟩
    · exact Or.inr ⟨hxj, hxk⟩
  · rintro x (hx | hx)
    · exact ⟨hx.1, h₀ hjk hx.2⟩
    · exact ⟨h₁ hij hx.1, hx.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.inter_caps_eq_union_of_ordered_caps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.inter_caps_eq_union_of_ordered_caps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.inter_caps_eq_union_of_ordered_caps ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.inter_caps_eq_union_of_ordered_caps

theorem exists_neighborhood_lateral_pair_cover
    {M : Type*} [TopologicalSpace M] [T2Space M] {S A₀ A₁ T : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {f g : (Fin 3 → ℝ) × ℝ → M}
    (hf : _root_.Set.InjOn f (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hg : _root_.Set.InjOn g (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hann : IsAnnulusOn
      (f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∪
        g '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1)) A₀ A₁)
    (hS : f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∪
      g '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ S)
    (hfends : f '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      f '' (stdSimplexBoundary 2 ×ˢ {1}) ⊆ T)
    (hgends : g '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      g '' (stdSimplexBoundary 2 ×ˢ {1}) ⊆ T) {x : M}
    (hx : x ∈ f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∪
      g '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hxend : x ∉ A₀ ∪ A₁) :
    ∃ V : Set M, V ∈ 𝓝 x ∧ V ∩ S ⊆
      f '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Ioo (0 : ℝ) 1) ∪
        g '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Ioo (0 : ℝ) 1) ∪ T := by
  have hnhds := hann.mem_nhdsWithin_of_not_mem_ends hS hx hxend
  obtain ⟨V, hV, hcover⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hnhds
  refine ⟨V, hV, ?_⟩
  intro y hy
  rcases hcover hy with hyf | hyg
  · by_cases hyt : y ∈ f '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
        f '' (stdSimplexBoundary 2 ×ˢ {1})
    · exact Or.inr (hfends hyt)
    · exact Or.inl (Or.inl ((image_lateral_open_eq_sdiff_ends hf).superset ⟨hyf, hyt⟩))
  · by_cases hyt : y ∈ g '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
        g '' (stdSimplexBoundary 2 ×ˢ {1})
    · exact Or.inr (hgends hyt)
    · exact Or.inl (Or.inr ((image_lateral_open_eq_sdiff_ends hg).superset ⟨hyg, hyt⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_neighborhood_lateral_pair_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_neighborhood_lateral_pair_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_neighborhood_lateral_pair_cover ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_neighborhood_lateral_pair_cover

end DifferentialGeometry.Topology.PiecewiseLinear
