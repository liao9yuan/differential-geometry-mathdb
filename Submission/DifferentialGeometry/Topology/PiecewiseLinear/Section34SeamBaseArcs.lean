import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCorrectionComposition
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCorrectionPlacement
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalLocalChart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Classical in
theorem IsPLHomeomorphOn.seam_base_arc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {θ : ℝ × ℝ → E}
    (hθ : IsPLHomeomorphOn θ (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) K.space)
    {e : ℝ} (he1 : e ≤ 1) :
    let γ := fun t : ℝ => θ (t / 2 + 1 / 2, 0)
    IsPLHomeomorphOn γ (_root_.Set.Icc (-e) e) (γ '' _root_.Set.Icc (-e) e) ∧
      γ '' _root_.Set.Icc (-e) e ⊆ (boundaryComplex 2 K).space := by
  let I := _root_.Set.Icc (-e / 2 + 1 / 2) (e / 2 + 1 / 2)
  have hI : I ⊆ _root_.Set.Icc (0 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hη : IsPLHomeomorphOn (fun t : ℝ => t / 2 + 1 / 2) (_root_.Set.Icc (-e) e) I := by
    simpa only [I, div_eq_mul_inv, mul_comm, one_mul] using
      (isPLHomeomorphOn_mul_add_Icc (m := (1 / 2 : ℝ)) (c := 1 / 2)
        (a := -e) (b := e) (by norm_num) rfl rfl)
  have hθ' := hθ.restrict (isHPolytope_Icc.isPolyhedron.prod
    (isHPolytope_singleton (0 : ℝ)).isPolyhedron)
    (_root_.Set.prod_mono hI (singleton_subset_iff.mpr (by norm_num)))
  have hγ := (hη.trans
    (isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_prod_const (0 : ℝ))).trans hθ'
  have hbd : θ '' frontier (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
      (boundaryComplex 2 K).space := by
    obtain ⟨q, hq⟩ := isPLBall_unit_square
    rw [← hq.image_stdSimplexBoundary_eq_frontier_real_prod, ← _root_.Set.image_comp]
    exact (hq.trans hθ).image_stdSimplexBoundary_eq_boundaryComplex K rfl
  refine ⟨hγ.image_eq.symm ▸ hγ, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  apply hbd.subset
  refine ⟨(t / 2 + 1 / 2, 0), ?_, rfl⟩
  rw [frontier_prod_eq, isClosed_Icc.closure_eq, frontier_Icc (zero_le_one' ℝ)]
  refine Or.inl ⟨?_, by simp⟩
  constructor <;> linarith [ht.1, ht.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.seam_base_arc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.seam_base_arc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.seam_base_arc ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.seam_base_arc

theorem IsCylindricalDiagram.base_side_of_corrected_seam_matching
    {E F Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P A : Set E} {R : Set F} {C : Set Q} {T : Set ℝ}
    {g : E × ℝ → F} (hg : IsCylindricalDiagram g P R)
    (hends : ∀ p ∈ P, g (p, 0) = g (p, 1)) (hAP : A ⊆ P)
    {H : F → F} (hH : _root_.Set.InjOn H R) (hHA : H '' (g '' (A ×ˢ _root_.Set.Icc (0 : ℝ) 1)) =
      g '' (A ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    {κ : Q × E → F} {ν : Q → Q} {ρ : Q × ℝ → F} {γ : ℝ → E} {z : Q}
    (hνz : ν z ∈ C) (hγ : _root_.Set.MapsTo γ T P)
    (hκ : ∀ p ∈ P, κ (z, p) = g (p, 0))
    (hmatch : ∀ t ∈ T, H (κ (z, γ t)) = ρ (ν z, t))
    (hside : ρ '' (C ×ˢ T) ⊆ g '' (A ×ˢ _root_.Set.Icc (0 : ℝ) 1)) : _root_.Set.MapsTo γ T A := by
  intro t ht
  have hx : (γ t, (0 : ℝ)) ∈ P ×ˢ _root_.Set.Icc (0 : ℝ) 1 := ⟨hγ ht, by norm_num⟩
  have hmem : H (g (γ t, 0)) ∈ g '' (A ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    rw [← hκ (γ t) (hγ ht), hmatch t ht]
    exact hside ⟨(ν z, t), ⟨hνz, ht⟩, rfl⟩
  obtain ⟨y, hy, heq⟩ := hHA.symm.subset hmem
  have hyR : y ∈ R := hg.image_eq.subset (_root_.Set.image_mono (_root_.Set.prod_mono_left hAP) hy)
  have heq' := hH hyR (hg.image_eq.subset (_root_.Set.mem_image_of_mem g hx)) heq
  exact (hg.mem_image_base_iff_of_equal_ends hends hx hAP).mp (heq' ▸ hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.base_side_of_corrected_seam_matching then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.base_side_of_corrected_seam_matching"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.base_side_of_corrected_seam_matching ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.base_side_of_corrected_seam_matching

theorem ContinuousWithinAt.exists_common_disjoint_symmetric_arcs
    {E : Type*} [TopologicalSpace E] [T2Space E] {γ₀ γ₁ : ℝ → E} {e₀ e₁ : ℝ}
    (he₀ : 0 < e₀) (he₁ : 0 < e₁)
    (hγ₀ : ContinuousWithinAt γ₀ (_root_.Set.Icc (-e₀) e₀) 0)
    (hγ₁ : ContinuousWithinAt γ₁ (_root_.Set.Icc (-e₁) e₁) 0) (hne : γ₀ 0 ≠ γ₁ 0) :
    ∃ d : ℝ, 0 < d ∧ d ≤ e₀ ∧ d ≤ e₁ ∧
      Disjoint (γ₀ '' _root_.Set.Icc (-d) d) (γ₁ '' _root_.Set.Icc (-d) d) := by
  obtain ⟨U, V, hU, hV, hxU, hxV, hUV⟩ := t2_separation hne
  obtain ⟨d₀, hd₀, hd₀e, hγ₀U⟩ := ContinuousWithinAt.exists_symmetric_interval_mapsTo he₀ hγ₀
    (_root_.Set.mapsTo_univ _ _) (by simpa only [nhdsWithin_univ] using hU.mem_nhds hxU)
  obtain ⟨d₁, hd₁, hd₁e, hγ₁V⟩ := ContinuousWithinAt.exists_symmetric_interval_mapsTo he₁ hγ₁
    (_root_.Set.mapsTo_univ _ _) (by simpa only [nhdsWithin_univ] using hV.mem_nhds hxV)
  refine ⟨min d₀ d₁, lt_min hd₀ hd₁, (min_le_left _ _).trans hd₀e,
    (min_le_right _ _).trans hd₁e, hUV.mono ?_ ?_⟩
  · exact (_root_.Set.image_mono (_root_.Set.Icc_subset_Icc (neg_le_neg (min_le_left _ _))
      (min_le_left _ _))).trans hγ₀U.image_subset
  · exact (_root_.Set.image_mono (_root_.Set.Icc_subset_Icc (neg_le_neg (min_le_right _ _))
      (min_le_right _ _))).trans hγ₁V.image_subset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.ContinuousWithinAt.exists_common_disjoint_symmetric_arcs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.ContinuousWithinAt.exists_common_disjoint_symmetric_arcs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.ContinuousWithinAt.exists_common_disjoint_symmetric_arcs ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.ContinuousWithinAt.exists_common_disjoint_symmetric_arcs

open _root_.Classical in
theorem IsCylindricalDiagram.signed_sides_of_seam_matching
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P A B : Set E} {R : Set F} {g : E × ℝ → F}
    (hg : IsCylindricalDiagram g P R) (hends : ∀ p ∈ P, g (p, 0) = g (p, 1))
    (hAP : A ⊆ P) (hBP : B ⊆ P)
    {H : F → F} (hH : _root_.Set.InjOn H R)
    (hHA : H '' (g '' (A ×ˢ _root_.Set.Icc (0 : ℝ) 1)) = g '' (A ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hHB : H '' (g '' (B ×ˢ _root_.Set.Icc (0 : ℝ) 1)) = g '' (B ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    {θ : ℝ × ℝ → E}
    (hθ : IsPLHomeomorphOn θ (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1) P)
    {κ : (Fin 3 → ℝ) × E → F} {ν : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    {ρ : (Fin 3 → ℝ) × ℝ → F} {d e s : ℝ}
    (hde : d ≤ e) (hes : e ≤ s) (he1 : e ≤ 1)
    (hκ : ∀ p ∈ P, ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, κ (stdTriangleLoop t, p) = g (p, t))
    (hν : _root_.Set.MapsTo ν (stdSimplexBoundary 2) (stdSimplexBoundary 2))
    (hmatch : ∀ z ∈ stdSimplexBoundary 2, ∀ t ∈ _root_.Set.Icc (-e) e,
      H (κ (z, θ (t / 2 + 1 / 2, 0))) = ρ (ν z, t))
    (hpos : ρ '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) s) ⊆
      g '' (A ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hneg : ρ '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (-s) 0) ⊆
      g '' (B ×ˢ _root_.Set.Icc (0 : ℝ) 1)) :
    (fun t : ℝ => θ (t / 2 + 1 / 2, 0)) '' _root_.Set.Icc 0 d ⊆ A ∧
      (fun t : ℝ => θ (t / 2 + 1 / 2, 0)) '' _root_.Set.Icc (-d) 0 ⊆ B := by
  have hz : stdTriangleLoop 0 ∈ stdSimplexBoundary 2 :=
    stdTriangleLoop_image.subset (_root_.Set.mem_image_of_mem _ (by norm_num))
  have hpath {t : ℝ} (ht : t ∈ _root_.Set.Icc (-e) e) : θ (t / 2 + 1 / 2, 0) ∈ P := by
    apply hθ.bijOn.mapsTo
    refine ⟨?_, by norm_num⟩
    constructor <;> linarith [ht.1, ht.2]
  have hκzero (p) (hp : p ∈ P) : κ (stdTriangleLoop 0, p) = g (p, 0) :=
    hκ p hp 0 (by norm_num)
  constructor
  · have hsub : _root_.Set.Icc (0 : ℝ) d ⊆ _root_.Set.Icc (-e) e := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    exact (hg.base_side_of_corrected_seam_matching hends hAP hH hHA
      (hν hz) (fun _ ht => hpath (hsub ht)) hκzero
      (fun t ht => hmatch _ hz t (hsub ht))
      ((_root_.Set.image_mono (_root_.Set.prod_mono_right (_root_.Set.Icc_subset_Icc le_rfl (hde.trans hes)))).trans
        hpos)).image_subset
  · have hsub : _root_.Set.Icc (-d) (0 : ℝ) ⊆ _root_.Set.Icc (-e) e := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    exact (hg.base_side_of_corrected_seam_matching hends hBP hH hHB
      (hν hz) (fun _ ht => hpath (hsub ht)) hκzero
      (fun t ht => hmatch _ hz t (hsub ht))
      ((_root_.Set.image_mono (_root_.Set.prod_mono_right (_root_.Set.Icc_subset_Icc (neg_le_neg (hde.trans hes)) le_rfl))).trans
        hneg)).image_subset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.signed_sides_of_seam_matching then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.signed_sides_of_seam_matching"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.signed_sides_of_seam_matching ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.signed_sides_of_seam_matching

end DifferentialGeometry.Topology.PiecewiseLinear
