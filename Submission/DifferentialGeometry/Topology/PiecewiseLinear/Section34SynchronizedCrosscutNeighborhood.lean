import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SynchronizedFillingEnlargement
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SynchronizedBaseArcs
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34ExpandedSquareCrossingChartsSwap
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CollaredCylinderFrontier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Classical in
theorem Section34SeamMarkedBandFilling.exists_crosscut_neighborhood_avoiding
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {Cc Cp Cq As Bs S T D F J₀ J₁ : Set M}
    (h : Section34SeamMarkedBandFilling Cc Cp Cq As Bs S T D F J₀ J₁)
    {Z : Set M} (hZ : IsClosed Z) (hZsheet : Z ⊆ As ∪ Bs)
    (hZfaces : Disjoint Z (D ∪ F)) :
    ∃ (P V : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M)
      (N X Y : Set (ℝ × ℝ)) (H : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3))
      (δ ε : ℝ → ℝ × ℝ) (p : Fin 2 → ℝ × ℝ)
      (e : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) (r : Fin 2 → ℝ),
      (IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = Cc ∧
      V ⊆ interior P ∧ u '' V ⊆ interior S ∧ IsPLBall 2 N ∧ IsCombinatorialSolidTorus V ∧
      IsCylindricalDiagram H N V ∧ (∀ z ∈ N, H (z, 0) = H (z, 1)) ∧
      frontier V = H '' (frontier N ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      IsPLHomeomorphOn δ (_root_.Set.Icc 0 1) X ∧ IsPLHomeomorphOn ε (_root_.Set.Icc 0 1) Y ∧
      X ⊆ N ∧ Y ⊆ N ∧ X ∩ frontier N = {δ 0, δ 1} ∧
      Y ∩ frontier N = {ε 0, ε 1} ∧ X ∩ Y = {p 0, p 1} ∧
      p 0 ≠ p 1 ∧ (∀ k, p k ∈ interior N) ∧
      (∀ k, (u ∘ H) '' ({p k} ×ˢ _root_.Set.Icc (0 : ℝ) 1) = ![J₀, J₁] k) ∧
      u '' V ∩ As = (u ∘ H) '' (X ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      u '' V ∩ Bs = (u ∘ H) '' (Y ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      (∀ k, 0 < r k ∧ IsPLHomeomorphOn (e k) (e k).source (e k).target ∧
        e k (0, 0) = p k ∧ _root_.Set.Ioo (-r k) (r k) ×ˢ _root_.Set.Ioo (-r k) (r k) ⊆ (e k).source ∧
        (∀ z ∈ _root_.Set.Ioo (-r k) (r k) ×ˢ _root_.Set.Ioo (-r k) (r k), e k z ∈ X ↔ z.2 = 0) ∧
        ∀ s ∈ _root_.Set.Ioo (-r k) (r k), e k (0, s) ∈ Y)) ∧
      Disjoint (u '' V) Z := by
  obtain ⟨P, u, R, g, H, a, A₀, A₁, δ₀, δ₁, C, f, α, β, ρ, L, W, c, θ, b, ν,
    ⟨hP, hu, hcell, -, -, -, _, _, _, hδ₀, hδ₁, hδ₀₀, hδ₀₁, hδ₁₀, hδ₁₁,
    hcover, hinter, _, _, hCdis, hfamily, hc, _, hVP, hsupport, _, _, _,
    hH, hHends, hHeq, _, hframe, _, _, htraceA, htraceB⟩, havoid⟩ :=
      h.exists_synchronized_enlargement_avoiding hZ hZsheet hZfaces
  let Q := _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1
  let N := _root_.Set.Icc (-c) (1 + c) ×ˢ _root_.Set.Icc (-c) (1 + c)
  let d := _root_.Min.min (b 0) (b 1)
  let γ := fun (k : Fin 2) (t : ℝ) => θ k (t / 2 + 1 / 2, 0)
  let η₀ := fun (k : Fin 2) (t : ℝ) => section34SquareShellFlatten c (γ k (-t / 2), t)
  let η₁ := fun (k : Fin 2) (t : ℝ) => section34SquareShellFlatten c (γ k (t / 2), t)
  let X := A₀ ∪ (η₀ 0 '' _root_.Set.Icc 0 c ∪ η₀ 1 '' _root_.Set.Icc 0 c)
  let Y := A₁ ∪ (η₁ 0 '' _root_.Set.Icc 0 c ∪ η₁ 1 '' _root_.Set.Icc 0 c)
  obtain ⟨_, hdb, hγ, hγbd, hγzero, hdis⟩ := synchronized_base_arcs
    (fun k => (hframe k).1) (fun k => (hframe k).2.1)
    (fun k => (hframe k).2.2.1) (fun k => (hframe k).2.2.2.1)
    (fun k => (hframe k).2.2.2.2.2.1.bijOn.mapsTo)
    (fun k => (hfamily k).1) hCdis
    (fun k => (hframe k).2.2.2.2.2.2.2.2.2.2.1)
    (fun k => (hframe k).2.2.2.2.2.2.2.2.2.2.2)
  change ∀ k, γ k 0 = a k at hγzero
  have hcd : c ≤ 2 * d := by
    have h : c / 2 ≤ d := le_min (hframe 0).2.2.2.2.1 (hframe 1).2.2.2.2.1
    linarith
  have hAbd : A₀ ⊆ frontier Q := subset_union_left.trans hcover.subset
  have hBbd : A₁ ⊆ frontier Q := subset_union_right.trans hcover.subset
  obtain ⟨δ, ε, hδ, hε, -, -, -, -, hXN, hYN, -, -, hXends, hYends, hXY⟩ :=
    exists_expanded_square_crosscuts hδ₀ hδ₁ (hδ₁₀.trans hδ₀₀.symm)
      (hδ₁₁.trans hδ₀₁.symm) hAbd hBbd (hinter.trans (by rw [hδ₀₀, hδ₀₁]))
      hc hcd hγ hγbd ((hγzero 0).trans hδ₀₀.symm)
      ((hγzero 1).trans hδ₀₁.symm) hdis
  have hpos (k : Fin 2) : γ k '' _root_.Set.Icc (0 : ℝ) d ⊆ A₀ :=
    (_root_.Set.image_mono (_root_.Set.Icc_subset_Icc le_rfl (hdb k))).trans (hframe k).2.2.2.2.2.2.2.1
  have hneg (k : Fin 2) : γ k '' _root_.Set.Icc (-d) 0 ⊆ A₁ :=
    (_root_.Set.image_mono (_root_.Set.Icc_subset_Icc (neg_le_neg (hdb k)) le_rfl)).trans
      (hframe k).2.2.2.2.2.2.2.2.1
  have hpair : A₀ ∩ A₁ = {γ 0 0, γ 1 0} := by rw [hγzero, hγzero]; exact hinter
  have hex := exists_swapped_axis_charts_of_expanded_square_paths hc hcd hγ hγbd hdis
    hAbd hpair hpos hneg
  choose e r hr he hcenter hsource hcurve haxis using hex
  have hN : IsPLBall 2 N :=
    isPLBall_two_prod (isPLBall_Icc (by linarith)) (isPLBall_Icc (by linarith))
  have hQint : Q ⊆ interior N := by
    rw [interior_prod_eq, interior_Icc]
    rintro p hp
    exact ⟨by constructor <;> linarith [hp.1.1, hp.1.2],
      by constructor <;> linarith [hp.2.1, hp.2.2]⟩
  have haQ (k : Fin 2) : a k ∈ Q := by
    rw [← hγzero k]
    exact (isClosed_Icc.prod isClosed_Icc).frontier_subset
      (hγbd k (_root_.Set.mem_image_of_mem _ (by constructor <;> linarith [hc, hcd])))
  have hane : a 0 ≠ a 1 := by
    intro heq
    have hh := hδ₀.bijOn.injOn (by norm_num : (0 : ℝ) ∈ Icc 0 1)
      (by norm_num : (1 : ℝ) ∈ Icc 0 1) (hδ₀₀.trans (heq.trans hδ₀₁.symm))
    norm_num at hh
  have hunion (T : Fin 2 → Set (ℝ × ℝ)) : (⋃ k, T k) = T 0 ∪ T 1 := by
    ext x
    simp only [_root_.Set.mem_iUnion, _root_.Set.mem_union]
    constructor
    · rintro ⟨k, hk⟩
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr hk
    · rintro (hx | hx)
      · exact ⟨0, hx⟩
      · exact ⟨1, hx⟩
  refine ⟨P, R.space ∪ W, u, N, X, Y, H, δ, ε, a, e, r, ?_, havoid⟩
  refine ⟨hP, hu, hcell, hVP, hsupport, hN, hH.isCombinatorialSolidTorus hN (by simp),
    hH, hHends, hH.frontier_eq_image_base_frontier hN (by simp) (by simp),
    hδ, hε, hXN, hYN, hXends, hYends, ?_, hane, fun k => hQint (haQ k), ?_, ?_, ?_, ?_⟩
  · simpa only [hδ₀₀, hδ₀₁] using hXY
  · intro k
    rw [_root_.Set.image_comp, (hHeq.mono (_root_.Set.prod_mono_left (singleton_subset_iff.mpr (haQ k)))).image_eq,
      ← _root_.Set.image_comp]
    exact (hframe k).2.2.2.2.2.2.2.2.2.1
  · simpa only [hunion] using htraceA
  · simpa only [hunion] using htraceB
  · intro k
    exact ⟨hr k, he k, (hcenter k).trans (hγzero k), hsource k, hcurve k, haxis k⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamMarkedBandFilling.exists_crosscut_neighborhood_avoiding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamMarkedBandFilling.exists_crosscut_neighborhood_avoiding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamMarkedBandFilling.exists_crosscut_neighborhood_avoiding ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamMarkedBandFilling.exists_crosscut_neighborhood_avoiding

open _root_.Classical in
theorem Section34SeamMarkedBandFilling.exists_crosscut_neighborhood
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {Cc Cp Cq As Bs S T D F J₀ J₁ : Set M}
    (h : Section34SeamMarkedBandFilling Cc Cp Cq As Bs S T D F J₀ J₁) :
    ∃ (P V : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M)
      (N X Y : Set (ℝ × ℝ)) (H : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3))
      (δ ε : ℝ → ℝ × ℝ) (p : Fin 2 → ℝ × ℝ)
      (e : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) (r : Fin 2 → ℝ),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ u '' P = Cc ∧
      V ⊆ interior P ∧ u '' V ⊆ interior S ∧ IsPLBall 2 N ∧ IsCombinatorialSolidTorus V ∧
      IsCylindricalDiagram H N V ∧ (∀ z ∈ N, H (z, 0) = H (z, 1)) ∧
      frontier V = H '' (frontier N ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      IsPLHomeomorphOn δ (_root_.Set.Icc 0 1) X ∧ IsPLHomeomorphOn ε (_root_.Set.Icc 0 1) Y ∧
      X ⊆ N ∧ Y ⊆ N ∧ X ∩ frontier N = {δ 0, δ 1} ∧
      Y ∩ frontier N = {ε 0, ε 1} ∧ X ∩ Y = {p 0, p 1} ∧
      p 0 ≠ p 1 ∧ (∀ k, p k ∈ interior N) ∧
      (∀ k, (u ∘ H) '' ({p k} ×ˢ _root_.Set.Icc (0 : ℝ) 1) = ![J₀, J₁] k) ∧
      u '' V ∩ As = (u ∘ H) '' (X ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      u '' V ∩ Bs = (u ∘ H) '' (Y ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      (∀ k, 0 < r k ∧ IsPLHomeomorphOn (e k) (e k).source (e k).target ∧
        e k (0, 0) = p k ∧ _root_.Set.Ioo (-r k) (r k) ×ˢ _root_.Set.Ioo (-r k) (r k) ⊆ (e k).source ∧
        (∀ z ∈ _root_.Set.Ioo (-r k) (r k) ×ˢ _root_.Set.Ioo (-r k) (r k), e k z ∈ X ↔ z.2 = 0) ∧
        ∀ s ∈ _root_.Set.Ioo (-r k) (r k), e k (0, s) ∈ Y) := by
  obtain ⟨P, V, u, N, X, Y, H, δ, ε, p, e, r, hdata, -⟩ :=
    h.exists_crosscut_neighborhood_avoiding isClosed_empty (_root_.Set.empty_subset _) (_root_.Set.empty_disjoint _)
  exact ⟨P, V, u, N, X, Y, H, δ, ε, p, e, r, hdata⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamMarkedBandFilling.exists_crosscut_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamMarkedBandFilling.exists_crosscut_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamMarkedBandFilling.exists_crosscut_neighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamMarkedBandFilling.exists_crosscut_neighborhood

end DifferentialGeometry.Topology.PiecewiseLinear
