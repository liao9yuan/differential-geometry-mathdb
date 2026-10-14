import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34BigonNeighborhoodTrace
import Mathlib.Topology.OpenPartialHomeomorph.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology

theorem OpenPartialHomeomorph.eventually_inter_eq_singleton_of_axes
    {X : Type*} [TopologicalSpace X] {J L : Set X}
    (e : OpenPartialHomeomorph (ℝ × ℝ) X) {ε : ℝ} (hε : 0 < ε)
    (hsource : _root_.Set.Ioo (-ε) ε ×ˢ _root_.Set.Ioo (-ε) ε ⊆ e.source)
    (hJ : ∀ p ∈ _root_.Set.Ioo (-ε) ε ×ˢ _root_.Set.Ioo (-ε) ε, e p ∈ J ↔ p.1 = 0)
    (hL : ∀ p ∈ _root_.Set.Ioo (-ε) ε ×ˢ _root_.Set.Ioo (-ε) ε, e p ∈ L ↔ p.2 = 0) :
    ∀ᶠ y in 𝓝 (e (0, 0)), y ∈ J ∩ L ↔ y = e (0, 0) := by
  have hzero : (0 : ℝ) ∈ _root_.Set.Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have hopen : IsOpen (e '' (_root_.Set.Ioo (-ε) ε ×ˢ _root_.Set.Ioo (-ε) ε)) :=
    e.isOpen_image_of_subset_source (isOpen_Ioo.prod isOpen_Ioo) hsource
  filter_upwards [hopen.mem_nhds ⟨(0, 0), ⟨hzero, hzero⟩, rfl⟩] with y hy
  obtain ⟨p, hp, rfl⟩ := hy
  constructor
  · intro hpJL
    have hp0 : p = (0, 0) := Prod.ext ((hJ p hp).mp hpJL.1) ((hL p hp).mp hpJL.2)
    rw [hp0]
  · intro hep
    have hp0 := e.injOn (hsource hp) (hsource ⟨hzero, hzero⟩) hep
    rw [hp0]
    exact ⟨(hJ (0, 0) ⟨hzero, hzero⟩).mpr rfl, (hL (0, 0) ⟨hzero, hzero⟩).mpr rfl⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.OpenPartialHomeomorph
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OpenPartialHomeomorph.eventually_inter_eq_singleton_of_axes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OpenPartialHomeomorph.eventually_inter_eq_singleton_of_axes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OpenPartialHomeomorph.eventually_inter_eq_singleton_of_axes ``Submission.DifferentialGeometry.Topology.OpenPartialHomeomorph.eventually_inter_eq_singleton_of_axes

theorem OpenPartialHomeomorph.eventually_inter_eq_singleton_within_of_axes
    {X : Type*} [TopologicalSpace X] {S J L : Set X}
    (e : OpenPartialHomeomorph (ℝ × ℝ) S) {ε : ℝ} (hε : 0 < ε)
    (hsource : _root_.Set.Ioo (-ε) ε ×ˢ _root_.Set.Ioo (-ε) ε ⊆ e.source)
    (hJ : ∀ p ∈ _root_.Set.Ioo (-ε) ε ×ˢ _root_.Set.Ioo (-ε) ε, (e p : X) ∈ J ↔ p.1 = 0)
    (hL : ∀ p ∈ _root_.Set.Ioo (-ε) ε ×ˢ _root_.Set.Ioo (-ε) ε, (e p : X) ∈ L ↔ p.2 = 0) :
    ∀ᶠ y in 𝓝[S] (e (0, 0) : X), y ∈ J ∩ L ↔ y = (e (0, 0) : X) := by
  have h := OpenPartialHomeomorph.eventually_inter_eq_singleton_of_axes
    (J := ((↑) : S → X) ⁻¹' J) (L := ((↑) : S → X) ⁻¹' L) e hε hsource hJ hL
  rw [← map_nhds_subtype_val (e (0, 0))]
  change ∀ᶠ y : S in 𝓝 (e (0, 0)), (y : X) ∈ J ∩ L ↔ (y : X) = (e (0, 0) : X)
  filter_upwards [h] with y hy
  exact hy.trans ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OpenPartialHomeomorph.eventually_inter_eq_singleton_within_of_axes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OpenPartialHomeomorph.eventually_inter_eq_singleton_within_of_axes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OpenPartialHomeomorph.eventually_inter_eq_singleton_within_of_axes ``Submission.DifferentialGeometry.Topology.OpenPartialHomeomorph.eventually_inter_eq_singleton_within_of_axes

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCombinatorialManifold.exists_disk_neighborhood_with_isolated_crossings
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {B Ω J L : Set E} {p q : E}
    (hB : IsPLBall 2 B) (hBK : B ⊆ K.space) (hΩ : IsOpen Ω) (hBΩ : B ⊆ Ω)
    (hJ : IsPLSphere 1 J) (hL : IsPLSphere 1 L) (hJK : J ⊆ K.space) (hLK : L ⊆ K.space)
    (hBJ : IsPLBall 1 (B ∩ J)) (hBL : IsPLBall 1 (B ∩ L))
    (htrace : B ∩ (J ∩ L) = {p, q})
    (hisolated : ∀ x ∈ ({p, q} : Set E),
      ∀ᶠ y in 𝓝[K.space] x, y ∈ J ∩ L → y = x) :
    ∃ (N : Set E) (r : (Fin 3 → ℝ) → E) (α β : (Fin 2 → ℝ) → E),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) N ∧ N ⊆ K.space ∩ Ω ∧
      B ⊆ r '' openSimplex (stdVertices 1) ∧
      IsPLHomeomorphOn α (stdSimplex ℝ (Fin 2)) (N ∩ J) ∧
      (N ∩ J) ∩ r '' stdSimplexBoundary 2 = α '' stdSimplexBoundary 1 ∧
      IsPLHomeomorphOn β (stdSimplex ℝ (Fin 2)) (N ∩ L) ∧
      (N ∩ L) ∩ r '' stdSimplexBoundary 2 = β '' stdSimplexBoundary 1 ∧
      N ∩ (J ∩ L) = {p, q} := by
  let R := (J ∩ L) \ {p, q}
  have hR : IsClosed R := by
    apply isOpen_compl_iff.mp
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    by_cases hxJL : x ∈ J ∩ L
    · have hxpair : x ∈ ({p, q} : Set E) := by
        by_contra h
        exact hx ⟨hxJL, h⟩
      filter_upwards [eventually_nhdsWithin_iff.mp (hisolated x hxpair)] with y hy
      intro hyR
      exact hyR.2 (hy (hJK hyR.1.1) hyR.1 ▸ hxpair)
    · have hc := hJ.isPolyhedron.isClosed.inter hL.isPolyhedron.isClosed
      filter_upwards [hc.isOpen_compl.mem_nhds hxJL] with y hy
      exact fun hyR => hy hyR.1
  have hBW : B ⊆ Ω \ R := by
    intro x hx
    refine ⟨hBΩ hx, ?_⟩
    intro hxR
    exact hxR.2 (htrace.subset ⟨hx, hxR.1⟩)
  let F : Bool → Set E
    | false => J
    | true => L
  have hF : ∀ i, IsPLSphere 1 (F i) := by
    intro i
    cases i
    · exact hJ
    · exact hL
  have hFK : ∀ i, F i ⊆ K.space := by
    intro i
    cases i
    · exact hJK
    · exact hLK
  have hBF : ∀ i, IsPLBall 1 (B ∩ F i) := by
    intro i
    cases i
    · exact hBJ
    · exact hBL
  obtain ⟨N, r, f, hr, hNW, hBint, hf⟩ :=
    hK.exists_disk_neighborhood_with_crosscuts K hB hBK (hΩ.sdiff hR) hBW F hF hFK hBF
  have hBN : B ⊆ N := by
    rw [hr.image_openSimplex_stdVertices] at hBint
    exact hBint.trans _root_.Set.sdiff_subset
  refine ⟨N, r, f _root_.Bool.false, f _root_.Bool.true, hr, fun x hx => ⟨(hNW hx).1, (hNW hx).2.1⟩,
    hBint, (hf _root_.Bool.false).1, (hf _root_.Bool.false).2, (hf _root_.Bool.true).1, (hf _root_.Bool.true).2, ?_⟩
  apply Subset.antisymm
  · intro x hx
    by_contra h
    exact (hNW hx.1).2.2 ⟨hx.2, h⟩
  · intro x hx
    have hxB := htrace.symm.subset hx
    exact ⟨hBN hxB.1, hxB.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_disk_neighborhood_with_isolated_crossings then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_disk_neighborhood_with_isolated_crossings"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_disk_neighborhood_with_isolated_crossings ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_disk_neighborhood_with_isolated_crossings

end DifferentialGeometry.Topology.PiecewiseLinear
