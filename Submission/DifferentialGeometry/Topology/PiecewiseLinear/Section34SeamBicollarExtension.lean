import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamAnnulusExtensionGerm
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.EssentialPolygonProductCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.exists_annulus_map_matching_short_bicollar_charts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A W₀ W₁ : Set E} {φ σ₀ σ₁ : (Fin 3 → ℝ) × ℝ → E}
    (hφ : IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (-1 : ℝ) 1) A)
    {d : ℝ} (hd : 0 < d)
    (hσ₀ : IsPLHomeomorphOn σ₀ (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (-d) d) W₀)
    (hσ₁ : IsPLHomeomorphOn σ₁ (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (-d) d) W₁)
    (hzero₀ : ∀ x ∈ stdSimplexBoundary 2, σ₀ (x, 0) = φ (x, 0))
    (hzero₁ : ∀ x ∈ stdSimplexBoundary 2, σ₁ (x, 0) = φ (x, 0))
    (hpos₀ : σ₀ '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) d) ⊆
      φ '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hpos₁ : σ₁ '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) d) ⊆
      φ '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hneg₀ : σ₀ '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (-d) 0) ⊆
      φ '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (-1 : ℝ) 0))
    (hneg₁ : σ₁ '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (-d) 0) ⊆
      φ '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (-1 : ℝ) 0)) :
    ∃ (e : ℝ) (F : E → E), 0 < e ∧ e ≤ d ∧ IsPLHomeomorphOn F A A ∧
      _root_.Set.EqOn F id (φ '' (stdSimplexBoundary 2 ×ˢ {0})) ∧
      F '' (φ '' (stdSimplexBoundary 2 ×ˢ {(-1 : ℝ)})) =
        φ '' (stdSimplexBoundary 2 ×ˢ {(-1 : ℝ)}) ∧
      F '' (φ '' (stdSimplexBoundary 2 ×ˢ {(1 : ℝ)})) =
        φ '' (stdSimplexBoundary 2 ×ˢ {(1 : ℝ)}) ∧
      F '' (φ '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (-1 : ℝ) 0)) =
        φ '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (-1 : ℝ) 0) ∧
      F '' (φ '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1)) =
        φ '' (stdSimplexBoundary 2 ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      ∀ x ∈ stdSimplexBoundary 2, ∀ t ∈ _root_.Set.Icc (-e) e,
        F (σ₀ (x, t)) = σ₁ (x, t) := by
  let S := stdSimplexBoundary 2
  let P := φ '' (S ×ˢ _root_.Set.Icc (0 : ℝ) 1)
  let N := φ '' (S ×ˢ _root_.Set.Icc (-1 : ℝ) 0)
  let J := φ '' (S ×ˢ {(0 : ℝ)})
  let s : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ := fun z => (z.1, -z.2)
  have hS : IsPolyhedron S := by
    simpa only [simplexBoundary_stdVertices_space] using
      (isPLSphere_simplexBoundary_std 1).isPolyhedron
  have hsubp : S ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ S ×ˢ _root_.Set.Icc (-1 : ℝ) 1 :=
    _root_.Set.prod_mono_right (_root_.Set.Icc_subset_Icc (by norm_num) le_rfl)
  have hsubn : S ×ˢ _root_.Set.Icc (-1 : ℝ) 0 ⊆ S ×ˢ _root_.Set.Icc (-1 : ℝ) 1 :=
    _root_.Set.prod_mono_right (_root_.Set.Icc_subset_Icc le_rfl (by norm_num))
  have hφp : IsPLHomeomorphOn φ (S ×ˢ _root_.Set.Icc (0 : ℝ) 1) P :=
    hφ.restrict (hS.prod isHPolytope_Icc.isPolyhedron) hsubp
  have hφn : IsPLHomeomorphOn φ (S ×ˢ _root_.Set.Icc (-1 : ℝ) 0) N :=
    hφ.restrict (hS.prod isHPolytope_Icc.isPolyhedron) hsubn
  have hs (b : ℝ) :
      IsPLHomeomorphOn s (S ×ˢ _root_.Set.Icc (0 : ℝ) b) (S ×ˢ _root_.Set.Icc (-b) 0) := by
    have h := isPLHomeomorphOn_mul_add_Icc_of_neg (m := (-1 : ℝ)) (c := 0)
      (a := 0) (b := b) (a' := -b) (b' := 0) (by norm_num) (by ring) (by ring)
    exact (hS.isPLHomeomorphOn_id.prodMap h).congr (by
      rintro ⟨x, t⟩ _
      simp [s])
  have hσp {σ : (Fin 3 → ℝ) × ℝ → E} {W : Set E}
      (hσ : IsPLHomeomorphOn σ (S ×ˢ _root_.Set.Icc (-d) d) W) :
      IsPLHomeomorphOn σ (S ×ˢ _root_.Set.Icc (0 : ℝ) d) (σ '' (S ×ˢ _root_.Set.Icc (0 : ℝ) d)) :=
    hσ.restrict (hS.prod isHPolytope_Icc.isPolyhedron)
      (_root_.Set.prod_mono_right (_root_.Set.Icc_subset_Icc (by linarith) le_rfl))
  have hσn {σ : (Fin 3 → ℝ) × ℝ → E} {W : Set E}
      (hσ : IsPLHomeomorphOn σ (S ×ˢ _root_.Set.Icc (-d) d) W) :
      IsPLHomeomorphOn (σ ∘ s) (S ×ˢ _root_.Set.Icc (0 : ℝ) d)
        (σ '' (S ×ˢ _root_.Set.Icc (-d) 0)) :=
    (hs d).trans (hσ.restrict (hS.prod isHPolytope_Icc.isPolyhedron)
      (_root_.Set.prod_mono_right (_root_.Set.Icc_subset_Icc le_rfl hd.le)))
  obtain ⟨ep, Fp, hep, hepd, hFp, hFpJ, hFptop, hFpmatch⟩ :=
    hφp.exists_annulus_map_matching_short_core_charts hd
      (hσp hσ₀) (hσp hσ₁) hzero₀ hzero₁ hpos₀ hpos₁
  have hcore : (φ ∘ s) '' (S ×ˢ {(0 : ℝ)}) = J := by
    apply _root_.Set.image_congr
    rintro ⟨x, t⟩ ⟨_, ht⟩
    simp only [_root_.Set.mem_singleton_iff] at ht
    simp [s, ht]
  have htop : (φ ∘ s) '' (S ×ˢ {(1 : ℝ)}) = φ '' (S ×ˢ {(-1 : ℝ)}) := by
    rw [_root_.Set.image_comp]
    congr 1
    ext z
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      change t = 1 at ht
      subst t
      simpa [s] using hx
    · intro hz
      refine ⟨(z.1, 1), ⟨hz.1, rfl⟩, ?_⟩
      ext <;> simp_all [s]
  obtain ⟨en, Fn, hen, hend, hFn, hFnJ, hFnbot, hFnmatch⟩ :=
    ((hs 1).trans hφn).exists_annulus_map_matching_short_core_charts hd
      (hσn hσ₀) (hσn hσ₁)
      (fun x hx => by simpa [s] using hzero₀ x hx)
      (fun x hx => by simpa [s] using hzero₁ x hx) hneg₀ hneg₁
  rw [hcore] at hFnJ
  rw [htop] at hFnbot
  have hPN : P ∩ N = J := by
    apply Subset.antisymm
    · rintro z ⟨⟨x, hx, hxeq⟩, ⟨y, hy, hyeq⟩⟩
      have heq := hφ.bijOn.injOn (hsubp hx) (hsubn hy) (hxeq.trans hyeq.symm)
      subst y
      exact ⟨x, ⟨hx.1, le_antisymm hy.2.2 hx.2.1⟩, hxeq⟩
    · rintro z ⟨x, hx, rfl⟩
      exact ⟨⟨x, ⟨hx.1, hx.2.symm ▸ (by norm_num : (0 : ℝ) ∈ Icc 0 1)⟩, rfl⟩,
        ⟨x, ⟨hx.1, hx.2.symm ▸ (by norm_num : (0 : ℝ) ∈ Icc (-1) 0)⟩, rfl⟩⟩
  have hPA : P ∪ N = A := by
    rw [← hφ.image_eq, ← _root_.Set.image_union]
    congr 1
    ext z
    constructor
    · rintro (hz | hz)
      · exact hsubp hz
      · exact hsubn hz
    · intro hz
      rcases le_total 0 z.2 with ht | ht
      · exact Or.inl ⟨hz.1, ht, hz.2.2⟩
      · exact Or.inr ⟨hz.1, hz.2.1, ht⟩
  have hP : IsPolyhedron P :=
    (hS.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      hφp.isPiecewiseAffineOn hφp.bijOn.injOn
  have hN : IsPolyhedron N :=
    (hS.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      hφn.isPiecewiseAffineOn hφn.bijOn.injOn
  have hagree : _root_.Set.EqOn Fp Fn (P ∩ N) := fun z hz =>
    (hFpJ (hPN.subset hz)).trans (hFnJ (hPN.subset hz)).symm
  have hsurj : _root_.Set.SurjOn Fp (P ∩ N) (P ∩ N) := fun z hz =>
    ⟨z, hz, hFpJ (hPN.subset hz)⟩
  obtain ⟨F, hF, hFFp, hFFn⟩ :=
    exists_isPLHomeomorphOn_union hP hN hFp hFn hagree hsurj
  rw [hPA] at hF
  let e := _root_.Min.min ep en
  have hep' : e ≤ ep := min_le_left _ _
  have hen' : e ≤ en := min_le_right _ _
  refine ⟨e, F, lt_min hep hen, hep'.trans hepd, hF, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hFFp.mono (fun _ hz => (hPN.symm.subset hz).1)).trans hFpJ
  · exact (hFFn.mono (_root_.Set.image_mono (_root_.Set.prod_mono_right (by
      intro t ht
      simp only [_root_.Set.mem_singleton_iff] at ht
      subst t
      norm_num)))).image_eq.trans hFnbot
  · exact (hFFp.mono (_root_.Set.image_mono (_root_.Set.prod_mono_right (by
      intro t ht
      simp only [_root_.Set.mem_singleton_iff] at ht
      subst t
      norm_num)))).image_eq.trans hFptop
  · exact hFFn.image_eq.trans hFn.image_eq
  · exact hFFp.image_eq.trans hFp.image_eq
  · intro x hx t ht
    by_cases ht0 : 0 ≤ t
    · have htd : t ∈ _root_.Set.Icc (0 : ℝ) d := ⟨ht0, ht.2.trans (hep'.trans hepd)⟩
      rw [hFFp (hpos₀ ⟨(x, t), ⟨hx, htd⟩, rfl⟩)]
      exact hFpmatch x hx t ⟨ht0, ht.2.trans hep'⟩
    · have htd : t ∈ _root_.Set.Icc (-d) 0 := ⟨by linarith [ht.1, hep'.trans hepd], le_of_not_ge ht0⟩
      rw [hFFn (hneg₀ ⟨(x, t), ⟨hx, htd⟩, rfl⟩)]
      have h := hFnmatch x hx (-t) ⟨by linarith, by linarith [ht.1]⟩
      simpa [s] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_annulus_map_matching_short_bicollar_charts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_annulus_map_matching_short_bicollar_charts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_annulus_map_matching_short_bicollar_charts ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_annulus_map_matching_short_bicollar_charts

end DifferentialGeometry.Topology.PiecewiseLinear
