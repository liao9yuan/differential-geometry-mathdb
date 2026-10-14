import Submission.DifferentialGeometry.Topology.Embedding.AmbientIsotopy
import Submission.DifferentialGeometry.Topology.Embedding.Factor
import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace Manifold
open _root_.Manifold

open _root_.Manifold in
private theorem exists_height_preserving_diffeomorph_of_ambient_isotopy
    {F M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {e : ℝ × M → F × ℝ} {a b c : ℝ} (hc : c ∈ _root_.Set.Icc a b)
    (hheight : ∀ t ∈ _root_.Set.Icc a b, ∀ x, (e (t, x)).2 = t)
    (Φ : ℝ → F ≃ₘ[ℝ] F)
    (hΦ : ContDiff ℝ ∞ (fun q : ℝ × F => Φ q.1 q.2))
    (hΦi : ContDiff ℝ ∞ (fun q : ℝ × F => (Φ q.1).symm q.2))
    (hΦe : ∀ t ∈ _root_.Set.Icc a b, ∀ x,
      Φ t (e (a, x)).1 = (e (t, x)).1 ∧
      (Φ t).symm (e (t, x)).1 = (e (a, x)).1)
    {K U : Set F} (hK : IsCompact K) (hKU : K ⊆ U)
    (hfix : ∀ t : ℝ, _root_.Set.EqOn (Φ t) id Kᶜ ∧ _root_.Set.EqOn (Φ t).symm id Kᶜ)
    {W : Set ℝ} (hW : IsOpen W) (habW : _root_.Set.Icc a b ⊆ W) :
    ∃ D : (F × ℝ) ≃ₘ[ℝ] (F × ℝ),
      (∀ y, (D y).2 = y.2) ∧
      (∀ y, D (y, c) = (y, c)) ∧
      (∀ t ∈ _root_.Set.Icc a b, ∀ x, D ((e (c, x)).1, t) = e (t, x)) ∧
      D '' (_root_.Set.range (fun x => (e (c, x)).1) ×ˢ _root_.Set.Icc a b) = e '' (_root_.Set.Icc a b ×ˢ _root_.Set.univ) ∧
      ∃ K : Set (F × ℝ), IsCompact K ∧ K ⊆ U ×ˢ W ∧ _root_.Set.EqOn D id Kᶜ := by
  obtain ⟨ρ, hρ, hρc, hρone, hρW, _⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact _root_.CompactIccSpace.isCompact_Icc hW habW
  let θ : ℝ → ℝ := fun t => c + ρ t * (t - c)
  have hθ : ContDiff ℝ ∞ θ := contDiff_const.add (hρ.mul (contDiff_id.sub contDiff_const))
  have hθc : θ c = c := by simp [θ]
  have hθeq (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) : θ t = t := by
    have hρt : ρ t = 1 := hρone.self_of_nhdsSet ht
    simp [θ, hρt]
  let D : (F × ℝ) ≃ₘ[ℝ] (F × ℝ) :=
    { toEquiv := Equiv.prodCongrLeft (fun t => ((Φ c).symm.trans (Φ (θ t))).toEquiv)
      contMDiff_toFun := ((hΦ.comp ((hθ.comp contDiff_snd).prodMk
        ((Φ c).symm.contMDiff.contDiff.comp contDiff_fst))).prodMk contDiff_snd).contMDiff
      contMDiff_invFun := (((Φ c).contMDiff.contDiff.comp
        (hΦi.comp ((hθ.comp contDiff_snd).prodMk contDiff_fst))).prodMk contDiff_snd).contMDiff }
  have hDe (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) (x : M) : D ((e (c, x)).1, t) = e (t, x) := by
    apply Prod.ext
    · change Φ (θ t) ((Φ c).symm (e (c, x)).1) = (e (t, x)).1
      rw [hθeq t ht, ← (hΦe c hc x).1, (Φ c).symm_apply_apply]
      exact (hΦe t ht x).1
    · exact (hheight t ht x).symm
  refine ⟨D, fun _ => rfl, ?_, hDe, ?_, K ×ˢ tsupport ρ, hK.prod hρc,
    _root_.Set.prod_mono hKU hρW, ?_⟩
  · intro y
    change (Φ (θ c) ((Φ c).symm y), c) = (y, c)
    rw [hθc, (Φ c).apply_symm_apply]
  · ext z
    constructor
    · rintro ⟨⟨y, t⟩, ⟨⟨x, rfl⟩, ht⟩, rfl⟩
      exact ⟨(t, x), ⟨ht, _root_.Set.mem_univ x⟩, (hDe t ht x).symm⟩
    · rintro ⟨⟨t, x⟩, ⟨ht, _⟩, rfl⟩
      exact ⟨((e (c, x)).1, t), ⟨mem_range_self x, ht⟩, hDe t ht x⟩
  · rintro ⟨y, t⟩ hyt
    apply Prod.ext
    · change Φ (θ t) ((Φ c).symm y) = y
      by_cases hy : y ∈ K
      · have ht : t ∉ tsupport ρ := fun ht => hyt ⟨hy, ht⟩
        have hθt : θ t = c := by simp [θ, image_eq_zero_of_notMem_tsupport ht]
        rw [hθt, (Φ c).apply_symm_apply]
      · rw [(hfix c).2 hy]
        exact (hfix (θ t)).1 hy
    · rfl

run_cmd do
  let target := ``Submission.Manifold.exists_height_preserving_diffeomorph_of_ambient_isotopy
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Manifold.exists_height_preserving_diffeomorph_of_ambient_isotopy target :: scope.openDecls } }

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M]

open _root_.Manifold in
theorem exists_height_preserving_diffeomorph_of_level_family_at
    {e : ℝ × M → F × ℝ} {a b c : ℝ} (hc : c ∈ _root_.Set.Icc a b)
    (he : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F × ℝ) ∞ e (_root_.Set.Icc a b ×ˢ _root_.Set.univ))
    (hemb : ∀ t ∈ _root_.Set.Icc a b, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, F × ℝ) ∞ (fun x => e (t, x)))
    (hheight : ∀ t ∈ _root_.Set.Icc a b, ∀ x, (e (t, x)).2 = t)
    {U : Set F} (hU : IsOpen U)
    (heU : (fun p => (e p).1) '' (_root_.Set.Icc a b ×ˢ _root_.Set.univ) ⊆ U)
    {W : Set ℝ} (hW : IsOpen W) (habW : _root_.Set.Icc a b ⊆ W) :
    ∃ D : (F × ℝ) ≃ₘ[ℝ] (F × ℝ),
      (∀ y, (D y).2 = y.2) ∧
      (∀ y, D (y, c) = (y, c)) ∧
      (∀ t ∈ _root_.Set.Icc a b, ∀ x, D ((e (c, x)).1, t) = e (t, x)) ∧
      D '' (_root_.Set.range (fun x => (e (c, x)).1) ×ˢ _root_.Set.Icc a b) = e '' (_root_.Set.Icc a b ×ˢ _root_.Set.univ) ∧
      ∃ K : Set (F × ℝ), IsCompact K ∧ K ⊆ U ×ˢ W ∧ _root_.Set.EqOn D id Kᶜ := by
  have hp : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ (fun p => (e p).1)
      (_root_.Set.Icc a b ×ˢ _root_.Set.univ) := contDiff_fst.contMDiff.comp_contMDiffOn he
  have hpe (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) :
      IsSmoothEmbedding I 𝓘(ℝ, F) ∞ (fun x => (e (t, x)).1) :=
    (hemb t ht).fst_of_snd_eq_const (by simp) (hheight t ht)
  obtain ⟨Φ, hΦ, hΦi, _, hΦe, K, hK, hKU, hfix⟩ :=
    exists_contDiff_compact_ambient_isotopy_Icc hp hpe hU heU
  exact exists_height_preserving_diffeomorph_of_ambient_isotopy hc hheight Φ hΦ hΦi hΦe
    hK hKU hfix hW habW

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_height_preserving_diffeomorph_of_level_family_at then
    throwError "Refusing to shadow existing declaration Manifold.exists_height_preserving_diffeomorph_of_level_family_at"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_height_preserving_diffeomorph_of_level_family_at ``Submission.Manifold.exists_height_preserving_diffeomorph_of_level_family_at

open _root_.Manifold in
theorem exists_height_preserving_diffeomorph_of_level_family
    {e : ℝ × M → F × ℝ} {a b : ℝ}
    (he : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F × ℝ) ∞ e (_root_.Set.Icc a b ×ˢ _root_.Set.univ))
    (hemb : ∀ t ∈ _root_.Set.Icc a b, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, F × ℝ) ∞ (fun x => e (t, x)))
    (hheight : ∀ t ∈ _root_.Set.Icc a b, ∀ x, (e (t, x)).2 = t)
    {U : Set F} (hU : IsOpen U)
    (heU : (fun p => (e p).1) '' (_root_.Set.Icc a b ×ˢ _root_.Set.univ) ⊆ U)
    {W : Set ℝ} (hW : IsOpen W) (habW : _root_.Set.Icc a b ⊆ W) :
    ∃ D : (F × ℝ) ≃ₘ[ℝ] (F × ℝ),
      (∀ y, (D y).2 = y.2) ∧
      (∀ y, D (y, a) = (y, a)) ∧
      (∀ t ∈ _root_.Set.Icc a b, ∀ x, D ((e (a, x)).1, t) = e (t, x)) ∧
      D '' (_root_.Set.range (fun x => (e (a, x)).1) ×ˢ _root_.Set.Icc a b) = e '' (_root_.Set.Icc a b ×ˢ _root_.Set.univ) ∧
      ∃ K : Set (F × ℝ), IsCompact K ∧ K ⊆ U ×ˢ W ∧ _root_.Set.EqOn D id Kᶜ := by
  by_cases hab : a ≤ b
  · exact exists_height_preserving_diffeomorph_of_level_family_at (c := a)
      ⟨le_rfl, hab⟩ he hemb hheight hU heU hW habW
  · have hempty : _root_.Set.Icc a b = ∅ := _root_.Set.Icc_eq_empty_of_lt (lt_of_not_ge hab)
    refine ⟨Diffeomorph.refl 𝓘(ℝ, F × ℝ) (F × ℝ) ∞, fun _ => rfl,
      fun _ => rfl, ?_, ?_, ∅, isCompact_empty, _root_.Set.empty_subset _, fun _ _ => rfl⟩
    · intro t ht
      simp only [hempty, _root_.Set.mem_empty_iff_false] at ht
    · simp only [hempty, _root_.Set.prod_empty, _root_.Set.empty_prod, _root_.Set.image_empty]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_height_preserving_diffeomorph_of_level_family then
    throwError "Refusing to shadow existing declaration Manifold.exists_height_preserving_diffeomorph_of_level_family"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_height_preserving_diffeomorph_of_level_family ``Submission.Manifold.exists_height_preserving_diffeomorph_of_level_family

open _root_.Manifold in
theorem exists_height_preserving_diffeomorph_of_halfspace_level_family_at
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
    [CompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ℝ × M → F} {a b c : ℝ} (hc : c ∈ _root_.Set.Icc a b)
    (he : ContMDiffOn (𝓘(ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, F) ∞ e (_root_.Set.Icc a b ×ˢ _root_.Set.univ))
    (hemb : ∀ t ∈ _root_.Set.Icc a b, _root_.Manifold.IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, F) ∞ (fun x => e (t, x)))
    {U : Set F} (hU : IsOpen U) (heU : e '' (_root_.Set.Icc a b ×ˢ _root_.Set.univ) ⊆ U)
    {W : Set ℝ} (hW : IsOpen W) (habW : _root_.Set.Icc a b ⊆ W) :
    ∃ D : (F × ℝ) ≃ₘ[ℝ] (F × ℝ),
      (∀ y, (D y).2 = y.2) ∧
      (∀ y, D (y, c) = (y, c)) ∧
      (∀ t ∈ _root_.Set.Icc a b, ∀ x, D (e (c, x), t) = (e (t, x), t)) ∧
      D '' (_root_.Set.range (fun x => e (c, x)) ×ˢ _root_.Set.Icc a b) =
        (fun q : ℝ × M => (e q, q.1)) '' (_root_.Set.Icc a b ×ˢ _root_.Set.univ) ∧
      ∃ K : Set (F × ℝ), IsCompact K ∧ K ⊆ U ×ˢ W ∧ _root_.Set.EqOn D id Kᶜ := by
  obtain ⟨Φ, hΦ, hΦi, _, hΦe, K, hK, hKU, hfix⟩ :=
    exists_contDiff_compact_ambient_isotopy_halfspace_Icc he hemb hU heU
  exact exists_height_preserving_diffeomorph_of_ambient_isotopy
    (e := fun q => (e q, q.1)) hc (fun _ _ _ => rfl) Φ hΦ hΦi hΦe hK hKU hfix hW habW

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_height_preserving_diffeomorph_of_halfspace_level_family_at then
    throwError "Refusing to shadow existing declaration Manifold.exists_height_preserving_diffeomorph_of_halfspace_level_family_at"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_height_preserving_diffeomorph_of_halfspace_level_family_at ``Submission.Manifold.exists_height_preserving_diffeomorph_of_halfspace_level_family_at

end Manifold
