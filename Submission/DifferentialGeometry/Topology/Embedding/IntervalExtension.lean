import Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.ConvexOpen
import Submission.DifferentialGeometry.Topology.Manifold.IntervalExtension
import Submission.DifferentialGeometry.Topology.Embedding.Stability

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace Manifold
open _root_.Manifold

open _root_.Set _root_.Submission.Set

open _root_.Manifold in
private theorem exists_isSmoothEmbedding_eqOn_Icc_of_eventually
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : ℝ × M → V} {a b : ℝ} (hab : a ≤ b)
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ F)
    (hFemb : ∀ t ∈ _root_.Set.Icc a b, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => F (t, x)))
    (hleft : ∀ᶠ t in 𝓝 a, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => F (t, x)))
    (hright : ∀ᶠ t in 𝓝 b, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => F (t, x))) :
    ∃ G : ℝ × M → V, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ G ∧
      (∀ t, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => G (t, x))) ∧
      EqOn G F (_root_.Set.Icc a b ×ˢ _root_.Set.univ) := by
  obtain ⟨c, v, ha, hac⟩ := hleft.exists_Ioo_subset
  obtain ⟨u, d, hb, hbd⟩ := hright.exists_Ioo_subset
  have hnear (t : ℝ) (ht : t ∈ _root_.Set.Ioo c d) :
      IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => F (t, x)) := by
    by_cases hta : t < a
    · exact hac ⟨ht.1, hta.trans ha.2⟩
    · by_cases hbt : b < t
      · exact hbd ⟨hb.1.trans hbt, ht.2⟩
      · exact hFemb t ⟨le_of_not_gt hta, le_of_not_gt hbt⟩
  have hsub : _root_.Set.Icc a b ⊆ _root_.Set.Ioo c d :=
    fun _ ht => ⟨ha.1.trans_le ht.1, ht.2.trans_lt hb.2⟩
  obtain ⟨τ, hτ, hτrange, hτeq⟩ :=
    DifferentialGeometry.Analysis.exists_contDiff_range_subset_eqOn
      _root_.CompactIccSpace.isCompact_Icc isOpen_Ioo (convex_Ioo c d) hsub ⟨a, hsub ⟨le_rfl, hab⟩⟩
  refine ⟨fun q => F (τ q.1, q.2),
    hF.comp ((hτ.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd),
    fun t => hnear (τ t) (hτrange ⟨t, rfl⟩), ?_⟩
  intro q hq
  change F (τ q.1, q.2) = F q
  rw [hτeq hq.1]
  rfl

run_cmd do
  let target := ``Submission.Manifold.exists_isSmoothEmbedding_eqOn_Icc_of_eventually
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Manifold.exists_isSmoothEmbedding_eqOn_Icc_of_eventually target :: scope.openDecls } }

open _root_.Manifold in
theorem exists_isSmoothEmbedding_extension_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {e : ℝ × M → V} {a b : ℝ} (hab : a ≤ b)
    (he : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e (_root_.Set.Icc a b ×ˢ _root_.Set.univ))
    (hf : ∀ t ∈ _root_.Set.Icc a b, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x))) :
    ∃ G : ℝ × M → V, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ G ∧
      (∀ t, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => G (t, x))) ∧
      EqOn G e (_root_.Set.Icc a b ×ˢ _root_.Set.univ) := by
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x⟩⟩
  · refine ⟨fun q => e (a, q.2),
      (hf a ⟨le_rfl, hab⟩).contMDiff.comp contMDiff_snd,
      fun _ => hf a ⟨le_rfl, hab⟩, ?_⟩
    intro q _
    exact hM.elim q.2
  · let h := (hf a ⟨le_rfl, hab⟩).isImmersion
    let hi := h.isImmersionOfComplement_complement x
    let : FiniteDimensional ℝ (E × h.complement) :=
      FiniteDimensional.of_injective hi.equiv.toLinearEquiv.toLinearMap hi.equiv.injective
    let : FiniteDimensional ℝ E :=
      FiniteDimensional.of_injective (LinearMap.inl ℝ E h.complement)
        LinearMap.inl_injective
    have : T2Space M := (hf a ⟨le_rfl, hab⟩).isEmbedding.t2Space
    obtain ⟨F, hF, hFe⟩ := exists_contMDiff_extension_Icc he
    have hFemb (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) :
        IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => F (t, x)) := by
      have hslice : (fun x => F (t, x)) = fun x => e (t, x) :=
        funext fun x => hFe ⟨ht, _root_.Set.mem_univ x⟩
      rw [hslice]
      exact hf t ht
    obtain ⟨G, hG, hGemb, hGF⟩ := exists_isSmoothEmbedding_eqOn_Icc_of_eventually
      hab hF hFemb
      (eventually_isSmoothEmbedding hF (hFemb a ⟨le_rfl, hab⟩) (by simp))
      (eventually_isSmoothEmbedding hF (hFemb b ⟨hab, le_rfl⟩) (by simp))
    exact ⟨G, hG, hGemb, hGF.trans hFe⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_isSmoothEmbedding_extension_Icc then
    throwError "Refusing to shadow existing declaration Manifold.exists_isSmoothEmbedding_extension_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_isSmoothEmbedding_extension_Icc ``Submission.Manifold.exists_isSmoothEmbedding_extension_Icc

open _root_.Manifold in
theorem exists_isSmoothEmbedding_extension_Icc_halfspace
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
    [CompactSpace M] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {e : ℝ × M → V} {a b : ℝ} (hab : a ≤ b)
    (he : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e (_root_.Set.Icc a b ×ˢ _root_.Set.univ))
    (hf : ∀ t ∈ _root_.Set.Icc a b, _root_.Manifold.IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞
      (fun x => e (t, x))) :
    ∃ G : ℝ × M → V, ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ G ∧
      (∀ t, _root_.Manifold.IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => G (t, x))) ∧
      EqOn G e (_root_.Set.Icc a b ×ˢ _root_.Set.univ) := by
  have : T2Space M := (hf a ⟨le_rfl, hab⟩).isEmbedding.t2Space
  obtain ⟨F, hF, hFe⟩ := exists_contMDiff_extension_Icc_halfspace he
  have hFemb (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) :
      IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => F (t, x)) := by
    have hslice : (fun x => F (t, x)) = fun x => e (t, x) :=
      funext fun x => hFe ⟨ht, _root_.Set.mem_univ x⟩
    rw [hslice]
    exact hf t ht
  obtain ⟨G, hG, hGemb, hGF⟩ := exists_isSmoothEmbedding_eqOn_Icc_of_eventually
    hab hF hFemb
    (eventually_isSmoothEmbedding_halfspace hF (hFemb a ⟨le_rfl, hab⟩))
    (eventually_isSmoothEmbedding_halfspace hF (hFemb b ⟨hab, le_rfl⟩))
  exact ⟨G, hG, hGemb, hGF.trans hFe⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_isSmoothEmbedding_extension_Icc_halfspace then
    throwError "Refusing to shadow existing declaration Manifold.exists_isSmoothEmbedding_extension_Icc_halfspace"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_isSmoothEmbedding_extension_Icc_halfspace ``Submission.Manifold.exists_isSmoothEmbedding_extension_Icc_halfspace

end Manifold
