import Submission.DifferentialGeometry.Analysis.Calculus.LipschitzFamily
import Submission.DifferentialGeometry.Topology.Embedding.Extension
import Submission.DifferentialGeometry.Topology.Embedding.Diffeomorph
import Submission.DifferentialGeometry.Topology.Diffeomorph.Perturbation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.NNReal

namespace Manifold
open _root_.Manifold

open _root_.Set _root_.Submission.Set

open _root_.Manifold in
private theorem eventually_exists_lipschitz_perturbation_of_compact_extension
    {n : ℕ∞} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {M : Type*} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {e : P × M → V} {p₀ : P}
    (hn : 1 ≤ n)
    {G : P × V → V} (hG : ContDiff ℝ n G) (hGc : HasCompactSupport G)
    (hGe : _root_.Set.EqOn (fun q : P × M => G (q.1, e (p₀, q.2))) e
      (Metric.closedBall p₀ 1 ×ˢ _root_.Set.univ)) :
    ∀ᶠ p in 𝓝 p₀, ∃ g : V → V, ContDiff ℝ n g ∧ HasCompactSupport g ∧
      LipschitzWith (1 / 2 : ℝ≥0) g ∧ ∀ x, e (p₀, x) + g (e (p₀, x)) = e (p, x) := by
  have hlip : ∀ᶠ p in 𝓝 p₀,
      LipschitzWith (1 / 2 : ℝ≥0) (fun y => G (p, y) - G (p₀, y)) :=
    ContDiff.eventually_lipschitzWith_sub_slice
      (hG.of_le (WithTop.coe_le_coe.mpr hn)) hGc p₀ (by norm_num)
  have hnear : Metric.closedBall p₀ 1 ∈ 𝓝 p₀ :=
    Metric.closedBall_mem_nhds p₀ zero_lt_one
  filter_upwards [hlip, hnear] with p hp hpnear
  have hslice : ContDiff ℝ n (fun y => G (p, y) - G (p₀, y)) :=
    (hG.comp (contDiff_const.prodMk contDiff_id)).sub
      (hG.comp (contDiff_const.prodMk contDiff_id))
  have hsupp : HasCompactSupport (fun y => G (p, y) - G (p₀, y)) := by
    apply HasCompactSupport.intro (hGc.image continuous_snd)
    intro y hy
    have hzero (q : P) : G (q, y) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hqy => hy ⟨(q, y), hqy, rfl⟩)
    rw [hzero p, hzero p₀, sub_self]
  refine ⟨_, hslice, hsupp, hp, fun x => ?_⟩
  rw [show G (p, e (p₀, x)) = e (p, x) from
    hGe (x := (p, x)) ⟨hpnear, _root_.Set.mem_univ x⟩]
  rw [show G (p₀, e (p₀, x)) = e (p₀, x) from
    hGe (x := (p₀, x)) ⟨Metric.mem_closedBall_self zero_le_one, _root_.Set.mem_univ x⟩]
  abel

run_cmd do
  let target := ``Submission.Manifold.eventually_exists_lipschitz_perturbation_of_compact_extension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Manifold.eventually_exists_lipschitz_perturbation_of_compact_extension target :: scope.openDecls } }

open _root_.Manifold in
private theorem eventually_exists_lipschitz_perturbation
    {n : ℕ∞} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
    [CompactSpace M] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {e : P × M → V} {p₀ : P}
    (he : ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, V) n e)
    (hf₀ : _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) n (fun x => e (p₀, x))) (hn : 1 ≤ n) :
    ∀ᶠ p in 𝓝 p₀, ∃ g : V → V, ContDiff ℝ n g ∧ HasCompactSupport g ∧
      LipschitzWith (1 / 2 : ℝ≥0) g ∧ ∀ x, e (p₀, x) + g (e (p₀, x)) = e (p, x) := by
  let f : P × M → P × V := fun q => (q.1, e (p₀, q.2))
  have hf : _root_.Manifold.IsSmoothEmbedding (𝓘(ℝ, P).prod I) 𝓘(ℝ, P × V) n f := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact (IsSmoothEmbedding.id (I := 𝓘(ℝ, P)) (M := P) (n := n)).prodMap hf₀
  have hK : IsCompact (Metric.closedBall p₀ 1 ×ˢ (_root_.Set.univ : Set M)) :=
    (_root_.ProperSpace.isCompact_closedBall p₀ 1).prod isCompact_univ
  obtain ⟨G, hG, hGc, -, hGe⟩ := hf.exists_contDiff_compact_extension
    he hK isOpen_univ (_root_.Set.subset_univ _)
  exact eventually_exists_lipschitz_perturbation_of_compact_extension hn hG hGc hGe

run_cmd do
  let target := ``Submission.Manifold.eventually_exists_lipschitz_perturbation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Manifold.eventually_exists_lipschitz_perturbation target :: scope.openDecls } }

open _root_.Manifold in
theorem eventually_exists_diffeomorph_comp_eq
    {n : ℕ∞} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
    [CompactSpace M] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {e : P × M → V} {p₀ : P}
    (he : ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, V) n e)
    (hf₀ : _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) n (fun x => e (p₀, x))) (hn : 1 ≤ n) :
    ∀ᶠ p in 𝓝 p₀, ∃ Φ : Diffeomorph 𝓘(ℝ, V) 𝓘(ℝ, V) V V n,
      ∀ x, Φ (e (p₀, x)) = e (p, x) := by
  filter_upwards [eventually_exists_lipschitz_perturbation he hf₀ hn] with p hp
  obtain ⟨g, hg, _, hglip, hge⟩ := hp
  exact ⟨Diffeomorph.addLipschitz hg hglip (by norm_num), hge⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.eventually_exists_diffeomorph_comp_eq then
    throwError "Refusing to shadow existing declaration Manifold.eventually_exists_diffeomorph_comp_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.eventually_exists_diffeomorph_comp_eq ``Submission.Manifold.eventually_exists_diffeomorph_comp_eq

open _root_.Manifold in
theorem eventually_isSmoothEmbedding
    {n : ℕ∞} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
    [CompactSpace M] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {e : P × M → V} {p₀ : P}
    (he : ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, V) n e)
    (hf₀ : _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) n (fun x => e (p₀, x))) (hn : 1 ≤ n) :
    ∀ᶠ p in 𝓝 p₀, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) n (fun x => e (p, x)) := by
  filter_upwards [eventually_exists_diffeomorph_comp_eq he hf₀ hn] with p hp
  obtain ⟨Φ, hΦ⟩ := hp
  exact (funext hΦ) ▸ hf₀.diffeomorph_comp Φ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.eventually_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration Manifold.eventually_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.eventually_isSmoothEmbedding ``Submission.Manifold.eventually_isSmoothEmbedding

section

open scoped _root_.ContDiff _root_.Submission.ContDiff

open _root_.Manifold in
theorem eventually_exists_contDiff_ambient_isotopy
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {e : P × M → V} {p₀ : P}
    (he : ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, V) ∞ e)
    (hf₀ : _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (p₀, x))) :
    ∀ᶠ p in 𝓝 p₀, ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ x, Φ 1 (e (p₀, x)) = e (p, x)) ∧
      ∃ K : Set V, IsCompact K ∧ ∀ t : ℝ,
        EqOn (Φ t) id Kᶜ ∧ _root_.Set.EqOn (Φ t).symm id Kᶜ := by
  filter_upwards [eventually_exists_lipschitz_perturbation he hf₀ (by simp)] with p hp
  obtain ⟨g, hg, hgc, hglip, hge⟩ := hp
  refine ⟨Diffeomorph.addLipschitzIsotopy hg hglip (by norm_num),
    Diffeomorph.contDiff_addLipschitzIsotopy hg hglip (by norm_num),
    Diffeomorph.contDiff_addLipschitzIsotopy_symm hg hglip (by norm_num),
    Diffeomorph.addLipschitzIsotopy_zero hg hglip (by norm_num), ?_,
    Diffeomorph.exists_isCompact_eqOn_addLipschitzIsotopy hg hglip (by norm_num) hgc⟩
  intro x
  simpa only [Diffeomorph.addLipschitzIsotopy_one, Diffeomorph.addLipschitz_apply]
    using hge x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.eventually_exists_contDiff_ambient_isotopy then
    throwError "Refusing to shadow existing declaration Manifold.eventually_exists_contDiff_ambient_isotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.eventually_exists_contDiff_ambient_isotopy ``Submission.Manifold.eventually_exists_contDiff_ambient_isotopy

open _root_.Manifold in
theorem eventually_isSmoothEmbedding_halfspace
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
    [CompactSpace M] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {e : P × M → V} {p₀ : P}
    (he : ContMDiff (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf₀ : _root_.Manifold.IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => e (p₀, x))) :
    ∀ᶠ p in 𝓝 p₀, _root_.Manifold.IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞
      (fun x => e (p, x)) := by
  let f : P × M → P × V := fun q => (q.1, e (p₀, q.2))
  have hf : _root_.Manifold.IsSmoothEmbedding (𝓘(ℝ, P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, P × V) ∞ f := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact (IsSmoothEmbedding.id (I := 𝓘(ℝ, P)) (M := P) (n := ∞)).prodMap hf₀
  have hK : IsCompact (Metric.closedBall p₀ 1 ×ˢ (_root_.Set.univ : Set M)) :=
    (_root_.ProperSpace.isCompact_closedBall p₀ 1).prod isCompact_univ
  obtain ⟨G, hG, hGc, -, hGe⟩ :=
    hf.exists_contDiff_compact_extension_prod_halfspace_of_tsupport_image_subset
      he hK isOpen_univ (_root_.Set.subset_univ _)
  filter_upwards [eventually_exists_lipschitz_perturbation_of_compact_extension
    (n := (⊤ : ℕ∞)) (by simp) hG hGc hGe] with p hp
  obtain ⟨g, hg, _, hglip, hge⟩ := hp
  exact (funext hge) ▸ hf₀.diffeomorph_comp
    (Diffeomorph.addLipschitz hg hglip (by norm_num))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.eventually_isSmoothEmbedding_halfspace then
    throwError "Refusing to shadow existing declaration Manifold.eventually_isSmoothEmbedding_halfspace"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.eventually_isSmoothEmbedding_halfspace ``Submission.Manifold.eventually_isSmoothEmbedding_halfspace

end

end Manifold
