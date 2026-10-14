import Submission.DifferentialGeometry.Topology.Diffeomorph.TimeDependentFlow
import Submission.DifferentialGeometry.Topology.Embedding.ParametricVelocity
import Submission.DifferentialGeometry.Topology.Embedding.IntervalExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace Manifold
open _root_.Manifold

open _root_.Set _root_.Submission.Set

open _root_.Manifold in
private theorem exists_contDiff_compact_ambient_isotopy_of_velocity
    {M : Type*}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ℝ × M → V} (he : ∀ x, ContDiff ℝ ∞ (fun s => e (s, x)))
    (X : ℝ × V → V) (hX : ContDiff ℝ ∞ X) (hXc : HasCompactSupport X)
    {a b : ℝ} {U : Set V} (hXU : tsupport X ⊆ _root_.Set.univ ×ˢ U)
    (hXe : ∀ t ∈ _root_.Set.Icc a b, ∀ x, X (t, e (t, x)) = deriv (fun s => e (s, x)) t) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ _root_.Set.Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x) ∧
        (Φ t).symm (e (t, x)) = e (a, x)) ∧
      ∃ S : Set V, IsCompact S ∧ S ⊆ U ∧ ∀ t : ℝ,
        EqOn (Φ t) id Sᶜ ∧ _root_.Set.EqOn (Φ t).symm id Sᶜ := by
  let Φ : ℝ → (V ≃ₘ[ℝ] V) := fun t => Diffeomorph.timeDependentFlow X hX hXc a t
  refine ⟨Φ, (Diffeomorph.contDiff_timeDependentFlow X hX hXc).comp
    (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)),
    (Diffeomorph.contDiff_timeDependentFlow_symm X hX hXc).comp
      (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)),
    Diffeomorph.timeDependentFlow_refl X hX hXc a, ?_,
    Prod.snd '' tsupport X, hXc.image continuous_snd, ?_,
    fun t => Diffeomorph.timeDependentFlow_eqOn_compl_image_tsupport X hX hXc a t⟩
  · intro t ht x
    have hγ : ContDiff ℝ ∞ (fun s => e (s, x)) := he x
    have hγ' (s : ℝ) (hs : s ∈ _root_.Set.Ico a b) :
        HasDerivWithinAt (fun u => e (u, x)) (X (s, e (s, x))) (_root_.Set.Ici s) s := by
      rw [hXe s ⟨hs.1, hs.2.le⟩ x]
      exact (hγ.differentiable (by simp) s).hasDerivAt.hasDerivWithinAt
    have hmatch : Φ t (e (a, x)) = e (t, x) :=
      Diffeomorph.timeDependentFlow_eqOn_Icc X hX hXc hγ.continuous.continuousOn hγ' ht
    refine ⟨hmatch, ?_⟩
    rw [← hmatch]
    exact (Φ t).symm_apply_apply _
  · rintro _ ⟨q, hq, rfl⟩
    exact (hXU hq).2

run_cmd do
  let target := ``Submission.Manifold.exists_contDiff_compact_ambient_isotopy_of_velocity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Manifold.exists_contDiff_compact_ambient_isotopy_of_velocity target :: scope.openDecls } }

open _root_.Manifold in
theorem exists_contDiff_compact_ambient_isotopy_of_tsupport_image_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ℝ × M → V} (he : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {U : Set V} (hU : IsOpen U) (heU : e '' ((_root_.Set.Icc a b ×ˢ _root_.Set.univ) ∩
      tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ U) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ _root_.Set.Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x) ∧
        (Φ t).symm (e (t, x)) = e (a, x)) ∧
      ∃ S : Set V, IsCompact S ∧ S ⊆ U ∧ ∀ t : ℝ,
        EqOn (Φ t) id Sᶜ ∧ _root_.Set.EqOn (Φ t).symm id Sᶜ := by
  have htrace : (fun q : ℝ × M => (q.1, e q)) ''
      ((_root_.Set.Icc a b ×ˢ _root_.Set.univ) ∩
        tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ _root_.Set.univ ×ˢ U := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨mem_univ _, heU ⟨q, hq, rfl⟩⟩
  obtain ⟨X, hX, hXc, hXU, hXe⟩ :=
    exists_contDiff_compact_velocity_extension_Icc_of_tsupport_image_subset
      he hf (isOpen_univ.prod hU) htrace
  exact exists_contDiff_compact_ambient_isotopy_of_velocity
    (fun x => (he.comp (contMDiff_id.prodMk (contMDiff_const (c := x)))).contDiff)
    X hX hXc hXU hXe

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contDiff_compact_ambient_isotopy_of_tsupport_image_subset then
    throwError "Refusing to shadow existing declaration Manifold.exists_contDiff_compact_ambient_isotopy_of_tsupport_image_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contDiff_compact_ambient_isotopy_of_tsupport_image_subset ``Submission.Manifold.exists_contDiff_compact_ambient_isotopy_of_tsupport_image_subset

open _root_.Manifold in
theorem exists_contDiff_compact_ambient_isotopy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ℝ × M → V} (he : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {U : Set V} (hU : IsOpen U) (heU : e '' (_root_.Set.Icc a b ×ˢ _root_.Set.univ) ⊆ U) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ _root_.Set.Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x) ∧
        (Φ t).symm (e (t, x)) = e (a, x)) ∧
      ∃ S : Set V, IsCompact S ∧ S ⊆ U ∧ ∀ t : ℝ,
        EqOn (Φ t) id Sᶜ ∧ _root_.Set.EqOn (Φ t).symm id Sᶜ :=
  exists_contDiff_compact_ambient_isotopy_of_tsupport_image_subset he hf hU
    ((_root_.Set.image_mono _root_.Set.inter_subset_left).trans heU)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contDiff_compact_ambient_isotopy then
    throwError "Refusing to shadow existing declaration Manifold.exists_contDiff_compact_ambient_isotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contDiff_compact_ambient_isotopy ``Submission.Manifold.exists_contDiff_compact_ambient_isotopy

open _root_.Manifold in
theorem exists_contDiff_compact_ambient_isotopy_eqOn_nhds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ℝ × M → V} (he : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {U : Set V} (hU : IsOpen U)
    (heU : e '' ((_root_.Set.Icc a b ×ˢ _root_.Set.univ) ∩
      tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ U)
    {D : Set V} (hD : IsClosed D)
    (hDA : Disjoint D (e '' ((_root_.Set.Icc a b ×ˢ _root_.Set.univ) ∩
      tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)))) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ _root_.Set.Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x) ∧
        (Φ t).symm (e (t, x)) = e (a, x)) ∧
      ∃ S : Set V, IsCompact S ∧ S ⊆ U ∧
        (∀ t : ℝ, _root_.Set.EqOn (Φ t) id Sᶜ ∧ _root_.Set.EqOn (Φ t).symm id Sᶜ) ∧
        ∃ W : Set V, IsOpen W ∧ D ⊆ W ∧
          ∀ t : ℝ, _root_.Set.EqOn (Φ t) id W ∧ _root_.Set.EqOn (Φ t).symm id W := by
  have hactive : e '' ((_root_.Set.Icc a b ×ˢ _root_.Set.univ) ∩
      tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ U ∩ Dᶜ := by
    intro z hz
    exact ⟨heU hz, fun hzD => Set.disjoint_left.mp hDA hzD hz⟩
  obtain ⟨Φ, hΦ, hΦi, hΦa, hΦe, S, hS, hSU, hΦS⟩ :=
    exists_contDiff_compact_ambient_isotopy_of_tsupport_image_subset he hf
      (hU.inter hD.isOpen_compl) hactive
  refine ⟨Φ, hΦ, hΦi, hΦa, hΦe, S, hS, hSU.trans _root_.Set.inter_subset_left, hΦS,
    Sᶜ, hS.isClosed.isOpen_compl, ?_, hΦS⟩
  intro z hz hzS
  exact (hSU hzS).2 hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contDiff_compact_ambient_isotopy_eqOn_nhds then
    throwError "Refusing to shadow existing declaration Manifold.exists_contDiff_compact_ambient_isotopy_eqOn_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contDiff_compact_ambient_isotopy_eqOn_nhds ``Submission.Manifold.exists_contDiff_compact_ambient_isotopy_eqOn_nhds

open _root_.Manifold in
theorem exists_contDiff_compact_ambient_isotopy_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ℝ × M → V} {a b : ℝ}
    (he : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e (_root_.Set.Icc a b ×ˢ _root_.Set.univ))
    (hf : ∀ t ∈ _root_.Set.Icc a b, _root_.Manifold.IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {U : Set V} (hU : IsOpen U) (heU : e '' (_root_.Set.Icc a b ×ˢ _root_.Set.univ) ⊆ U) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ _root_.Set.Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x) ∧
        (Φ t).symm (e (t, x)) = e (a, x)) ∧
      ∃ S : Set V, IsCompact S ∧ S ⊆ U ∧ ∀ t : ℝ,
        EqOn (Φ t) id Sᶜ ∧ _root_.Set.EqOn (Φ t).symm id Sᶜ := by
  by_cases hab : a ≤ b
  · obtain ⟨G, hG, hGemb, hGe⟩ := exists_isSmoothEmbedding_extension_Icc hab he hf
    have hGU : G '' (_root_.Set.Icc a b ×ˢ _root_.Set.univ) ⊆ U := by
      rintro _ ⟨q, hq, rfl⟩
      rw [hGe hq]
      exact heU ⟨q, hq, rfl⟩
    obtain ⟨Φ, hΦ, hΦi, hΦa, hΦe, hS⟩ :=
      exists_contDiff_compact_ambient_isotopy hG hGemb hU hGU
    refine ⟨Φ, hΦ, hΦi, hΦa, ?_, hS⟩
    intro t ht x
    have hGa : G (a, x) = e (a, x) := hGe ⟨⟨le_rfl, hab⟩, _root_.Set.mem_univ x⟩
    have hGt : G (t, x) = e (t, x) := hGe ⟨ht, _root_.Set.mem_univ x⟩
    simpa only [hGa, hGt] using hΦe t ht x
  · refine ⟨fun _ => Diffeomorph.refl 𝓘(ℝ, V) V ∞,
      contDiff_snd, contDiff_snd, rfl, ?_, ∅, isCompact_empty, _root_.Set.empty_subset U, ?_⟩
    · intro t ht
      exact (hab (ht.1.trans ht.2)).elim
    · exact fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contDiff_compact_ambient_isotopy_Icc then
    throwError "Refusing to shadow existing declaration Manifold.exists_contDiff_compact_ambient_isotopy_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contDiff_compact_ambient_isotopy_Icc ``Submission.Manifold.exists_contDiff_compact_ambient_isotopy_Icc

open _root_.Manifold in
theorem exists_contDiff_compact_ambient_isotopy_halfspace_of_tsupport_image_subset
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
    [CompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ℝ × M → V} (he : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, _root_.Manifold.IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {U : Set V} (hU : IsOpen U) (heU : e '' ((_root_.Set.Icc a b ×ˢ _root_.Set.univ) ∩
      tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ U) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ _root_.Set.Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x) ∧
        (Φ t).symm (e (t, x)) = e (a, x)) ∧
      ∃ S : Set V, IsCompact S ∧ S ⊆ U ∧ ∀ t : ℝ,
        EqOn (Φ t) id Sᶜ ∧ _root_.Set.EqOn (Φ t).symm id Sᶜ := by
  have htrace : (fun q : ℝ × M => (q.1, e q)) ''
      ((_root_.Set.Icc a b ×ˢ _root_.Set.univ) ∩
        tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ _root_.Set.univ ×ˢ U := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨mem_univ _, heU ⟨q, hq, rfl⟩⟩
  obtain ⟨X, hX, hXc, hXU, hXe⟩ :=
    exists_contDiff_compact_velocity_extension_halfspace_Icc_of_tsupport_image_subset
      he hf (isOpen_univ.prod hU) htrace
  exact exists_contDiff_compact_ambient_isotopy_of_velocity
    (fun x => (he.comp (contMDiff_id.prodMk (contMDiff_const (c := x)))).contDiff)
    X hX hXc hXU hXe

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contDiff_compact_ambient_isotopy_halfspace_of_tsupport_image_subset then
    throwError "Refusing to shadow existing declaration Manifold.exists_contDiff_compact_ambient_isotopy_halfspace_of_tsupport_image_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contDiff_compact_ambient_isotopy_halfspace_of_tsupport_image_subset ``Submission.Manifold.exists_contDiff_compact_ambient_isotopy_halfspace_of_tsupport_image_subset

open _root_.Manifold in
theorem exists_contDiff_compact_ambient_isotopy_halfspace
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
    [CompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ℝ × M → V} (he : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, _root_.Manifold.IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {U : Set V} (hU : IsOpen U) (heU : e '' (_root_.Set.Icc a b ×ˢ _root_.Set.univ) ⊆ U) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ _root_.Set.Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x) ∧
        (Φ t).symm (e (t, x)) = e (a, x)) ∧
      ∃ S : Set V, IsCompact S ∧ S ⊆ U ∧ ∀ t : ℝ,
        EqOn (Φ t) id Sᶜ ∧ _root_.Set.EqOn (Φ t).symm id Sᶜ :=
  exists_contDiff_compact_ambient_isotopy_halfspace_of_tsupport_image_subset he hf hU
    ((_root_.Set.image_mono _root_.Set.inter_subset_left).trans heU)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contDiff_compact_ambient_isotopy_halfspace then
    throwError "Refusing to shadow existing declaration Manifold.exists_contDiff_compact_ambient_isotopy_halfspace"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contDiff_compact_ambient_isotopy_halfspace ``Submission.Manifold.exists_contDiff_compact_ambient_isotopy_halfspace

open _root_.Manifold in
theorem exists_contDiff_compact_ambient_isotopy_halfspace_eqOn_nhds
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
    [CompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ℝ × M → V} (he : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, _root_.Manifold.IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {U : Set V} (hU : IsOpen U)
    (heU : e '' ((_root_.Set.Icc a b ×ˢ _root_.Set.univ) ∩
      tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ U)
    {D : Set V} (hD : IsClosed D)
    (hDA : Disjoint D (e '' ((_root_.Set.Icc a b ×ˢ _root_.Set.univ) ∩
      tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)))) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ _root_.Set.Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x) ∧
        (Φ t).symm (e (t, x)) = e (a, x)) ∧
      ∃ S : Set V, IsCompact S ∧ S ⊆ U ∧
        (∀ t : ℝ, _root_.Set.EqOn (Φ t) id Sᶜ ∧ _root_.Set.EqOn (Φ t).symm id Sᶜ) ∧
        ∃ W : Set V, IsOpen W ∧ D ⊆ W ∧
          ∀ t : ℝ, _root_.Set.EqOn (Φ t) id W ∧ _root_.Set.EqOn (Φ t).symm id W := by
  have hactive : e '' ((_root_.Set.Icc a b ×ˢ _root_.Set.univ) ∩
      tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ U ∩ Dᶜ := by
    intro z hz
    exact ⟨heU hz, fun hzD => Set.disjoint_left.mp hDA hzD hz⟩
  obtain ⟨Φ, hΦ, hΦi, hΦa, hΦe, S, hS, hSU, hΦS⟩ :=
    exists_contDiff_compact_ambient_isotopy_halfspace_of_tsupport_image_subset he hf
      (hU.inter hD.isOpen_compl) hactive
  refine ⟨Φ, hΦ, hΦi, hΦa, hΦe, S, hS, hSU.trans _root_.Set.inter_subset_left, hΦS,
    Sᶜ, hS.isClosed.isOpen_compl, ?_, hΦS⟩
  intro z hz hzS
  exact (hSU hzS).2 hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contDiff_compact_ambient_isotopy_halfspace_eqOn_nhds then
    throwError "Refusing to shadow existing declaration Manifold.exists_contDiff_compact_ambient_isotopy_halfspace_eqOn_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contDiff_compact_ambient_isotopy_halfspace_eqOn_nhds ``Submission.Manifold.exists_contDiff_compact_ambient_isotopy_halfspace_eqOn_nhds

open _root_.Manifold in
theorem exists_contDiff_compact_ambient_isotopy_halfspace_Icc
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
    [CompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ℝ × M → V} {a b : ℝ}
    (he : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e (_root_.Set.Icc a b ×ˢ _root_.Set.univ))
    (hf : ∀ t ∈ _root_.Set.Icc a b, _root_.Manifold.IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {U : Set V} (hU : IsOpen U) (heU : e '' (_root_.Set.Icc a b ×ˢ _root_.Set.univ) ⊆ U) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ _root_.Set.Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x) ∧
        (Φ t).symm (e (t, x)) = e (a, x)) ∧
      ∃ S : Set V, IsCompact S ∧ S ⊆ U ∧ ∀ t : ℝ,
        EqOn (Φ t) id Sᶜ ∧ _root_.Set.EqOn (Φ t).symm id Sᶜ := by
  by_cases hab : a ≤ b
  · obtain ⟨G, hG, hGemb, hGe⟩ := exists_isSmoothEmbedding_extension_Icc_halfspace hab he hf
    have hGU : G '' (_root_.Set.Icc a b ×ˢ _root_.Set.univ) ⊆ U := by
      rintro _ ⟨q, hq, rfl⟩
      rw [hGe hq]
      exact heU ⟨q, hq, rfl⟩
    obtain ⟨Φ, hΦ, hΦi, hΦa, hΦe, hS⟩ :=
      exists_contDiff_compact_ambient_isotopy_halfspace hG hGemb hU hGU
    refine ⟨Φ, hΦ, hΦi, hΦa, ?_, hS⟩
    intro t ht x
    have hGa : G (a, x) = e (a, x) := hGe ⟨⟨le_rfl, hab⟩, _root_.Set.mem_univ x⟩
    have hGt : G (t, x) = e (t, x) := hGe ⟨ht, _root_.Set.mem_univ x⟩
    simpa only [hGa, hGt] using hΦe t ht x
  · refine ⟨fun _ => Diffeomorph.refl 𝓘(ℝ, V) V ∞,
      contDiff_snd, contDiff_snd, rfl, ?_, ∅, isCompact_empty, _root_.Set.empty_subset U, ?_⟩
    · intro t ht
      exact (hab (ht.1.trans ht.2)).elim
    · exact fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.exists_contDiff_compact_ambient_isotopy_halfspace_Icc then
    throwError "Refusing to shadow existing declaration Manifold.exists_contDiff_compact_ambient_isotopy_halfspace_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.exists_contDiff_compact_ambient_isotopy_halfspace_Icc ``Submission.Manifold.exists_contDiff_compact_ambient_isotopy_halfspace_Icc

end Manifold
