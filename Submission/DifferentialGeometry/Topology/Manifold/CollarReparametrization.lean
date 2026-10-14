import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.SupportedExtension
import Submission.DifferentialGeometry.Topology.Diffeomorph.Translation
import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.Coordinates.JacobianSign

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Manifold
open scoped _root_.ContDiff _root_.Manifold

namespace PartialDiffeomorph
open _root_.PartialDiffeomorph

open _root_.Submission.DifferentialGeometry.Topology.Manifold

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [CompactSpace N]

open _root_.PartialDiffeomorph in
theorem exists_collar_reparametrization_isotopy
    (e : PartialDiffeomorph (J.prod 𝓘(ℝ)) I (N × ℝ) M ∞)
    {l u c d : ℝ} (hc : c ∈ _root_.Set.Ioo l u) (hd : d ∈ _root_.Set.Ioo l u)
    (hsource : _root_.Set.univ ×ˢ _root_.Set.Ioo l u ⊆ e.source) :
    ∃ φ : ℝ → ℝ ≃ₘ[ℝ] ℝ,
      ContDiff ℝ ∞ (fun q : ℝ × ℝ => φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × ℝ => (φ q.1).symm q.2) ∧
      φ 0 = Diffeomorph.refl 𝓘(ℝ) ℝ ∞ ∧
      (∀ s ∈ _root_.Set.Icc (0 : ℝ) 1, φ s c = c + s * (d - c)) ∧
      (∀ s a, 0 < deriv (φ s) a) ∧
      (∀ s, _root_.Set.EqOn (φ s) id (_root_.Set.Ioo l u)ᶜ ∧ _root_.Set.EqOn (φ s).symm id (_root_.Set.Ioo l u)ᶜ) ∧
      ∃ F : ℝ → M ≃ₘ⟮I, I⟯ M,
        ContMDiff (𝓘(ℝ).prod I) I ∞ (fun q : ℝ × M => F q.1 q.2) ∧
        ContMDiff (𝓘(ℝ).prod I) I ∞ (fun q : ℝ × M => (F q.1).symm q.2) ∧
        F 0 = Diffeomorph.refl I M ∞ ∧
        (∀ s z, z ∈ e.source → F s (e z) = e (z.1, φ s z.2)) ∧
        (∀ s z, z ∈ e.source → (F s).symm (e z) = e (z.1, (φ s).symm z.2)) ∧
        ∃ K : Set M, IsCompact K ∧ K ⊆ e '' (_root_.Set.univ ×ˢ _root_.Set.Ioo l u) ∧
          ∀ s, _root_.Set.EqOn (F s) id Kᶜ ∧ _root_.Set.EqOn (F s).symm id Kᶜ := by
  classical
  obtain ⟨φ, hφ, hφi, hφ0, hmove, _, L, hL, hLU, hfix⟩ :=
    Diffeomorph.exists_isotopy_translation_in_open (isCompact_singleton (x := c))
      isOpen_Ioo (d - c) (by
        intro s hs a ha
        have hac : a = c := ha
        subst a
        change l < c + s * (d - c) ∧ c + s * (d - c) < u
        have h := (convex_Ioo l u) hc hd (sub_nonneg.mpr hs.2) hs.1 (sub_add_cancel 1 s)
        have heq : (1 - s) • c + s • d = c + s * (d - c) := by
          simp only [smul_eq_mul]
          ring
        rwa [heq] at h)
  have hpositive (s a : ℝ) : 0 < deriv (φ s) a := by
    have h := (φ s).det_fderiv_pos_of_eqOn_compl_isCompact hL (hfix s).1 a
    simpa only [LinearMap.det_ring, ContinuousLinearMap.coe_coe, fderiv_eq_smul_deriv,
      one_smul] using h
  let D (s : ℝ) : (N × ℝ) ≃ₘ⟮J.prod 𝓘(ℝ), J.prod 𝓘(ℝ)⟯ N × ℝ :=
    (Diffeomorph.refl J N ∞).prodCongr (φ s)
  have hD : ContMDiff (𝓘(ℝ).prod (J.prod 𝓘(ℝ))) (J.prod 𝓘(ℝ)) ∞
      (fun q : ℝ × (N × ℝ) => D q.1 q.2) :=
    contMDiff_snd.fst.prodMk
      (hφ.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd.snd))
  have hDi : ContMDiff (𝓘(ℝ).prod (J.prod 𝓘(ℝ))) (J.prod 𝓘(ℝ)) ∞
      (fun q : ℝ × (N × ℝ) => (D q.1).symm q.2) :=
    contMDiff_snd.fst.prodMk
      (hφi.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd.snd))
  have hK : IsCompact (_root_.Set.univ ×ˢ L : Set (N × ℝ)) := isCompact_univ.prod hL
  have hKs : _root_.Set.univ ×ˢ L ⊆ e.source :=
    (Set.prod_mono (subset_refl _) hLU).trans hsource
  obtain ⟨F, hF, hFi, heq, hFK, _, hFfix⟩ :=
    e.exists_diffeomorph_family_extension D hD hDi hK hKs (by
      intro s z hz
      have hzL : z.2 ∉ L := fun h => hz ⟨mem_univ _, h⟩
      exact Prod.ext rfl ((hfix s).1 hzL))
  refine ⟨φ, hφ, hφi, hφ0, ?_, hpositive, ?_, F, hF, hFi, ?_, ?_, ?_,
    e '' (_root_.Set.univ ×ˢ L), hFK, Set.image_mono (Set.prod_mono (subset_refl _) hLU), ?_⟩
  · intro s hs
    simpa only [smul_eq_mul] using hmove s hs c (_root_.Set.mem_singleton c)
  · intro s
    exact ⟨(hfix s).1.mono (compl_subset_compl.mpr hLU),
      (hfix s).2.mono (compl_subset_compl.mpr hLU)⟩
  · apply Diffeomorph.ext
    intro y
    rw [(heq 0 y).1]
    by_cases hy : y ∈ e.target
    · rw [OpenPartialHomeomorph.extendById]
      change (if y ∈ e.target then e (D 0 (e.symm y)) else y) = y
      rw [if_pos hy]
      change e ((e.symm y).1, φ 0 (e.symm y).2) = y
      rw [hφ0]
      exact e.right_inv hy
    · exact if_neg hy
  · intro s z hz
    rw [(heq s (e z)).1, OpenPartialHomeomorph.extendById]
    change (if e z ∈ e.target then e (D s (e.symm (e z))) else e z) =
      e (z.1, φ s z.2)
    rw [if_pos (e.map_source hz)]
    have hleft : e.symm (e z) = z := e.left_inv hz
    rw [hleft]
    rfl
  · intro s z hz
    rw [(heq s (e z)).2, OpenPartialHomeomorph.extendById]
    change (if e z ∈ e.target then e ((D s).symm (e.symm (e z))) else e z) =
      e (z.1, (φ s).symm z.2)
    rw [if_pos (e.map_source hz)]
    have hleft : e.symm (e z) = z := e.left_inv hz
    rw [hleft]
    rfl
  · intro s
    exact ⟨fun y hy => (hFfix s y hy).1, fun y hy => (hFfix s y hy).2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.exists_collar_reparametrization_isotopy then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.exists_collar_reparametrization_isotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.exists_collar_reparametrization_isotopy ``Submission.PartialDiffeomorph.exists_collar_reparametrization_isotopy

end PartialDiffeomorph
