import Submission.DifferentialGeometry.Analysis.Calculus.Compactness.ArzelaAscoli
import Submission.DifferentialGeometry.Analysis.Calculus.Compactness.ClampedSubsequence
import Mathlib.Topology.MetricSpace.Lipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section
open _root_.Filter _root_.Set
open scoped _root_.Topology _root_.NNReal

namespace DifferentialGeometry.Analysis

variable {W : Type*} [PseudoMetricSpace W] [T2Space W]

theorem exists_subseq_tendsto_uniformlyOn_Ico_of_eventually_lipschitzOnWith
    {ell : ℝ} (hell : 0 < ell) (f : ℕ → ℝ → W)
    (hcompact : ∀ s ∈ _root_.Set.Ico (0 : ℝ) ell, ∃ K : Set W, IsCompact K ∧
      ∀ᶠ n in _root_.Filter.atTop, f n s ∈ K)
    (hLip : ∀ r ∈ _root_.Set.Ioo (0 : ℝ) ell, ∃ L : ℝ≥0,
      ∀ᶠ n in _root_.Filter.atTop, LipschitzOnWith L (f n) (_root_.Set.Icc (0 : ℝ) r)) :
    ∃ (phi : ℕ → ℕ) (g : C(_root_.Set.Ico (0 : ℝ) ell, W)), StrictMono phi ∧
      ∀ r : ℝ, r < ell → TendstoUniformlyOn
        (fun n (s : _root_.Set.Ico (0 : ℝ) ell) => f (phi n) s) g _root_.Filter.atTop {s | (s : ℝ) ≤ r} := by
  classical
  have hcontinuous : ∀ r : ℝ, 0 ≤ r → r < ell →
      ∀ᶠ n in _root_.Filter.atTop, ContinuousOn (f n) (_root_.Set.Icc (0 : ℝ) r) := by
    intro r hr hrlt
    obtain ⟨R, hrR, hR⟩ := exists_between hrlt
    obtain ⟨L, hL⟩ := hLip R ⟨hr.trans_lt hrR, hR⟩
    exact hL.mono fun n hn => hn.continuousOn.mono (_root_.Set.Icc_subset_Icc_right hrR.le)
  obtain ⟨sigma, T, beta, hsigma, _, _, _, _, heq⟩ :=
    ContinuousMap.exists_subsequence_clamped_Ico_of_eventually_continuousOn hell f hcontinuous
  have hbLip : ∀ r ∈ _root_.Set.Ioo (0 : ℝ) ell, ∃ L : ℝ≥0,
      ∀ᶠ n in _root_.Filter.atTop, LipschitzOnWith L (beta n) {s : _root_.Set.Ico 0 ell | (s : ℝ) ≤ r} := by
    intro r hr
    obtain ⟨L, hL⟩ := hLip r hr
    refine ⟨L, ?_⟩
    filter_upwards [hsigma.tendsto_atTop.eventually hL, heq r hr.2] with n hn he
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    rw [he s hs, he t ht]
    exact hn.dist_le_mul s ⟨s.property.1, hs⟩ t ⟨t.property.1, ht⟩
  have hbcompact (s : _root_.Set.Ico 0 ell) : ∃ K : Set W, IsCompact K ∧ ∀ n, beta n s ∈ K := by
    obtain ⟨r, hsr, hr⟩ := exists_between s.property.2
    obtain ⟨K, hK, hmem⟩ := hcompact s s.property
    have hev : ∀ᶠ n in _root_.Filter.atTop, beta n s ∈ K := by
      filter_upwards [hsigma.tendsto_atTop.eventually hmem, heq r hr] with n hn he
      rw [he s hsr.le]
      exact hn
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    refine ⟨K ∪ _root_.Set.range (fun i : Fin N => beta i s),
      hK.union (_root_.Set.finite_range _).isCompact, ?_⟩
    intro n
    rcases lt_or_ge n N with hn | hn
    · exact Or.inr ⟨⟨n, hn⟩, rfl⟩
    · exact Or.inl (hN n hn)
  let _ : LocallyCompactSpace (_root_.Set.Ico (0 : ℝ) ell) := isLocallyClosed_Ico.locallyCompactSpace
  obtain ⟨tau, g, htau, hconv⟩ :=
    arzela_ascoli_subseq_tendsto_locally_uniformly_of_pointwise_compact beta
      (DifferentialGeometry.equicontinuous_Ico_of_eventually_lipschitzOnWith
        (fun n => (beta n).continuous) hbLip) hbcompact
  refine ⟨sigma ∘ tau, g, hsigma.comp htau, ?_⟩
  intro r hr
  have hK : IsCompact {s : _root_.Set.Ico (0 : ℝ) ell | (s : ℝ) ≤ r} := by
    rw [Subtype.isCompact_iff]
    have hset : Subtype.val '' {s : _root_.Set.Ico (0 : ℝ) ell | (s : ℝ) ≤ r} = _root_.Set.Icc 0 r := by
      ext s
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨s.property.1, hs⟩
      · intro hs
        exact ⟨⟨s, hs.1, hs.2.trans_lt hr⟩, hs.2, rfl⟩
    rw [hset]
    exact _root_.CompactIccSpace.isCompact_Icc
  have hlim := hconv _ hK
  apply hlim.congr
  filter_upwards [htau.tendsto_atTop.eventually (heq r hr)] with n hn
  intro s hs
  exact hn s hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_subseq_tendsto_uniformlyOn_Ico_of_eventually_lipschitzOnWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_subseq_tendsto_uniformlyOn_Ico_of_eventually_lipschitzOnWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_subseq_tendsto_uniformlyOn_Ico_of_eventually_lipschitzOnWith ``Submission.DifferentialGeometry.Analysis.exists_subseq_tendsto_uniformlyOn_Ico_of_eventually_lipschitzOnWith

end DifferentialGeometry.Analysis

end
