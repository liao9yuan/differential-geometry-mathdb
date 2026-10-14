import Submission.DifferentialGeometry.Topology.Compactness.ProductChartBand
import Submission.DifferentialGeometry.Topology.Compactness.TimeInterval
import Submission.DifferentialGeometry.Topology.Compactness.FiniteSeparation
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.ContinuousMap

namespace DifferentialGeometry.Topology.Compactness

theorem exists_larger_product_chart_band
    {N M : Type*} [TopologicalSpace N] [CompactSpace N] [TopologicalSpace M]
    (e : OpenPartialHomeomorph (N × ℝ) M) {a b : ℝ} (hab : a ≤ b)
    (hsource : (_root_.Set.univ : Set N) ×ˢ _root_.Set.Icc a b ⊆ e.source)
    {U : Set M} (hU : IsOpen U) (hband : e '' ((_root_.Set.univ : Set N) ×ˢ _root_.Set.Icc a b) ⊆ U) :
    ∃ a' b', a' < a ∧ b < b' ∧
      (_root_.Set.univ : Set N) ×ˢ _root_.Set.Ioo a' b' ⊆ e.source ∧
      e '' ((_root_.Set.univ : Set N) ×ˢ _root_.Set.Ioo a' b') ⊆ U := by
  have hopen : IsOpen (e.source ∩ e ⁻¹' U) := e.isOpen_inter_preimage hU
  have hsmall : (_root_.Set.univ : Set N) ×ˢ _root_.Set.Icc a b ⊆ e.source ∩ e ⁻¹' U :=
    fun p hp ↦ ⟨hsource hp, hband ⟨p, hp, rfl⟩⟩
  obtain ⟨A, V, _, hV, hA, hI, hprod⟩ :=
    generalized_tube_lemma isCompact_univ _root_.CompactIccSpace.isCompact_Icc hopen hsmall
  obtain ⟨a', b', ha, hb, hsub⟩ := exists_larger_interval_subset_of_isOpen hab hV hI
  have hlarge : (_root_.Set.univ : Set N) ×ˢ _root_.Set.Ioo a' b' ⊆ e.source ∩ e ⁻¹' U :=
    fun p hp ↦ hprod ⟨hA hp.1, hsub hp.2⟩
  exact ⟨a', b', ha, hb, fun p hp ↦ (hlarge hp).1,
    by rintro z ⟨p, hp, rfl⟩; exact (hlarge hp).2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Compactness.exists_larger_product_chart_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Compactness.exists_larger_product_chart_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Compactness.exists_larger_product_chart_band ``Submission.DifferentialGeometry.Topology.Compactness.exists_larger_product_chart_band

theorem simplyConnectedSpace_product_chart_band
    {N M : Type*} [TopologicalSpace N] [SimplyConnectedSpace N] [TopologicalSpace M]
    (e : OpenPartialHomeomorph (N × ℝ) M) {a b : ℝ} (hab : a < b)
    (hsource : (_root_.Set.univ : Set N) ×ˢ _root_.Set.Ioo a b ⊆ e.source) :
    SimplyConnectedSpace (e '' ((_root_.Set.univ : Set N) ×ˢ _root_.Set.Ioo a b)) := by
  let _ : ContractibleSpace (_root_.Set.Ioo a b) :=
    (convex_Ioo a b).contractibleSpace (by obtain ⟨t, ht⟩ := exists_between hab; exact ⟨t, ht⟩)
  let E₁ : ↑(e '' ((_root_.Set.univ : Set N) ×ˢ _root_.Set.Ioo a b)) ≃ₜ N × _root_.Set.Ioo a b :=
    (e.homeomorphOfImageSubsetSource hsource rfl).symm.trans
      ((Homeomorph.Set.prod _root_.Set.univ (_root_.Set.Ioo a b)).trans
        ((Homeomorph.Set.univ N).prodCongr (Homeomorph.refl _)))
  let E₂ : N × _root_.Set.Ioo a b ≃ₕ N :=
    ((ContinuousMap.HomotopyEquiv.refl N).prodCongr
      (ContractibleSpace.hequiv_unit (_root_.Set.Ioo a b)).some).trans
        (Homeomorph.prodUnique N Unit).toHomotopyEquiv
  exact (E₁.toHomotopyEquiv.trans E₂).simplyConnectedSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Compactness.simplyConnectedSpace_product_chart_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Compactness.simplyConnectedSpace_product_chart_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Compactness.simplyConnectedSpace_product_chart_band ``Submission.DifferentialGeometry.Topology.Compactness.simplyConnectedSpace_product_chart_band

theorem exists_larger_product_chart_bands_preserving_disjointness
    {N M ι : Type*} [TopologicalSpace N] [CompactSpace N] [TopologicalSpace M]
    [T2Space M] [Finite ι] (e : ι → OpenPartialHomeomorph (N × ℝ) M)
    (a b : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (hsource : ∀ i, (_root_.Set.univ : Set N) ×ˢ _root_.Set.Icc (a i) (b i) ⊆ (e i).source)
    (R : ι → ι → Prop)
    (hd : ∀ i j, R i j → Disjoint
      (e i '' ((_root_.Set.univ : Set N) ×ˢ _root_.Set.Icc (a i) (b i)))
      (e j '' ((_root_.Set.univ : Set N) ×ˢ _root_.Set.Icc (a j) (b j)))) :
    ∃ a' b' : ι → ℝ, (∀ i, a' i < a i ∧ b i < b' i) ∧
      (∀ i, (_root_.Set.univ : Set N) ×ˢ _root_.Set.Ioo (a' i) (b' i) ⊆ (e i).source) ∧
      ∀ i j, R i j → Disjoint
        (e i '' ((_root_.Set.univ : Set N) ×ˢ _root_.Set.Ioo (a' i) (b' i)))
        (e j '' ((_root_.Set.univ : Set N) ×ˢ _root_.Set.Ioo (a' j) (b' j))) := by
  have hK (i : ι) : IsCompact (e i '' ((_root_.Set.univ : Set N) ×ˢ _root_.Set.Icc (a i) (b i))) :=
    (isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc).image_of_continuousOn
      ((e i).continuousOn.mono (hsource i))
  obtain ⟨U, hU, hKU, hUd⟩ := exists_open_supersets_preserving_disjointness _ hK R hd
  have hbig (i : ι) := exists_larger_product_chart_band (e i) (hab i) (hsource i) (hU i) (hKU i)
  choose a' b' ha hb hsrc himg using hbig
  exact ⟨a', b', fun i ↦ ⟨ha i, hb i⟩, hsrc,
    fun i j hij ↦ (hUd i j hij).mono (himg i) (himg j)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Compactness.exists_larger_product_chart_bands_preserving_disjointness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Compactness.exists_larger_product_chart_bands_preserving_disjointness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Compactness.exists_larger_product_chart_bands_preserving_disjointness ``Submission.DifferentialGeometry.Topology.Compactness.exists_larger_product_chart_bands_preserving_disjointness

end DifferentialGeometry.Topology.Compactness
