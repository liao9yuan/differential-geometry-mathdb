import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.Smooth
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.Manifold
open scoped _root_.Topology _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]


lemma exists_interval_margin {L : ℝ} (hL : 0 ≤ L) {U : Set ℝ}
    (hU : IsOpen U) (hsub : _root_.Set.Icc 0 L ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ _root_.Set.Icc (-δ) (L + δ) ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ := isCompact_Icc.exists_cthickening_subset_open hU hsub
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  apply hδU
  by_cases ht0 : t < 0
  · apply Metric.mem_cthickening_of_dist_le t 0 δ (_root_.Set.Icc 0 L) ⟨le_rfl, hL⟩
    rw [Real.dist_eq, sub_zero, abs_of_neg ht0]
    linarith [ht.1]
  by_cases htL : L < t
  · apply Metric.mem_cthickening_of_dist_le t L δ (_root_.Set.Icc 0 L) ⟨hL, le_rfl⟩
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr htL)]
    linarith [ht.2]
  · exact Metric.self_subset_cthickening (_root_.Set.Icc 0 L) ⟨le_of_not_gt ht0, le_of_not_gt htL⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_interval_margin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_interval_margin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_interval_margin ``Submission.DifferentialGeometry.Topology.Manifold.exists_interval_margin

lemma exists_rectangle_margin {L s : ℝ} (hL : 0 ≤ L) {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hsub : ({s} ×ˢ _root_.Set.Icc 0 L) ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ (_root_.Set.Icc (s - δ) (s + δ) ×ˢ _root_.Set.Icc (-δ) (L + δ)) ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_singleton.prod _root_.CompactIccSpace.isCompact_Icc).exists_cthickening_subset_open hU hsub
  refine ⟨δ, hδ, ?_⟩
  rintro ⟨a, t⟩ ⟨ha, ht⟩
  apply hδU
  have has : _root_.Dist.dist a s ≤ δ := by
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [ha.1, ha.2]
  by_cases ht0 : t < 0
  · apply Metric.mem_cthickening_of_dist_le (a, t) (s, 0) δ ({s} ×ˢ _root_.Set.Icc 0 L)
      ⟨rfl, le_rfl, hL⟩
    rw [Prod.dist_eq, max_le_iff]
    refine ⟨has, ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_neg ht0]
    linarith [ht.1]
  by_cases htL : L < t
  · apply Metric.mem_cthickening_of_dist_le (a, t) (s, L) δ ({s} ×ˢ _root_.Set.Icc 0 L)
      ⟨rfl, hL, le_rfl⟩
    rw [Prod.dist_eq, max_le_iff]
    refine ⟨has, ?_⟩
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr htL)]
    linarith [ht.2]
  · apply Metric.mem_cthickening_of_dist_le (a, t) (s, t) δ ({s} ×ˢ _root_.Set.Icc 0 L)
      ⟨rfl, le_of_not_gt ht0, le_of_not_gt htL⟩
    simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using has

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_rectangle_margin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_rectangle_margin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_rectangle_margin ``Submission.DifferentialGeometry.Topology.Manifold.exists_rectangle_margin

theorem exists_global_smooth_curve_eq_near_interval {c : ℝ → M} {L : ℝ}
    (hL : 0 ≤ L) {U : Set ℝ} (hU : IsOpen U) (hsub : _root_.Set.Icc 0 L ⊆ U)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ c U) :
    ∃ d : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ d ∧
      ∀ t ∈ _root_.Set.Icc 0 L, d =ᶠ[𝓝 t] c := by
  obtain ⟨δ, hδ, hδU⟩ := exists_interval_margin hL hU hsub
  obtain ⟨ρ, hρ, hρid, _, hρrange⟩ := DifferentialGeometry.exists_smooth_time_clamp
    (-δ / 3) (L + δ / 3) (δ / 3) (by linarith) (by positivity)
  have hρU (t : ℝ) : ρ t ∈ U := by
    apply hδU
    have ht := hρrange t
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨c ∘ ρ, hc.comp_contMDiff hρ.contMDiff hρU, ?_⟩
  intro t ht
  have hnb : _root_.Set.Icc (-δ / 3) (L + δ / 3) ∈ 𝓝 t :=
    Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2])
  filter_upwards [hnb] with s hs
  simp only [Function.comp_apply, hρid s hs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_global_smooth_curve_eq_near_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_global_smooth_curve_eq_near_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_global_smooth_curve_eq_near_interval ``Submission.DifferentialGeometry.Topology.Manifold.exists_global_smooth_curve_eq_near_interval

theorem exists_global_smooth_variation_eq_jointly_near_slice {f : ℝ × ℝ → M} {L s : ℝ}
    (hL : 0 ≤ L) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hsub : ({s} ×ˢ _root_.Set.Icc 0 L) ⊆ U) (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f U) :
    ∃ d : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ d ∧
      ∀ᶠ r in 𝓝 s, ∀ t ∈ _root_.Set.Icc 0 L,
        d =ᶠ[𝓝 (r, t)] f := by
  obtain ⟨δ, hδ, hδU⟩ := exists_rectangle_margin hL hU hsub
  obtain ⟨σ, hσ, hσid, _, hσrange⟩ := DifferentialGeometry.exists_smooth_time_clamp
    (s - δ / 3) (s + δ / 3) (δ / 3) (by linarith) (by positivity)
  obtain ⟨ρ, hρ, hρid, _, hρrange⟩ := DifferentialGeometry.exists_smooth_time_clamp
    (-δ / 3) (L + δ / 3) (δ / 3) (by linarith) (by positivity)
  have hrange (p : ℝ × ℝ) : (σ p.1, ρ p.2) ∈ U := by
    apply hδU
    have hs := hσrange p.1
    have ht := hρrange p.2
    constructor <;> constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  refine ⟨fun p => f (σ p.1, ρ p.2),
    hf.comp_contMDiff ((hσ.comp contDiff_fst).prodMk (hρ.comp contDiff_snd)).contMDiff hrange, ?_⟩
  have hnb : _root_.Set.Ioo (s - δ / 3) (s + δ / 3) ∈ 𝓝 s :=
    Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [hnb] with r hr
  intro t ht
  have hnt : _root_.Set.Icc (-δ / 3) (L + δ / 3) ∈ 𝓝 t :=
    Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2])
  have hnr : _root_.Set.Icc (s - δ / 3) (s + δ / 3) ∈ 𝓝 r := Icc_mem_nhds hr.1 hr.2
  have hnp := prod_mem_nhds hnr hnt
  filter_upwards [hnp] with p hp
  rw [hσid p.1 hp.1, hρid p.2 hp.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_global_smooth_variation_eq_jointly_near_slice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_global_smooth_variation_eq_jointly_near_slice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_global_smooth_variation_eq_jointly_near_slice ``Submission.DifferentialGeometry.Topology.Manifold.exists_global_smooth_variation_eq_jointly_near_slice

theorem exists_global_smooth_variation_eq_near_slice {f : ℝ × ℝ → M} {L s : ℝ}
    (hL : 0 ≤ L) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hsub : ({s} ×ˢ _root_.Set.Icc 0 L) ⊆ U) (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f U) :
    ∃ d : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ d ∧
      ∀ᶠ r in 𝓝 s, ∀ t ∈ _root_.Set.Icc 0 L,
        (fun u => d (r, u)) =ᶠ[𝓝 t] (fun u => f (r, u)) := by
  obtain ⟨d, hd, heq⟩ := exists_global_smooth_variation_eq_jointly_near_slice hL hU hsub hf
  refine ⟨d, hd, ?_⟩
  filter_upwards [heq] with r hr
  intro t ht
  exact (hr t ht).comp_tendsto (continuous_const.prodMk continuous_id).continuousAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_global_smooth_variation_eq_near_slice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_global_smooth_variation_eq_near_slice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_global_smooth_variation_eq_near_slice ``Submission.DifferentialGeometry.Topology.Manifold.exists_global_smooth_variation_eq_near_slice

end DifferentialGeometry.Topology.Manifold
