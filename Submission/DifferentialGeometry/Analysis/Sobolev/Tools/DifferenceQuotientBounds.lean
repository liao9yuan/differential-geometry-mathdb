import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient
import Mathlib.Analysis.Calculus.MeanValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Metric _root_.Set
open scoped _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem abs_diffQuot_le_of_norm_fderiv_le
    {c : E → ℝ} {K : Set E} {L : ℝ}
    (hc : ∀ y ∈ K, DifferentiableAt ℝ c y)
    (hL : ∀ y ∈ K, ‖fderiv ℝ c y‖ ≤ L)
    (k : Fin d) (s : ℝ) {x : E}
    (hx : _root_.Metric.cthickening |s| ({x} : Set E) ⊆ K) :
    |diffQuot k s c x| ≤ L := by
  have hball : _root_.Metric.closedBall x |s| ⊆ K :=
    (_root_.Metric.closedBall_subset_cthickening (_root_.Set.mem_singleton x) |s|).trans hx
  have hxball : x ∈ _root_.Metric.closedBall x |s| := _root_.Metric.mem_closedBall_self (abs_nonneg s)
  by_cases hs : s = 0
  · simp only [hs, diffQuot_zero_h, Pi.zero_apply, abs_zero]
    exact (norm_nonneg _).trans (hL x (hball hxball))
  have hshift : x + s • EuclideanSpace.single k (1 : ℝ) ∈ _root_.Metric.closedBall x |s| := by
    rw [_root_.Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp only [PiLp.norm_single, _root_.NormOneClass.norm_one, mul_one, Real.norm_eq_abs, le_refl]
  have hb := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y hy => hc y (hball hy)) (fun y hy => hL y (hball hy))
    (convex_closedBall x |s|) hxball hshift
  rw [add_sub_cancel_left, norm_smul] at hb
  simp only [PiLp.norm_single, _root_.NormOneClass.norm_one, mul_one, Real.norm_eq_abs] at hb
  rw [diffQuot_apply_of_ne k hs, abs_div]
  exact (div_le_iff₀ (abs_pos.mpr hs)).mpr hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.abs_diffQuot_le_of_norm_fderiv_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.abs_diffQuot_le_of_norm_fderiv_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.abs_diffQuot_le_of_norm_fderiv_le ``Submission.DifferentialGeometry.Analysis.Sobolev.abs_diffQuot_le_of_norm_fderiv_le

theorem abs_diffQuot_le_of_differentiableOn
    {c : E → ℝ} {Ω : Set E} {L : ℝ} (hΩ : IsOpen Ω)
    (hc : DifferentiableOn ℝ c Ω) (hL : ∀ y ∈ Ω, ‖fderiv ℝ c y‖ ≤ L)
    (k : Fin d) (s : ℝ) {x : E}
    (hx : _root_.Metric.cthickening |s| ({x} : Set E) ⊆ Ω) :
    |diffQuot k s c x| ≤ L :=
  abs_diffQuot_le_of_norm_fderiv_le
    (fun y hy => (hc y hy).differentiableAt (hΩ.mem_nhds hy)) hL k s hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.abs_diffQuot_le_of_differentiableOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.abs_diffQuot_le_of_differentiableOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.abs_diffQuot_le_of_differentiableOn ``Submission.DifferentialGeometry.Analysis.Sobolev.abs_diffQuot_le_of_differentiableOn

theorem exists_uniform_diffQuot_bound_on_compact
    {c : E → ℝ} {Ω K : Set E} (hΩ : IsOpen Ω)
    (hc : ContDiffOn ℝ 1 c Ω) (hK : IsCompact K) (hKs : K ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℝ, 0 ≤ L ∧ _root_.Metric.cthickening δ K ⊆ Ω ∧
      ∀ (k : Fin d) (s : ℝ), |s| ≤ δ → ∀ x ∈ K, |diffQuot k s c x| ≤ L := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKs
  have hcont : ContinuousOn (fderiv ℝ c) (_root_.Metric.cthickening δ K) :=
    (hc.continuousOn_fderiv_of_isOpen hΩ le_rfl).mono hδΩ
  obtain ⟨L, hL⟩ := hK.cthickening.exists_bound_of_continuousOn hcont
  refine ⟨δ, hδ, _root_.Max.max L 0, le_max_right _ _, hδΩ, ?_⟩
  intro k s hs x hx
  apply abs_diffQuot_le_of_norm_fderiv_le
    (fun y hy => (hc.differentiableOn (by norm_num) y (hδΩ hy)).differentiableAt (hΩ.mem_nhds (hδΩ hy)))
    (fun y hy => (hL y hy).trans (le_max_left L 0)) k s
  exact (_root_.Metric.cthickening_mono hs ({x} : Set E)).trans
    (_root_.Metric.cthickening_subset_of_subset δ (singleton_subset_iff.mpr hx))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.exists_uniform_diffQuot_bound_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.exists_uniform_diffQuot_bound_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.exists_uniform_diffQuot_bound_on_compact ``Submission.DifferentialGeometry.Analysis.Sobolev.exists_uniform_diffQuot_bound_on_compact

theorem exists_uniform_translate_diffQuot_bound_on_compact
    {ι : Type*} [Finite ι] {c : ι → E → ℝ} {Ω K : Set E} (hΩ : IsOpen Ω)
    (hc : ∀ i, ContDiffOn ℝ 1 (c i) Ω) (hK : IsCompact K) (hKs : K ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℝ, 0 ≤ L ∧ _root_.Metric.cthickening δ K ⊆ Ω ∧
      ∀ (i : ι) (k : Fin d) (s : ℝ), |s| ≤ δ → ∀ x ∈ K,
        |translate k s (c i) x| ≤ L ∧ |diffQuot k s (c i) x| ≤ L := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKs
  have hb (i : ι) : ∃ L : ℝ, 0 ≤ L ∧ ∀ y ∈ _root_.Metric.cthickening δ K,
      |c i y| ≤ L ∧ ‖fderiv ℝ (c i) y‖ ≤ L := by
    obtain ⟨A, hA⟩ := hK.cthickening.exists_bound_of_continuousOn ((hc i).continuousOn.mono hδΩ)
    obtain ⟨B, hB⟩ := hK.cthickening.exists_bound_of_continuousOn
      (((hc i).continuousOn_fderiv_of_isOpen hΩ le_rfl).mono hδΩ)
    refine ⟨max (_root_.Max.max A B) 0, le_max_right _ _, ?_⟩
    intro y hy
    exact ⟨(hA y hy).trans ((le_max_left A B).trans (le_max_left _ _)),
      (hB y hy).trans ((le_max_right A B).trans (le_max_left _ _))⟩
  choose L hL hbound using hb
  let C := ∑ i, L i
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => hL i)
  have hiC (i : ι) : L i ≤ C := Finset.single_le_sum (fun j _ => hL j) (Finset.mem_univ i)
  refine ⟨δ, hδ, C, hC, hδΩ, ?_⟩
  intro i k s hs x hx
  have hset : _root_.Metric.cthickening |s| ({x} : Set E) ⊆ _root_.Metric.cthickening δ K :=
    (_root_.Metric.cthickening_mono hs ({x} : Set E)).trans
      (_root_.Metric.cthickening_subset_of_subset δ (singleton_subset_iff.mpr hx))
  have hshift : x + s • EuclideanSpace.single k (1 : ℝ) ∈ _root_.Metric.cthickening δ K := by
    apply hset
    apply _root_.Metric.closedBall_subset_cthickening (_root_.Set.mem_singleton x) |s|
    rw [_root_.Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp only [PiLp.norm_single, _root_.NormOneClass.norm_one, mul_one, Real.norm_eq_abs, le_refl]
  refine ⟨((hbound i _ hshift).1).trans (hiC i), ?_⟩
  exact (abs_diffQuot_le_of_norm_fderiv_le
    (fun y hy => ((hc i).differentiableOn (by norm_num) y (hδΩ hy)).differentiableAt (hΩ.mem_nhds (hδΩ hy)))
    (fun y hy => (hbound i y hy).2) k s hset).trans (hiC i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.exists_uniform_translate_diffQuot_bound_on_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.exists_uniform_translate_diffQuot_bound_on_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.exists_uniform_translate_diffQuot_bound_on_compact ``Submission.DifferentialGeometry.Analysis.Sobolev.exists_uniform_translate_diffQuot_bound_on_compact


theorem exists_uniform_translate_diffQuot_bound_on_compact_family
    {ι Z : Type*} [Finite ι] [TopologicalSpace Z]
    {c : ι → Z → E → ℝ} {J : Set Z} {Ω K : Set E}
    (hJ : IsCompact J) (hΩ : IsOpen Ω) (hK : IsCompact K) (hKs : K ⊆ Ω)
    (hdiff : ∀ i t, t ∈ J → DifferentiableOn ℝ (c i t) Ω)
    (hc : ∀ i, ContinuousOn (fun p : Z × E => c i p.1 p.2) (J ×ˢ Ω))
    (hDc : ∀ i, ContinuousOn (fun p : Z × E => fderiv ℝ (c i p.1) p.2) (J ×ˢ Ω)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℝ, 0 ≤ L ∧ _root_.Metric.cthickening δ K ⊆ Ω ∧
      ∀ (i : ι) (t : Z), t ∈ J → ∀ (k : Fin d) (s : ℝ), |s| ≤ δ → ∀ x ∈ K,
        |translate k s (c i t) x| ≤ L ∧ |diffQuot k s (c i t) x| ≤ L := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKs
  have hb (i : ι) : ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ J, ∀ y ∈ _root_.Metric.cthickening δ K,
      |c i t y| ≤ L ∧ ‖fderiv ℝ (c i t) y‖ ≤ L := by
    obtain ⟨A, hA⟩ := (hJ.prod hK.cthickening).exists_bound_of_continuousOn
      ((hc i).mono (_root_.Set.prod_mono Subset.rfl hδΩ))
    obtain ⟨B, hB⟩ := (hJ.prod hK.cthickening).exists_bound_of_continuousOn
      ((hDc i).mono (_root_.Set.prod_mono Subset.rfl hδΩ))
    refine ⟨max (_root_.Max.max A B) 0, le_max_right _ _, ?_⟩
    intro t ht y hy
    exact ⟨(hA (t, y) ⟨ht, hy⟩).trans ((le_max_left A B).trans (le_max_left _ _)),
      (hB (t, y) ⟨ht, hy⟩).trans ((le_max_right A B).trans (le_max_left _ _))⟩
  choose L hL hbound using hb
  let C := ∑ i, L i
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => hL i)
  have hiC (i : ι) : L i ≤ C := Finset.single_le_sum (fun j _ => hL j) (Finset.mem_univ i)
  refine ⟨δ, hδ, C, hC, hδΩ, ?_⟩
  intro i t ht k s hs x hx
  have hset : _root_.Metric.cthickening |s| ({x} : Set E) ⊆ _root_.Metric.cthickening δ K :=
    (_root_.Metric.cthickening_mono hs ({x} : Set E)).trans
      (_root_.Metric.cthickening_subset_of_subset δ (singleton_subset_iff.mpr hx))
  have hshift : x + s • EuclideanSpace.single k (1 : ℝ) ∈ _root_.Metric.cthickening δ K := by
    apply hset
    apply _root_.Metric.closedBall_subset_cthickening (_root_.Set.mem_singleton x) |s|
    rw [_root_.Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp only [PiLp.norm_single, _root_.NormOneClass.norm_one, mul_one, Real.norm_eq_abs, le_refl]
  refine ⟨((hbound i t ht _ hshift).1).trans (hiC i), ?_⟩
  exact (abs_diffQuot_le_of_norm_fderiv_le
    (fun y hy => (hdiff i t ht y (hδΩ hy)).differentiableAt (hΩ.mem_nhds (hδΩ hy)))
    (fun y hy => (hbound i t ht y hy).2) k s hset).trans (hiC i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.exists_uniform_translate_diffQuot_bound_on_compact_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.exists_uniform_translate_diffQuot_bound_on_compact_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.exists_uniform_translate_diffQuot_bound_on_compact_family ``Submission.DifferentialGeometry.Analysis.Sobolev.exists_uniform_translate_diffQuot_bound_on_compact_family

end DifferentialGeometry.Analysis.Sobolev
