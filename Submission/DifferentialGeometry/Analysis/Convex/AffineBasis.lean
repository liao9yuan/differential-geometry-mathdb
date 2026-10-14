import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.FinCases

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace AffineBasis
open _root_.AffineBasis

variable {ι 𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

open _root_.AffineBasis in
theorem convexHull_image_eq_nonneg_coord (b : AffineBasis ι 𝕜 E) (s : Set ι) :
    convexHull 𝕜 (b '' s) =
      {x | (∀ i, 0 ≤ b.coord i x) ∧ ∀ i ∉ s, b.coord i x = 0} := by
  classical
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · have hrange : b '' s ⊆ _root_.Set.range b := _root_.Set.image_subset_range _ _
      have h := convexHull_mono hrange hx
      rw [b.convexHull_eq_nonneg_coord] at h
      exact h
    · intro i hi
      have hsub : convexHull 𝕜 (b '' s) ⊆ (b.coord i) ⁻¹' ({0} : Set 𝕜) := by
        apply convexHull_min
        · rintro _ ⟨j, hj, rfl⟩
          exact b.coord_apply_ne (fun h => hi (h.symm ▸ hj))
        · exact (convex_singleton 0).affine_preimage (b.coord i)
      exact hsub hx
  · rintro ⟨hpos, hzero⟩
    have hx : x ∈ affineSpan 𝕜 (_root_.Set.range b) := by
      rw [b.tot]
      exact AffineSubspace.mem_top 𝕜 E x
    obtain ⟨t, w, hw, rfl⟩ := (mem_affineSpan_iff_eq_affineCombination 𝕜 E).mp hx
    have hwpos (i : ι) (hi : i ∈ t) : 0 ≤ w i := by
      simpa only [b.coord_apply_combination_of_mem hi hw] using hpos i
    have hwzero (i : ι) (hi : i ∈ t) (his : i ∉ s) : w i = 0 := by
      simpa only [b.coord_apply_combination_of_mem hi hw] using hzero i his
    let u := t.filter (fun i => i ∈ s)
    have husub : u ⊆ t := Finset.filter_subset _ _
    have houtside (i : ι) (hi : i ∈ t) (hiu : i ∉ u) : w i = 0 :=
      hwzero i hi (fun his => hiu (Finset.mem_filter.mpr ⟨hi, his⟩))
    have huw : ∑ i ∈ u, w i = 1 := (Finset.sum_subset husub houtside).trans hw
    have heq : ∑ i ∈ u, w i • b i = ∑ i ∈ t, w i • b i :=
      Finset.sum_subset husub (fun i hi hiu => by rw [houtside i hi hiu, zero_smul])
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw, ← heq,
      ← u.centerMass_eq_of_sum_1 _ huw]
    exact u.centerMass_mem_convexHull (fun i hi => hwpos i (husub hi))
      (by rw [huw]; exact zero_lt_one)
      (fun i hi => _root_.Set.mem_image_of_mem b (Finset.mem_filter.mp hi).2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AffineBasis.convexHull_image_eq_nonneg_coord then
    throwError "Refusing to shadow existing declaration AffineBasis.convexHull_image_eq_nonneg_coord"
  Lean.modifyEnv fun env => Lean.addAlias env `AffineBasis.convexHull_image_eq_nonneg_coord ``Submission.AffineBasis.convexHull_image_eq_nonneg_coord

open _root_.AffineBasis in
theorem mem_segment_iff_coord (b : AffineBasis ι 𝕜 E) (i j : ι) {x : E} :
    x ∈ segment 𝕜 (b i) (b j) ↔
      (∀ k, 0 ≤ b.coord k x) ∧ ∀ k, k ≠ i → k ≠ j → b.coord k x = 0 := by
  rw [← convexHull_pair, ← _root_.Set.image_pair, b.convexHull_image_eq_nonneg_coord]
  simp only [_root_.Set.mem_ofPred_eq, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, not_or, and_imp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AffineBasis.mem_segment_iff_coord then
    throwError "Refusing to shadow existing declaration AffineBasis.mem_segment_iff_coord"
  Lean.modifyEnv fun env => Lean.addAlias env `AffineBasis.mem_segment_iff_coord ``Submission.AffineBasis.mem_segment_iff_coord

open _root_.AffineBasis in
theorem mem_segment_of_coord_eq_zero (b : AffineBasis (Fin 3) 𝕜 E)
    {x : E} (h : ∀ j, 0 ≤ b.coord j x) (i : Fin 3) (hi : b.coord i x = 0) :
    x ∈ segment 𝕜 (b (i + 1)) (b (i + 2)) := by
  apply (b.mem_segment_iff_coord _ _).mpr
  refine ⟨h, ?_⟩
  intro j hj₁ hj₂
  fin_cases i <;> fin_cases j <;> simp_all

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AffineBasis.mem_segment_of_coord_eq_zero then
    throwError "Refusing to shadow existing declaration AffineBasis.mem_segment_of_coord_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `AffineBasis.mem_segment_of_coord_eq_zero ``Submission.AffineBasis.mem_segment_of_coord_eq_zero

end AffineBasis
