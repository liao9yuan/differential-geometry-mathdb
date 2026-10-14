import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace Homeomorph
open _root_.Homeomorph

open _root_.Homeomorph in
theorem image_sublevel_eq_of_image_level_eq
    {X : Type*} [TopologicalSpace X] (P : ℝ → X ≃ₜ X)
    {a b c : ℝ} {f : X → ℝ} (hf : Continuous f)
    (hP : ∀ x, ContinuousOn (fun t => P t x) (_root_.Set.Icc a b))
    (hPa : P a = Homeomorph.refl X)
    (hlevel : ∀ t ∈ _root_.Set.Icc a b, P t '' {x | f x = c} = {x | f x = c})
    (t : ℝ) (ht : t ∈ _root_.Set.Icc a b) :
    P t '' {x | f x ≤ c} = {x | f x ≤ c} := by
  have hmem (s : ℝ) (hs : s ∈ _root_.Set.Icc a b) (x : X) : f (P s x) = c ↔ f x = c := by
    change P s x ∈ {y | f y = c} ↔ x ∈ {y | f y = c}
    conv_lhs => rw [← hlevel s hs]
    exact (P s).injective.mem_set_image
  have hle (x : X) : f (P t x) ≤ c ↔ f x ≤ c := by
    have hcurve : ContinuousOn (fun s => f (P s x)) (_root_.Set.Icc a t) :=
      (hf.comp_continuousOn (hP x)).mono (_root_.Set.Icc_subset_Icc le_rfl ht.2)
    have hstart : f (P a x) = f x := by rw [hPa]; rfl
    constructor
    · intro htx
      by_contra hx
      have hx' : c < f x := lt_of_not_ge hx
      obtain ⟨s, hs, hsc⟩ := intermediate_value_Icc' ht.1 hcurve
        (show c ∈ _root_.Set.Icc (f (P t x)) (f (P a x)) by rw [hstart]; exact ⟨htx, hx'.le⟩)
      have hxc := (hmem s ⟨hs.1, hs.2.trans ht.2⟩ x).mp hsc
      exact (ne_of_gt hx') hxc
    · intro hx
      by_contra htx
      have ht' : c < f (P t x) := lt_of_not_ge htx
      obtain ⟨s, hs, hsc⟩ := intermediate_value_Icc ht.1 hcurve
        (show c ∈ _root_.Set.Icc (f (P a x)) (f (P t x)) by rw [hstart]; exact ⟨hx, ht'.le⟩)
      have hxc := (hmem s ⟨hs.1, hs.2.trans ht.2⟩ x).mp hsc
      exact (ne_of_gt ht') ((hmem t ht x).mpr hxc)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hle y).mpr hy
  · intro hx
    change f x ≤ c at hx
    exact ⟨(P t).symm x, (hle ((P t).symm x)).mp (by simpa only [(P t).apply_symm_apply] using hx),
      (P t).apply_symm_apply x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.image_sublevel_eq_of_image_level_eq then
    throwError "Refusing to shadow existing declaration Homeomorph.image_sublevel_eq_of_image_level_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.image_sublevel_eq_of_image_level_eq ``Submission.Homeomorph.image_sublevel_eq_of_image_level_eq

open _root_.Homeomorph in
theorem isOpen_image_prod_level_of_height_translation
    {X : Type*} [TopologicalSpace X] (Φ : ℝ → X ≃ₜ X)
    (hΦi : Continuous (fun p : ℝ × X => (Φ p.1).symm p.2))
    {f : X → ℝ} (hf : Continuous f) {N : Set X} (hN : IsOpen N)
    {J : Set ℝ} (hJ : IsOpen J) (a : ℝ)
    (hheight : ∀ t ∈ J, ∀ x ∈ N, f (Φ t x) = f x + t) :
    IsOpen ((fun p : ℝ × X => Φ p.1 p.2) '' (J ×ˢ (N ∩ {x | f x = a}))) := by
  have heq : (fun p : ℝ × X => Φ p.1 p.2) '' (J ×ˢ (N ∩ {x | f x = a})) =
      {y | f y - a ∈ J ∧ (Φ (f y - a)).symm y ∈ N} := by
    ext y
    constructor
    · rintro ⟨⟨t, x⟩, ⟨ht, hx, hxa⟩, rfl⟩
      have hvalue : f (Φ t x) - a = t := by rw [hheight t ht x hx, hxa]; ring
      simp only [_root_.Set.mem_ofPred_eq, hvalue, _root_.Homeomorph.symm_apply_apply]
      exact ⟨ht, hx⟩
    · intro hy
      have hh := hheight (f y - a) hy.1 ((Φ (f y - a)).symm y) hy.2
      rw [(Φ (f y - a)).apply_symm_apply] at hh
      refine ⟨(f y - a, (Φ (f y - a)).symm y), ⟨hy.1, hy.2, ?_⟩,
        (Φ (f y - a)).apply_symm_apply y⟩
      change f ((Φ (f y - a)).symm y) = a
      linarith
  rw [heq]
  exact (hJ.preimage (hf.sub continuous_const)).inter
    (hN.preimage (hΦi.comp ((hf.sub continuous_const).prodMk continuous_id)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.isOpen_image_prod_level_of_height_translation then
    throwError "Refusing to shadow existing declaration Homeomorph.isOpen_image_prod_level_of_height_translation"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.isOpen_image_prod_level_of_height_translation ``Submission.Homeomorph.isOpen_image_prod_level_of_height_translation

end Homeomorph
