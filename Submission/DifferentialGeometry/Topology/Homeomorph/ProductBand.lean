import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set

namespace Homeomorph
open _root_.Homeomorph

variable {X : Type*} [TopologicalSpace X]

open _root_.Homeomorph in
private theorem snd_pos_of_zero_fixed (F : X × ℝ ≃ₜ X × ℝ)
    (hzero : ∀ x, F (x, 0) = (x, 0)) (u : ℝ)
    (hfix : ∀ q : X × ℝ, u ≤ q.2 → F q = q)
    (q : X × ℝ) (hq : 0 < q.2) : 0 < (F q).2 := by
  by_contra hn
  let b := _root_.Max.max q.2 u + 1
  have hqb : q.2 ≤ b := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hub : u ≤ b := (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hb : 0 < b := hq.trans_le hqb
  have hc : Continuous (fun t : ℝ => (F (q.1, t)).2) :=
    continuous_snd.comp (F.continuous.comp (continuous_const.prodMk continuous_id))
  have hfb : (F (q.1, b)).2 = b := congrArg Prod.snd (hfix _ hub)
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc hqb hc.continuousOn
    (show (0 : ℝ) ∈ _root_.Set.Icc (F (q.1, q.2)).2 (F (q.1, b)).2 from
      ⟨le_of_not_gt hn, hfb.symm ▸ hb.le⟩)
  have hz : F (q.1,t) = F ((F (q.1,t)).1,0) := by
    rw [hzero]
    exact Prod.ext rfl heq
  have ht0 : t = 0 := congrArg Prod.snd (F.injective hz)
  linarith [ht.1]

run_cmd do
  let target := ``Submission.Homeomorph.snd_pos_of_zero_fixed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.snd_pos_of_zero_fixed target :: scope.openDecls } }

open _root_.Homeomorph in
theorem snd_pos_iff_of_zero_fixed (F : X × ℝ ≃ₜ X × ℝ)
    (hzero : ∀ x, F (x, 0) = (x, 0)) (u : ℝ)
    (hfix : ∀ q : X × ℝ, u ≤ q.2 → F q = q) (q : X × ℝ) :
    0 < (F q).2 ↔ 0 < q.2 := by
  have hizero : ∀ x, F.symm (x,0) = (x,0) := fun x =>
    F.injective ((F.apply_symm_apply _).trans (hzero x).symm)
  have hifix : ∀ q : X × ℝ, u ≤ q.2 → F.symm q = q := fun q hq =>
    F.injective ((F.apply_symm_apply _).trans (hfix q hq).symm)
  constructor
  · intro h
    simpa only [F.symm_apply_apply] using snd_pos_of_zero_fixed F.symm hizero u hifix (F q) h
  · exact snd_pos_of_zero_fixed F hzero u hfix q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.snd_pos_iff_of_zero_fixed then
    throwError "Refusing to shadow existing declaration Homeomorph.snd_pos_iff_of_zero_fixed"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.snd_pos_iff_of_zero_fixed ``Submission.Homeomorph.snd_pos_iff_of_zero_fixed

open _root_.Homeomorph in
theorem snd_eq_zero_iff_of_zero_fixed (F : X × ℝ ≃ₜ X × ℝ)
    (hzero : ∀ x, F (x, 0) = (x, 0)) (q : X × ℝ) : (F q).2 = 0 ↔ q.2 = 0 := by
  constructor
  · intro h
    have heq : F q = F ((F q).1,0) := by
      rw [hzero]
      exact Prod.ext rfl h
    exact congrArg Prod.snd (F.injective heq)
  · intro h
    have hq : q = (q.1,0) := Prod.ext rfl h
    rw [hq,hzero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.snd_eq_zero_iff_of_zero_fixed then
    throwError "Refusing to shadow existing declaration Homeomorph.snd_eq_zero_iff_of_zero_fixed"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.snd_eq_zero_iff_of_zero_fixed ``Submission.Homeomorph.snd_eq_zero_iff_of_zero_fixed

open _root_.Homeomorph in
theorem mapsTo_closed_band_of_zero_fixed (F : X × ℝ ≃ₜ X × ℝ)
    (hzero : ∀ x, F (x, 0) = (x, 0)) {u b : ℝ} (hub : u ≤ b)
    (hfix : ∀ q : X × ℝ, u ≤ q.2 → F q = q) :
    MapsTo F (_root_.Set.univ ×ˢ _root_.Set.Icc 0 b) (_root_.Set.univ ×ˢ _root_.Set.Icc 0 b) := by
  rintro q ⟨_,h0,hb⟩
  refine ⟨mem_univ _,?_,?_⟩
  · rcases h0.eq_or_lt with h | h
    · exact le_of_eq ((F.snd_eq_zero_iff_of_zero_fixed hzero q).mpr h.symm).symm
    · exact ((F.snd_pos_iff_of_zero_fixed hzero u hfix q).mpr h).le
  · by_contra hn
    have hfb : b < (F q).2 := lt_of_not_ge hn
    have heq : F q = q := F.injective (hfix (F q) (hub.trans hfb.le))
    rw [heq] at hfb
    exact not_lt_of_ge hb hfb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.mapsTo_closed_band_of_zero_fixed then
    throwError "Refusing to shadow existing declaration Homeomorph.mapsTo_closed_band_of_zero_fixed"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.mapsTo_closed_band_of_zero_fixed ``Submission.Homeomorph.mapsTo_closed_band_of_zero_fixed

open _root_.Homeomorph in
theorem image_closed_band_of_zero_fixed (F : X × ℝ ≃ₜ X × ℝ)
    (hzero : ∀ x, F (x, 0) = (x, 0)) {u b : ℝ} (hub : u ≤ b)
    (hfix : ∀ q : X × ℝ, u ≤ q.2 → F q = q) :
    F '' (_root_.Set.univ ×ˢ _root_.Set.Icc 0 b) = _root_.Set.univ ×ˢ _root_.Set.Icc 0 b := by
  apply Subset.antisymm (F.mapsTo_closed_band_of_zero_fixed hzero hub hfix).image_subset
  intro q hq
  have hizero : ∀ x, F.symm (x,0) = (x,0) := fun x =>
    F.injective ((F.apply_symm_apply _).trans (hzero x).symm)
  have hifix : ∀ q : X × ℝ, u ≤ q.2 → F.symm q = q := fun q hq =>
    F.injective ((F.apply_symm_apply _).trans (hfix q hq).symm)
  exact ⟨F.symm q,F.symm.mapsTo_closed_band_of_zero_fixed hizero hub hifix hq,F.apply_symm_apply q⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.image_closed_band_of_zero_fixed then
    throwError "Refusing to shadow existing declaration Homeomorph.image_closed_band_of_zero_fixed"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.image_closed_band_of_zero_fixed ``Submission.Homeomorph.image_closed_band_of_zero_fixed

end Homeomorph
