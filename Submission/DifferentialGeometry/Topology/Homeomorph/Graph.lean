import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace Homeomorph
open _root_.Homeomorph

open _root_.Homeomorph in
private noncomputable def intervalShift (a c b d t : ℝ) : ℝ :=
  t + (d - c) * _root_.Max.max 0 (_root_.Min.min ((t - a) / (c - a)) ((b - t) / (b - c)))

run_cmd do
  let target := ``Submission.Homeomorph.intervalShift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.intervalShift target :: scope.openDecls } }

open _root_.Homeomorph in
private theorem intervalShift_eq_self_of_le {a c b d t : ℝ}
    (hac : a < c) (ht : t ≤ a) : intervalShift a c b d t = t := by
  have hn : _root_.Min.min ((t - a) / (c - a)) ((b - t) / (b - c)) ≤ 0 :=
    (min_le_left _ _).trans
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr hac).le)
  simp [intervalShift, max_eq_left hn]

run_cmd do
  let target := ``Submission.Homeomorph.intervalShift_eq_self_of_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.intervalShift_eq_self_of_le target :: scope.openDecls } }

open _root_.Homeomorph in
private theorem intervalShift_eq_self_of_ge {a c b d t : ℝ}
    (hcb : c < b) (ht : b ≤ t) : intervalShift a c b d t = t := by
  have hn : _root_.Min.min ((t - a) / (c - a)) ((b - t) / (b - c)) ≤ 0 :=
    (min_le_right _ _).trans
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr hcb).le)
  simp [intervalShift, max_eq_left hn]

run_cmd do
  let target := ``Submission.Homeomorph.intervalShift_eq_self_of_ge
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.intervalShift_eq_self_of_ge target :: scope.openDecls } }

open _root_.Homeomorph in
private theorem intervalShift_eq_left {a c b d t : ℝ}
    (hac : a < c) (hcb : c < b) (ht : t ∈ _root_.Set.Icc a c) :
    intervalShift a c b d t = a + (t - a) * (d - a) / (c - a) := by
  have hca := sub_pos.mpr hac
  have hbc := sub_pos.mpr hcb
  have hmin : (t - a) / (c - a) ≤ (b - t) / (b - c) := by
    apply (div_le_div_iff₀ hca hbc).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (hac.trans hcb).le)]
  have hn : 0 ≤ (t - a) / (c - a) := div_nonneg (sub_nonneg.mpr ht.1) hca.le
  simp only [intervalShift, min_eq_left hmin, max_eq_right hn]
  field_simp
  ring

run_cmd do
  let target := ``Submission.Homeomorph.intervalShift_eq_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.intervalShift_eq_left target :: scope.openDecls } }

open _root_.Homeomorph in
private theorem intervalShift_eq_right {a c b d t : ℝ}
    (hac : a < c) (hcb : c < b) (ht : t ∈ _root_.Set.Icc c b) :
    intervalShift a c b d t = b - (b - t) * (b - d) / (b - c) := by
  have hca := sub_pos.mpr hac
  have hbc := sub_pos.mpr hcb
  have hmin : (b - t) / (b - c) ≤ (t - a) / (c - a) := by
    apply (div_le_div_iff₀ hbc hca).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr (hac.trans hcb).le)]
  have hn : 0 ≤ (b - t) / (b - c) := div_nonneg (sub_nonneg.mpr ht.2) hbc.le
  simp only [intervalShift, min_eq_right hmin, max_eq_right hn]
  field_simp
  ring

run_cmd do
  let target := ``Submission.Homeomorph.intervalShift_eq_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.intervalShift_eq_right target :: scope.openDecls } }

open _root_.Homeomorph in
private theorem intervalShift_left_mem {a c b d t : ℝ}
    (hac : a < c) (hcb : c < b) (had : a < d) (ht : t ∈ _root_.Set.Icc a c) :
    intervalShift a c b d t ∈ _root_.Set.Icc a d := by
  rw [intervalShift_eq_left hac hcb ht]
  have hca := sub_pos.mpr hac
  constructor
  · exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (sub_nonneg.mpr ht.1)
      (sub_pos.mpr had).le) hca.le)
  · have hh : (t - a) * (d - a) / (c - a) ≤ d - a := by
      apply (div_le_iff₀ hca).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_pos.mpr had).le]
    linarith

run_cmd do
  let target := ``Submission.Homeomorph.intervalShift_left_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.intervalShift_left_mem target :: scope.openDecls } }

open _root_.Homeomorph in
private theorem intervalShift_right_mem {a c b d t : ℝ}
    (hac : a < c) (hcb : c < b) (hdb : d < b) (ht : t ∈ _root_.Set.Icc c b) :
    intervalShift a c b d t ∈ _root_.Set.Icc d b := by
  rw [intervalShift_eq_right hac hcb ht]
  have hbc := sub_pos.mpr hcb
  constructor
  · have hh : (b - t) * (b - d) / (b - c) ≤ b - d := by
      apply (div_le_iff₀ hbc).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr hdb).le]
    linarith
  · exact sub_le_self _ (div_nonneg (mul_nonneg (sub_nonneg.mpr ht.2)
      (sub_pos.mpr hdb).le) hbc.le)

run_cmd do
  let target := ``Submission.Homeomorph.intervalShift_right_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.intervalShift_right_mem target :: scope.openDecls } }

open _root_.Homeomorph in
private theorem intervalShift_left_inv {a c b d : ℝ}
    (hac : a < c) (hcb : c < b) (had : a < d) (hdb : d < b) (t : ℝ) :
    intervalShift a d b c (intervalShift a c b d t) = t := by
  rcases le_total t a with ht | hat
  · rw [intervalShift_eq_self_of_le hac ht, intervalShift_eq_self_of_le had ht]
  rcases le_total b t with ht | htb
  · rw [intervalShift_eq_self_of_ge hcb ht, intervalShift_eq_self_of_ge hdb ht]
  rcases le_total t c with htc | hct
  · rw [intervalShift_eq_left had hdb (intervalShift_left_mem hac hcb had ⟨hat, htc⟩),
      intervalShift_eq_left hac hcb ⟨hat, htc⟩]
    field_simp [sub_ne_zero.mpr hac.ne', sub_ne_zero.mpr had.ne',
      sub_ne_zero.mpr hcb.ne', sub_ne_zero.mpr hdb.ne']
    ring
  · rw [intervalShift_eq_right had hdb (intervalShift_right_mem hac hcb hdb ⟨hct, htb⟩),
      intervalShift_eq_right hac hcb ⟨hct, htb⟩]
    field_simp [sub_ne_zero.mpr hac.ne', sub_ne_zero.mpr had.ne',
      sub_ne_zero.mpr hcb.ne', sub_ne_zero.mpr hdb.ne']
    ring

run_cmd do
  let target := ``Submission.Homeomorph.intervalShift_left_inv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.intervalShift_left_inv target :: scope.openDecls } }

open _root_.Homeomorph in
noncomputable def graphShift {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : Continuous f) {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hab : ∀ x, f x ∈ _root_.Set.Ioo a b) : X × ℝ ≃ₜ X × ℝ where
  toFun p := (p.1, intervalShift a 0 b (f p.1) p.2)
  invFun p := (p.1, intervalShift a (f p.1) b 0 p.2)
  left_inv p := Prod.ext rfl (intervalShift_left_inv ha hb (hab p.1).1 (hab p.1).2 p.2)
  right_inv p := Prod.ext rfl (intervalShift_left_inv (hab p.1).1 (hab p.1).2 ha hb p.2)
  continuous_toFun := by
    apply continuous_fst.prodMk
    exact continuous_snd.add (((hf.comp continuous_fst).sub continuous_const).mul
      (continuous_const.max
        (((continuous_snd.sub continuous_const).div_const _).min
          ((continuous_const.sub continuous_snd).div_const _))))
  continuous_invFun := by
    apply continuous_fst.prodMk
    exact continuous_snd.add ((continuous_const.sub (hf.comp continuous_fst)).mul
      (continuous_const.max
        (((continuous_snd.sub continuous_const).div
          ((hf.comp continuous_fst).sub continuous_const)
          (fun p => (sub_pos.mpr (hab p.1).1).ne')).min
        ((continuous_const.sub continuous_snd).div
          (continuous_const.sub (hf.comp continuous_fst))
          (fun p => (sub_pos.mpr (hab p.1).2).ne')))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.graphShift then
    throwError "Refusing to shadow existing declaration Homeomorph.graphShift"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.graphShift ``Submission.Homeomorph.graphShift

open _root_.Homeomorph in
@[simp] theorem graphShift_apply_zero {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : Continuous f) {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hab : ∀ x, f x ∈ _root_.Set.Ioo a b) (x : X) : graphShift hf ha hb hab (x, 0) = (x, f x) := by
  apply Prod.ext
  · rfl
  change intervalShift a 0 b (f x) 0 = f x
  rw [intervalShift_eq_left ha hb ⟨ha.le, le_rfl⟩]
  field_simp [ha.ne]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.graphShift_apply_zero then
    throwError "Refusing to shadow existing declaration Homeomorph.graphShift_apply_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.graphShift_apply_zero ``Submission.Homeomorph.graphShift_apply_zero

open _root_.Homeomorph in
theorem graphShift_eq_self_of_eq_zero {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : Continuous f) {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hab : ∀ x, f x ∈ _root_.Set.Ioo a b) {p : X × ℝ} (hp : f p.1 = 0) :
    graphShift hf ha hb hab p = p := by
  apply Prod.ext
  · rfl
  change intervalShift a 0 b (f p.1) p.2 = p.2
  simp [intervalShift, hp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.graphShift_eq_self_of_eq_zero then
    throwError "Refusing to shadow existing declaration Homeomorph.graphShift_eq_self_of_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.graphShift_eq_self_of_eq_zero ``Submission.Homeomorph.graphShift_eq_self_of_eq_zero

open _root_.Homeomorph in
theorem graphShift_eq_self_of_notMem_Ioo {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : Continuous f) {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hab : ∀ x, f x ∈ _root_.Set.Ioo a b) {p : X × ℝ} (hp : p.2 ∉ _root_.Set.Ioo a b) :
    graphShift hf ha hb hab p = p := by
  apply Prod.ext
  · rfl
  change intervalShift a 0 b (f p.1) p.2 = p.2
  rcases not_and_or.mp hp with hp | hp
  · exact intervalShift_eq_self_of_le ha (le_of_not_gt hp)
  · exact intervalShift_eq_self_of_ge hb (le_of_not_gt hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.graphShift_eq_self_of_notMem_Ioo then
    throwError "Refusing to shadow existing declaration Homeomorph.graphShift_eq_self_of_notMem_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.graphShift_eq_self_of_notMem_Ioo ``Submission.Homeomorph.graphShift_eq_self_of_notMem_Ioo

open _root_.Homeomorph in
theorem graphShift_eqOn_compl {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : Continuous f) {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hab : ∀ x, f x ∈ _root_.Set.Ioo a b) :
    EqOn (graphShift hf ha hb hab) id (tsupport f ×ˢ _root_.Set.Icc a b)ᶜ := by
  intro p hp
  by_cases hx : p.1 ∈ tsupport f
  · apply graphShift_eq_self_of_notMem_Ioo
    intro ht
    exact hp ⟨hx, ht.1.le, ht.2.le⟩
  · exact graphShift_eq_self_of_eq_zero hf ha hb hab (image_eq_zero_of_notMem_tsupport hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.graphShift_eqOn_compl then
    throwError "Refusing to shadow existing declaration Homeomorph.graphShift_eqOn_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.graphShift_eqOn_compl ``Submission.Homeomorph.graphShift_eqOn_compl

open _root_.Homeomorph in
theorem graphShift_image_graphOn {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : Continuous f) {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hab : ∀ x, f x ∈ _root_.Set.Ioo a b) (s : Set X) :
    graphShift hf ha hb hab '' (s ×ˢ {(0 : ℝ)}) = s.graphOn f := by
  ext p
  constructor
  · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    have ht0 : t = 0 := ht
    subst t
    rw [graphShift_apply_zero]
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x, 0), ⟨hx, rfl⟩, graphShift_apply_zero hf ha hb hab x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.graphShift_image_graphOn then
    throwError "Refusing to shadow existing declaration Homeomorph.graphShift_image_graphOn"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.graphShift_image_graphOn ``Submission.Homeomorph.graphShift_image_graphOn

end Homeomorph
