import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Mathlib.Analysis.InnerProductSpace.Calculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric
open scoped _root_.ContDiff _root_.Manifold

namespace PartialDiffeomorph
open _root_.PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open _root_.PartialDiffeomorph in
private noncomputable def halfBallInversionMap (r : ℝ) (p : E × ℝ) : E × ℝ :=
  ((2 * r ^ 2 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2)) • p.1,
    (2 * r ^ 2 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2)) * (p.2 + r) - r)

run_cmd do
  let target := ``Submission.PartialDiffeomorph.halfBallInversionMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `PartialDiffeomorph.halfBallInversionMap target :: scope.openDecls } }

omit [InnerProductSpace ℝ E] in
open _root_.PartialDiffeomorph in
private theorem halfBallInversion_denominator {r : ℝ} {p : E × ℝ}
    (hp : p ≠ (0, -r)) : 0 < ‖p.1‖ ^ 2 + (p.2 + r) ^ 2 := by
  have hnonneg := sq_nonneg ‖p.1‖
  have hnonneg' := sq_nonneg (p.2 + r)
  by_contra hh
  have hsum : ‖p.1‖ ^ 2 + (p.2 + r) ^ 2 = 0 := by linarith
  have hx : ‖p.1‖ = 0 := by nlinarith
  have ht : p.2 = -r := by nlinarith
  exact hp (Prod.ext (norm_eq_zero.mp hx) ht)

run_cmd do
  let target := ``Submission.PartialDiffeomorph.halfBallInversion_denominator
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `PartialDiffeomorph.halfBallInversion_denominator target :: scope.openDecls } }

open _root_.PartialDiffeomorph in
private theorem halfBallInversion_denominator_apply (r : ℝ) {p : E × ℝ}
    (hp : p ≠ (0, -r)) :
    ‖(halfBallInversionMap r p).1‖ ^ 2 + ((halfBallInversionMap r p).2 + r) ^ 2 =
      4 * r ^ 4 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2) := by
  have hd := (halfBallInversion_denominator hp).ne'
  simp only [halfBallInversionMap, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  ring

run_cmd do
  let target := ``Submission.PartialDiffeomorph.halfBallInversion_denominator_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `PartialDiffeomorph.halfBallInversion_denominator_apply target :: scope.openDecls } }

open _root_.PartialDiffeomorph in
private theorem halfBallInversionMap_mem {r : ℝ} (hr : r ≠ 0) {p : E × ℝ}
    (hp : p ≠ (0, -r)) : halfBallInversionMap r p ≠ (0, -r) := by
  have heq := halfBallInversion_denominator_apply r hp
  intro hh
  rw [hh] at heq
  have hpos : 0 < 4 * r ^ 4 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2) :=
    div_pos (mul_pos (by norm_num) (by
      simpa only [← pow_mul] using (pow_pos (sq_pos_of_ne_zero hr) 2)))
      (halfBallInversion_denominator hp)
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), neg_add_cancel, add_zero] at heq
  linarith

run_cmd do
  let target := ``Submission.PartialDiffeomorph.halfBallInversionMap_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `PartialDiffeomorph.halfBallInversionMap_mem target :: scope.openDecls } }

open _root_.PartialDiffeomorph in
private theorem halfBallInversionMap_involutive {r : ℝ} (hr : r ≠ 0) {p : E × ℝ}
    (hp : p ≠ (0, -r)) : halfBallInversionMap r (halfBallInversionMap r p) = p := by
  have hd := (halfBallInversion_denominator hp).ne'
  have heq := halfBallInversion_denominator_apply r hp
  apply Prod.ext
  · change (2 * r ^ 2 / _) • ((2 * r ^ 2 / _) • p.1) = p.1
    rw [heq, smul_smul]
    have hc : (2 * r ^ 2 / (4 * r ^ 4 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2))) *
        (2 * r ^ 2 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2)) = 1 := by
      field_simp
      ring
    rw [hc, one_smul]
  · change (2 * r ^ 2 / _) * ((2 * r ^ 2 / _) * (p.2 + r) - r + r) - r = p.2
    rw [heq]
    field_simp
    ring

run_cmd do
  let target := ``Submission.PartialDiffeomorph.halfBallInversionMap_involutive
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `PartialDiffeomorph.halfBallInversionMap_involutive target :: scope.openDecls } }

open _root_.PartialDiffeomorph in
private theorem contDiffOn_halfBallInversionMap (r : ℝ) :
    ContDiffOn ℝ ∞ (halfBallInversionMap (E := E) r) {(0, -r)}ᶜ := by
  have hd : ContDiff ℝ ∞ (fun p : E × ℝ => ‖p.1‖ ^ 2 + (p.2 + r) ^ 2) :=
    ((contDiff_norm_sq ℝ).comp contDiff_fst).add ((contDiff_snd.add contDiff_const).pow 2)
  have hq : ContDiffOn ℝ ∞ (fun p : E × ℝ => 2 * r ^ 2 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2))
      {(0, -r)}ᶜ := contDiffOn_const.div hd.contDiffOn
        (fun _ hp => (halfBallInversion_denominator hp).ne')
  exact (hq.smul contDiffOn_fst).prodMk
    ((hq.mul (contDiffOn_snd.add contDiffOn_const)).sub contDiffOn_const)

run_cmd do
  let target := ``Submission.PartialDiffeomorph.contDiffOn_halfBallInversionMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `PartialDiffeomorph.contDiffOn_halfBallInversionMap target :: scope.openDecls } }

open _root_.PartialDiffeomorph in
noncomputable def halfBallInversion (r : ℝ) (hr : r ≠ 0) :
    PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞ where
  toFun := halfBallInversionMap r
  invFun := halfBallInversionMap r
  source := {(0, -r)}ᶜ
  target := {(0, -r)}ᶜ
  map_source' _ hp := halfBallInversionMap_mem hr hp
  map_target' _ hp := halfBallInversionMap_mem hr hp
  left_inv' _ hp := halfBallInversionMap_involutive hr hp
  right_inv' _ hp := halfBallInversionMap_involutive hr hp
  open_source := isOpen_compl_singleton
  open_target := isOpen_compl_singleton
  contMDiffOn_toFun := (contDiffOn_halfBallInversionMap r).contMDiffOn
  contMDiffOn_invFun := (contDiffOn_halfBallInversionMap r).contMDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.halfBallInversion then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.halfBallInversion"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.halfBallInversion ``Submission.PartialDiffeomorph.halfBallInversion

open _root_.PartialDiffeomorph in
theorem halfBallInversion_apply (r : ℝ) (hr : r ≠ 0) (p : E × ℝ) :
    halfBallInversion r hr p =
      ((2 * r ^ 2 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2)) • p.1,
        (2 * r ^ 2 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2)) * (p.2 + r) - r) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.halfBallInversion_apply then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.halfBallInversion_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.halfBallInversion_apply ``Submission.PartialDiffeomorph.halfBallInversion_apply

open _root_.PartialDiffeomorph in
@[simp] theorem halfBallInversion_symm (r : ℝ) (hr : r ≠ 0) :
    (halfBallInversion (E := E) r hr).symm = halfBallInversion r hr := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.halfBallInversion_symm then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.halfBallInversion_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.halfBallInversion_symm ``Submission.PartialDiffeomorph.halfBallInversion_symm

open _root_.PartialDiffeomorph in
@[simp] theorem halfBallInversion_source (r : ℝ) (hr : r ≠ 0) :
    (halfBallInversion (E := E) r hr).source = {(0, -r)}ᶜ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.halfBallInversion_source then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.halfBallInversion_source"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.halfBallInversion_source ``Submission.PartialDiffeomorph.halfBallInversion_source

open _root_.PartialDiffeomorph in
@[simp] theorem halfBallInversion_target (r : ℝ) (hr : r ≠ 0) :
    (halfBallInversion (E := E) r hr).target = {(0, -r)}ᶜ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.halfBallInversion_target then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.halfBallInversion_target"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.halfBallInversion_target ``Submission.PartialDiffeomorph.halfBallInversion_target

open _root_.PartialDiffeomorph in
theorem halfBallInversion_snd (r : ℝ) (hr : r ≠ 0) {p : E × ℝ}
    (hp : p ∈ (halfBallInversion r hr).source) :
    (halfBallInversion r hr p).2 =
      r * (r ^ 2 - (‖p.1‖ ^ 2 + p.2 ^ 2)) / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2) := by
  have hd := (halfBallInversion_denominator hp).ne'
  rw [halfBallInversion_apply]
  dsimp only
  field_simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.halfBallInversion_snd then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.halfBallInversion_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.halfBallInversion_snd ``Submission.PartialDiffeomorph.halfBallInversion_snd

open _root_.PartialDiffeomorph in
theorem norm_sq_halfBallInversion (r : ℝ) (hr : r ≠ 0) {p : E × ℝ}
    (hp : p ∈ (halfBallInversion r hr).source) :
    ‖(halfBallInversion r hr p).1‖ ^ 2 + (halfBallInversion r hr p).2 ^ 2 - r ^ 2 =
      -4 * r ^ 3 * p.2 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2) := by
  have hd := (halfBallInversion_denominator hp).ne'
  simp only [halfBallInversion_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.norm_sq_halfBallInversion then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.norm_sq_halfBallInversion"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.norm_sq_halfBallInversion ``Submission.PartialDiffeomorph.norm_sq_halfBallInversion

open _root_.PartialDiffeomorph in
theorem halfBallInversion_snd_nonneg_iff {r : ℝ} (hr : 0 < r) {p : E × ℝ}
    (hp : p ∈ (halfBallInversion r hr.ne').source) :
    0 ≤ (halfBallInversion r hr.ne' p).2 ↔ ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 := by
  rw [halfBallInversion_snd r hr.ne' hp, le_div_iff₀ (halfBallInversion_denominator hp)]
  simp only [_root_.MulZeroClass.zero_mul, mul_nonneg_iff_of_pos_left hr, sub_nonneg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.halfBallInversion_snd_nonneg_iff then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.halfBallInversion_snd_nonneg_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.halfBallInversion_snd_nonneg_iff ``Submission.PartialDiffeomorph.halfBallInversion_snd_nonneg_iff

open _root_.PartialDiffeomorph in
theorem norm_sq_halfBallInversion_le_iff {r : ℝ} (hr : 0 < r) {p : E × ℝ}
    (hp : p ∈ (halfBallInversion r hr.ne').source) :
    ‖(halfBallInversion r hr.ne' p).1‖ ^ 2 + (halfBallInversion r hr.ne' p).2 ^ 2 ≤ r ^ 2 ↔
      0 ≤ p.2 := by
  rw [← sub_nonpos, norm_sq_halfBallInversion r hr.ne' hp,
    div_le_iff₀ (halfBallInversion_denominator hp), _root_.MulZeroClass.zero_mul]
  have hc : 0 < 4 * r ^ 3 := by positivity
  constructor <;> intro hh <;> nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.norm_sq_halfBallInversion_le_iff then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.norm_sq_halfBallInversion_le_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.norm_sq_halfBallInversion_le_iff ``Submission.PartialDiffeomorph.norm_sq_halfBallInversion_le_iff

open _root_.PartialDiffeomorph in
theorem halfBallInversion_snd_nonpos_iff {r : ℝ} (hr : 0 < r) {p : E × ℝ}
    (hp : p ∈ (halfBallInversion r hr.ne').source) :
    (halfBallInversion r hr.ne' p).2 ≤ 0 ↔ r ^ 2 ≤ ‖p.1‖ ^ 2 + p.2 ^ 2 := by
  rw [halfBallInversion_snd r hr.ne' hp, div_le_iff₀ (halfBallInversion_denominator hp)]
  simp only [_root_.MulZeroClass.zero_mul]
  constructor <;> intro hh <;> nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.halfBallInversion_snd_nonpos_iff then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.halfBallInversion_snd_nonpos_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.halfBallInversion_snd_nonpos_iff ``Submission.PartialDiffeomorph.halfBallInversion_snd_nonpos_iff

open _root_.PartialDiffeomorph in
theorem norm_sq_halfBallInversion_ge_iff {r : ℝ} (hr : 0 < r) {p : E × ℝ}
    (hp : p ∈ (halfBallInversion r hr.ne').source) :
    r ^ 2 ≤ ‖(halfBallInversion r hr.ne' p).1‖ ^ 2 + (halfBallInversion r hr.ne' p).2 ^ 2 ↔
      p.2 ≤ 0 := by
  rw [← sub_nonneg, norm_sq_halfBallInversion r hr.ne' hp,
    le_div_iff₀ (halfBallInversion_denominator hp), _root_.MulZeroClass.zero_mul]
  have hc : 0 < 4 * r ^ 3 := by positivity
  constructor <;> intro hh <;> nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.norm_sq_halfBallInversion_ge_iff then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.norm_sq_halfBallInversion_ge_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.norm_sq_halfBallInversion_ge_iff ``Submission.PartialDiffeomorph.norm_sq_halfBallInversion_ge_iff

open _root_.PartialDiffeomorph in
theorem mem_halfBallInversion_source_of_snd_nonneg {r : ℝ} (hr : 0 < r)
    {p : E × ℝ} (hp : 0 ≤ p.2) : p ∈ (halfBallInversion r hr.ne').source := by
  intro heq
  change p = (0, -r) at heq
  rw [heq] at hp
  exact (not_le_of_gt hr) (by simpa using hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.mem_halfBallInversion_source_of_snd_nonneg then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.mem_halfBallInversion_source_of_snd_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.mem_halfBallInversion_source_of_snd_nonneg ``Submission.PartialDiffeomorph.mem_halfBallInversion_source_of_snd_nonneg

open _root_.PartialDiffeomorph in
theorem halfBall_subset_halfBallInversion_source {r : ℝ} (hr : 0 < r) :
    {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2} ⊆
      (halfBallInversion r hr.ne').source := by
  exact fun _ hp => mem_halfBallInversion_source_of_snd_nonneg hr hp.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.halfBall_subset_halfBallInversion_source then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.halfBall_subset_halfBallInversion_source"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.halfBall_subset_halfBallInversion_source ``Submission.PartialDiffeomorph.halfBall_subset_halfBallInversion_source

open _root_.PartialDiffeomorph in
theorem halfBallInversion_isImage_halfBall {r : ℝ} (hr : 0 < r) :
    (halfBallInversion (E := E) r hr.ne').toOpenPartialHomeomorph.IsImage
      {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2}
      {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2} := by
  intro p hp
  exact ((norm_sq_halfBallInversion_le_iff hr hp).and
    (halfBallInversion_snd_nonneg_iff hr hp)).trans and_comm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.halfBallInversion_isImage_halfBall then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.halfBallInversion_isImage_halfBall"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.halfBallInversion_isImage_halfBall ``Submission.PartialDiffeomorph.halfBallInversion_isImage_halfBall

open _root_.PartialDiffeomorph in
theorem halfBallInversion_image_halfBall {r : ℝ} (hr : 0 < r) :
    halfBallInversion (E := E) r hr.ne' ''
      {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2} =
      {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2} := by
  have h := (halfBallInversion_isImage_halfBall (E := E) hr).image_eq
  change halfBallInversion r hr.ne' '' ((halfBallInversion r hr.ne').source ∩
    {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2}) =
    (halfBallInversion r hr.ne').source ∩ {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2} at h
  rw [inter_eq_right.mpr (halfBall_subset_halfBallInversion_source hr)] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.halfBallInversion_image_halfBall then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.halfBallInversion_image_halfBall"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.halfBallInversion_image_halfBall ``Submission.PartialDiffeomorph.halfBallInversion_image_halfBall

open _root_.PartialDiffeomorph in
theorem norm_sq_halfBallInversion_eq_iff {r : ℝ} (hr : 0 < r) {p : E × ℝ}
    (hp : p ∈ (halfBallInversion r hr.ne').source) :
    ‖(halfBallInversion r hr.ne' p).1‖ ^ 2 + (halfBallInversion r hr.ne' p).2 ^ 2 = r ^ 2 ↔
      p.2 = 0 := by
  rw [← sub_eq_zero, norm_sq_halfBallInversion r hr.ne' hp, div_eq_zero_iff,
    mul_eq_zero]
  have hc : -4 * r ^ 3 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hr.ne')
  simp only [hc, false_or, (halfBallInversion_denominator hp).ne', or_false]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.norm_sq_halfBallInversion_eq_iff then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.norm_sq_halfBallInversion_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.norm_sq_halfBallInversion_eq_iff ``Submission.PartialDiffeomorph.norm_sq_halfBallInversion_eq_iff

open _root_.PartialDiffeomorph in
theorem halfBallInversion_isImage_disk {r : ℝ} (hr : 0 < r) :
    (halfBallInversion (E := E) r hr.ne').toOpenPartialHomeomorph.IsImage
      (_root_.Metric.closedBall 0 r ×ˢ {(0 : ℝ)})
      {p | ‖p.1‖ ^ 2 + p.2 ^ 2 = r ^ 2 ∧ 0 ≤ p.2} := by
  intro p hp
  change (‖(halfBallInversion r hr.ne' p).1‖ ^ 2 +
    (halfBallInversion r hr.ne' p).2 ^ 2 = r ^ 2 ∧
    0 ≤ (halfBallInversion r hr.ne' p).2) ↔ _
  rw [norm_sq_halfBallInversion_eq_iff hr hp, halfBallInversion_snd_nonneg_iff hr hp]
  simp only [_root_.Set.mem_prod, mem_closedBall_zero_iff, _root_.Set.mem_singleton_iff]
  constructor
  · rintro ⟨ht, hx⟩
    rw [ht] at hx
    exact ⟨by nlinarith [norm_nonneg p.1], ht⟩
  · rintro ⟨hx, ht⟩
    refine ⟨ht, ?_⟩
    rw [ht]
    nlinarith [norm_nonneg p.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.halfBallInversion_isImage_disk then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.halfBallInversion_isImage_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.halfBallInversion_isImage_disk ``Submission.PartialDiffeomorph.halfBallInversion_isImage_disk

open _root_.PartialDiffeomorph in
theorem halfBallInversion_image_disk {r : ℝ} (hr : 0 < r) :
    halfBallInversion (E := E) r hr.ne' '' (_root_.Metric.closedBall 0 r ×ˢ {(0 : ℝ)}) =
      {p | ‖p.1‖ ^ 2 + p.2 ^ 2 = r ^ 2 ∧ 0 ≤ p.2} := by
  have h := (halfBallInversion_isImage_disk (E := E) hr).image_eq
  change halfBallInversion r hr.ne' '' ((halfBallInversion r hr.ne').source ∩
    _root_.Metric.closedBall (0 : E) r ×ˢ {(0 : ℝ)}) =
    (halfBallInversion r hr.ne').target ∩ {p | ‖p.1‖ ^ 2 + p.2 ^ 2 = r ^ 2 ∧ 0 ≤ p.2} at h
  rw [inter_eq_right.mpr (show _root_.Metric.closedBall (0 : E) r ×ˢ {(0 : ℝ)} ⊆
    (halfBallInversion r hr.ne').source from fun p hp =>
      mem_halfBallInversion_source_of_snd_nonneg hr (le_of_eq hp.2.symm)),
    inter_eq_right.mpr (show {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 = r ^ 2 ∧ 0 ≤ p.2} ⊆
      (halfBallInversion r hr.ne').target from fun _ hp =>
        mem_halfBallInversion_source_of_snd_nonneg hr hp.2)] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.halfBallInversion_image_disk then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.halfBallInversion_image_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.halfBallInversion_image_disk ``Submission.PartialDiffeomorph.halfBallInversion_image_disk

open _root_.PartialDiffeomorph in
theorem halfBallInversion_image_hemisphere {r : ℝ} (hr : 0 < r) :
    halfBallInversion (E := E) r hr.ne' ''
      {p | ‖p.1‖ ^ 2 + p.2 ^ 2 = r ^ 2 ∧ 0 ≤ p.2} =
      closedBall 0 r ×ˢ {(0 : ℝ)} := by
  have h := (halfBallInversion_isImage_disk (E := E) hr).symm.image_eq
  change halfBallInversion r hr.ne' '' ((halfBallInversion r hr.ne').target ∩
    {p | ‖p.1‖ ^ 2 + p.2 ^ 2 = r ^ 2 ∧ 0 ≤ p.2}) =
    (halfBallInversion r hr.ne').source ∩ _root_.Metric.closedBall (0 : E) r ×ˢ {(0 : ℝ)} at h
  rw [inter_eq_right.mpr (show {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 = r ^ 2 ∧ 0 ≤ p.2} ⊆
    (halfBallInversion r hr.ne').target from fun _ hp =>
      mem_halfBallInversion_source_of_snd_nonneg hr hp.2),
    inter_eq_right.mpr (show _root_.Metric.closedBall (0 : E) r ×ˢ {(0 : ℝ)} ⊆
      (halfBallInversion r hr.ne').source from fun p hp =>
        mem_halfBallInversion_source_of_snd_nonneg hr (le_of_eq hp.2.symm))] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.halfBallInversion_image_hemisphere then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.halfBallInversion_image_hemisphere"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.halfBallInversion_image_hemisphere ``Submission.PartialDiffeomorph.halfBallInversion_image_hemisphere

open _root_.PartialDiffeomorph in
theorem halfBallInversion_eq_self_of_norm_eq {r : ℝ} (hr : r ≠ 0) {x : E}
    (hx : ‖x‖ = r) : halfBallInversion r hr (x, 0) = (x, 0) := by
  rw [halfBallInversion_apply, hx]
  have hc : 2 * r ^ 2 / (r ^ 2 + r ^ 2) = 1 := by
    field_simp
    ring
  simp only [hc, one_smul, zero_add, one_mul, sub_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.halfBallInversion_eq_self_of_norm_eq then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.halfBallInversion_eq_self_of_norm_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.halfBallInversion_eq_self_of_norm_eq ``Submission.PartialDiffeomorph.halfBallInversion_eq_self_of_norm_eq

end PartialDiffeomorph
