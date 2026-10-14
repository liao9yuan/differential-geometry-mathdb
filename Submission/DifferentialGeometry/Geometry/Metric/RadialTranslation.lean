import Submission.DifferentialGeometry.Geometry.Metric.RadialField
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.Deriv.Inv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.InnerProductSpace

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialTranslation (s : ℝ) (x : E) : E := ((‖x‖ + s) / ‖x‖) • x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.radialTranslation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.radialTranslation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.radialTranslation ``Submission.DifferentialGeometry.Geometry.Riemannian.radialTranslation

theorem norm_radialTranslation (s : ℝ) {x : E} (hx : _root_.Max.max 0 (-s) < ‖x‖) :
    ‖radialTranslation s x‖ = ‖x‖ + s := by
  have hr : 0 < ‖x‖ := (le_max_left _ _).trans_lt hx
  have hrs : 0 < ‖x‖ + s := by linarith [(le_max_right 0 (-s)).trans_lt hx]
  rw [radialTranslation, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hrs hr)]
  exact div_mul_cancel₀ _ hr.ne'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.norm_radialTranslation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.norm_radialTranslation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.norm_radialTranslation ``Submission.DifferentialGeometry.Geometry.Riemannian.norm_radialTranslation

private theorem radial_translation_mem_target (s : ℝ) {x : E}
    (hx : _root_.Max.max 0 (-s) < ‖x‖) : _root_.Max.max 0 s < ‖radialTranslation s x‖ := by
  rw [norm_radialTranslation s hx]
  rw [max_lt_iff]
  constructor
  · linarith [(le_max_right 0 (-s)).trans_lt hx]
  · linarith [(le_max_left 0 (-s)).trans_lt hx]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.radial_translation_mem_target
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.radial_translation_mem_target target :: scope.openDecls } }

theorem radialTranslation_neg_cancel (s : ℝ) {x : E} (hx : _root_.Max.max 0 (-s) < ‖x‖) :
    radialTranslation (-s) (radialTranslation s x) = x := by
  have hr : ‖x‖ ≠ 0 := ne_of_gt ((le_max_left _ _).trans_lt hx)
  have hrs : ‖x‖ + s ≠ 0 := by
    have h := (le_max_right 0 (-s)).trans_lt hx
    linarith
  rw [radialTranslation, norm_radialTranslation s hx, radialTranslation, smul_smul]
  have hc : ((‖x‖ + s + -s) / (‖x‖ + s)) * ((‖x‖ + s) / ‖x‖) = 1 := by
    field_simp
    ring
  rw [hc, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.radialTranslation_neg_cancel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.radialTranslation_neg_cancel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.radialTranslation_neg_cancel ``Submission.DifferentialGeometry.Geometry.Riemannian.radialTranslation_neg_cancel

theorem contDiffAt_radialTranslation (s : ℝ) {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (radialTranslation s) x := by
  have hn := contDiffAt_norm ℝ (n := ∞) hx
  exact ((hn.add contDiffAt_const).div hn (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.contDiffAt_radialTranslation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.contDiffAt_radialTranslation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.contDiffAt_radialTranslation ``Submission.DifferentialGeometry.Geometry.Riemannian.contDiffAt_radialTranslation

def radialTranslationDiffeomorph (s : ℝ) :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ where
  toFun := radialTranslation s
  invFun := radialTranslation (-s)
  source := {x | _root_.Max.max 0 (-s) < ‖x‖}
  target := {x | _root_.Max.max 0 s < ‖x‖}
  map_source' := fun _ hx => radial_translation_mem_target s hx
  map_target' := fun _ hx => by
    simpa only [_root_.Set.mem_ofPred_eq, neg_neg] using radial_translation_mem_target (-s)
      (by simpa only [_root_.Set.mem_ofPred_eq, neg_neg] using hx)
  left_inv' := fun _ hx => radialTranslation_neg_cancel s hx
  right_inv' := fun _ hx => by
    simpa only [neg_neg] using radialTranslation_neg_cancel (-s)
      (by simpa only [_root_.Set.mem_ofPred_eq, neg_neg] using hx)
  open_source := isOpen_lt continuous_const continuous_norm
  open_target := isOpen_lt continuous_const continuous_norm
  contMDiffOn_toFun := by
    intro x hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp ((le_max_left _ _).trans_lt hx)
    exact ((contDiffAt_radialTranslation s hx0).contMDiffAt).contMDiffWithinAt
  contMDiffOn_invFun := by
    intro x hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp ((le_max_left _ _).trans_lt hx)
    exact ((contDiffAt_radialTranslation (-s) hx0).contMDiffAt).contMDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph ``Submission.DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph

@[simp] theorem radialTranslationDiffeomorph_apply (s : ℝ) (x : E) :
    radialTranslationDiffeomorph s x = radialTranslation s x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph_apply

@[simp] theorem radialTranslationDiffeomorph_source (s : ℝ) :
    (radialTranslationDiffeomorph (E := E) s).source = {x | _root_.Max.max 0 (-s) < ‖x‖} := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph_source ``Submission.DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph_source

@[simp] theorem radialTranslationDiffeomorph_target (s : ℝ) :
    (radialTranslationDiffeomorph (E := E) s).target = {x | _root_.Max.max 0 s < ‖x‖} := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph_target ``Submission.DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph_target

@[simp] theorem radialTranslationDiffeomorph_symm_apply (s : ℝ) (x : E) :
    (radialTranslationDiffeomorph s).symm x = radialTranslation (-s) x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.radialTranslationDiffeomorph_symm_apply

theorem fderiv_radialTranslation_apply (s : ℝ) {x : E} (hx : x ≠ 0) (v : E) :
    fderiv ℝ (radialTranslation s) x v =
      ((‖x‖ + s) / ‖x‖) • v - (s * ⟪x, v⟫_ℝ / ‖x‖ ^ 3) • x := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hn : HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
    have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hr)
    convert h using 1
    · funext y
      exact (Real.sqrt_sq (norm_nonneg y)).symm
    · ext u
      simp only [smul_apply, smul_eq_mul, Real.sqrt_sq (norm_nonneg x)]
      field_simp
      ring
  have hc : HasFDerivAt (fun y : E => (‖y‖ + s) / ‖y‖)
      ((-s / ‖x‖ ^ 3) • innerSL ℝ x) x := by
    convert! (hn.add_const s).mul ((hasDerivAt_inv hr).comp_hasFDerivAt x hn) using 1
    ext u
    simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply, Function.comp_apply]
    field_simp
    ring
  have hd := hc.smul (hasFDerivAt_id x)
  have hv := congrArg (fun D : E →L[ℝ] E => D v) hd.fderiv
  change fderiv ℝ (radialTranslation s) x v = _ at hv
  rw [hv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply, smul_eq_mul, id_eq]
  have heq : (-s / ‖x‖ ^ 3) * ⟪x, v⟫_ℝ = -(s * ⟪x, v⟫_ℝ / ‖x‖ ^ 3) := by ring
  rw [heq]
  module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.fderiv_radialTranslation_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.fderiv_radialTranslation_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.fderiv_radialTranslation_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.fderiv_radialTranslation_apply

theorem mfderiv_radialTranslation_apply (s : ℝ) {x : E} (hx : x ≠ 0) (v : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (radialTranslation s) x v =
      ((‖x‖ + s) / ‖x‖) • v - (s * ⟪x, v⟫_ℝ / ‖x‖ ^ 3) • x := by
  rw [mfderiv_eq_fderiv]
  exact fderiv_radialTranslation_apply s hx v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.mfderiv_radialTranslation_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.mfderiv_radialTranslation_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.mfderiv_radialTranslation_apply ``Submission.DifferentialGeometry.Geometry.Riemannian.mfderiv_radialTranslation_apply

theorem radialBilinearField_radialTranslation (s A : ℝ) {x : E}
    (hx : _root_.Max.max 0 (-s) < ‖x‖) (v w : E) :
    radialBilinearField (fun _ => A) (radialTranslation s x)
      (fderiv ℝ (radialTranslation s) x v) (fderiv ℝ (radialTranslation s) x w) =
      radialBilinearField (fun _ => A) x v w := by
  have hr : 0 < ‖x‖ := (le_max_left _ _).trans_lt hx
  have hx0 : x ≠ 0 := norm_pos_iff.mp hr
  have hrs : 0 < ‖x‖ + s := by linarith [(le_max_right 0 (-s)).trans_lt hx]
  rw [fderiv_radialTranslation_apply s hx0, fderiv_radialTranslation_apply s hx0]
  simp only [radialBilinearField_apply, norm_radialTranslation s hx]
  simp only [radialTranslation, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm v x, real_inner_comm w x,
    real_inner_self_eq_norm_sq]
  field_simp [hr.ne', hrs.ne']
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.radialBilinearField_radialTranslation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.radialBilinearField_radialTranslation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.radialBilinearField_radialTranslation ``Submission.DifferentialGeometry.Geometry.Riemannian.radialBilinearField_radialTranslation

end DifferentialGeometry.Geometry.Riemannian
