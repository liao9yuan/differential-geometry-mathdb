import Submission.DifferentialGeometry.Topology.Diffeomorph.Perturbation
import Submission.DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn
import Submission.DifferentialGeometry.Analysis.Calculus.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.NNReal

private theorem lipschitz_smoothAbs_sub_norm
    {E : Type*} [SeminormedAddCommGroup E] {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith 1 (fun x : E => Real.smoothAbs ε ‖x‖ - ‖x‖) := by
  have hbound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
      |(Real.smoothAbs ε a - a) - (Real.smoothAbs ε b - b)| ≤ b - a := by
    have hm := (Real.smoothAbs.strictMonoOn_Ici hε).monotoneOn ha hb hab
    have hl := (Real.smoothAbs.lipschitzWith ε).dist_le_mul a b
    simp only [Real.dist_eq, NNReal.coe_one, one_mul, abs_of_nonpos (sub_nonpos.mpr hab),
      abs_of_nonpos (sub_nonpos.mpr hm)] at hl
    rw [abs_le]
    constructor <;> linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs]
  rcases le_total ‖x‖ ‖y‖ with hxy | hyx
  · exact (hbound ‖x‖ ‖y‖ (norm_nonneg _) (norm_nonneg _) hxy).trans
      (by simpa only [norm_sub_rev] using norm_sub_norm_le y x)
  · rw [abs_sub_comm]
    exact (hbound ‖y‖ ‖x‖ (norm_nonneg _) (norm_nonneg _) hyx).trans (norm_sub_norm_le x y)

run_cmd do
  let target := ``Submission.lipschitz_smoothAbs_sub_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `lipschitz_smoothAbs_sub_norm target :: scope.openDecls } }

private theorem lipschitz_smoothAbs_norm_shift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ε : ℝ} (hε : 0 < ε) (v : E) :
    LipschitzWith ‖v‖₊ (fun x : E => (Real.smoothAbs ε ‖x‖ - ‖x‖) • v) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← sub_smul, norm_smul]
  have hb := (lipschitz_smoothAbs_sub_norm (E := E) hε).dist_le_mul x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hb
  change |(Real.smoothAbs ε ‖x‖ - ‖x‖) - (Real.smoothAbs ε ‖y‖ - ‖y‖)| * ‖v‖ ≤ ‖v‖ * _root_.Dist.dist x y
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hb (norm_nonneg v)

run_cmd do
  let target := ``Submission.lipschitz_smoothAbs_norm_shift
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `lipschitz_smoothAbs_norm_shift target :: scope.openDecls } }

noncomputable def Homeomorph.smoothAbsNormShift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ε : ℝ} (hε : 0 < ε) (v : E) (hv : ‖v‖ < 1) : E ≃ₜ E :=
  (Diffeomorph.addLipschitz (𝕜 := ℝ) (n := 0)
    (contDiff_zero.mpr (lipschitz_smoothAbs_norm_shift hε v).continuous)
    (lipschitz_smoothAbs_norm_shift hε v) (show ‖v‖₊ < 1 from hv)).toHomeomorph

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Homeomorph
  let env ← Lean.getEnv
  if env.contains `Homeomorph.smoothAbsNormShift then
    throwError "Refusing to shadow existing declaration Homeomorph.smoothAbsNormShift"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.smoothAbsNormShift ``Submission.Homeomorph.smoothAbsNormShift

@[simp] theorem Homeomorph.smoothAbsNormShift_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ε : ℝ} (hε : 0 < ε) (v : E) (hv : ‖v‖ < 1) (x : E) :
    Homeomorph.smoothAbsNormShift hε v hv x = x + (Real.smoothAbs ε ‖x‖ - ‖x‖) • v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.smoothAbsNormShift_apply then
    throwError "Refusing to shadow existing declaration Homeomorph.smoothAbsNormShift_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.smoothAbsNormShift_apply ``Submission.Homeomorph.smoothAbsNormShift_apply

theorem Homeomorph.isLocalDiffeomorphAt_smoothAbsNormShift
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ε : ℝ} (hε : 0 < ε) (v : E) (hv : ‖v‖ < 1) {x : E} (hx : x ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (Homeomorph.smoothAbsNormShift hε v hv) x := by
  let f : E → E := fun y => (Real.smoothAbs ε ‖y‖ - ‖y‖) • v
  have hf : ContDiffOn ℝ ∞ f ({0}ᶜ : Set E) := by
    intro y hy
    have hn : ContDiffAt ℝ ∞ (_root_.Norm.norm : E → ℝ) y := contDiffAt_norm ℝ hy
    exact (((Real.smoothAbs.contDiff ε).contDiffAt.comp y hn).sub hn).smul
      contDiffAt_const |>.contDiffWithinAt
  have hfAt := hf.contDiffAt (isClosed_singleton.isOpen_compl.mem_nhds hx)
  have hb : ‖-fderiv ℝ f x‖ < 1 := by
    rw [norm_neg]
    exact (norm_fderiv_le_of_lipschitz ℝ (lipschitz_smoothAbs_norm_shift hε v)).trans_lt hv
  have hi : IsUnit (1 + fderiv ℝ f x) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hb
  let L : E ≃L[ℝ] E := ContinuousLinearEquiv.ofUnit hi.unit
  have hL : (L : E →L[ℝ] E) = 1 + fderiv ℝ f x := hi.unit_spec
  apply
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
    _ (contDiff_id.contDiffOn.add hf).contMDiffOn isClosed_singleton.isOpen_compl x hx L
  rw [hL]
  exact ((hasFDerivAt_id x).add (hfAt.differentiableAt (by simp)).hasFDerivAt).hasMFDerivAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.isLocalDiffeomorphAt_smoothAbsNormShift then
    throwError "Refusing to shadow existing declaration Homeomorph.isLocalDiffeomorphAt_smoothAbsNormShift"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.isLocalDiffeomorphAt_smoothAbsNormShift ``Submission.Homeomorph.isLocalDiffeomorphAt_smoothAbsNormShift

theorem Homeomorph.smoothAbsNormShift_apply_eq_self
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ε : ℝ} (hε : 0 < ε) (v : E) (hv : ‖v‖ < 1) {x : E} (hx : ε ≤ ‖x‖) :
    smoothAbsNormShift hε v hv x = x := by
  rw [smoothAbsNormShift_apply, Real.smoothAbs.eq_self_of_le hε hx, sub_self, zero_smul, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.smoothAbsNormShift_apply_eq_self then
    throwError "Refusing to shadow existing declaration Homeomorph.smoothAbsNormShift_apply_eq_self"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.smoothAbsNormShift_apply_eq_self ``Submission.Homeomorph.smoothAbsNormShift_apply_eq_self
