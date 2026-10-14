import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.Abel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Manifold _root_.NNReal

namespace Diffeomorph
open _root_.Diffeomorph

section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {n : ℕ∞ω} {f : E → E} {C : ℝ≥0}

open _root_.Diffeomorph in
noncomputable def addLipschitz (hf : ContDiff 𝕜 n f)
    (hlip : LipschitzWith C f) (hC : C < 1) :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) E E n := by
  have ha : ApproximatesLinearOn (fun x => x + f x)
      (ContinuousLinearEquiv.refl 𝕜 E : E →L[𝕜] E) Set.univ C := by
    intro x hx y hy
    convert hlip.norm_sub_le x y using 1
    congr 1
    simp only [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_apply]
    abel
  have hc : Subsingleton E ∨
      C < ‖((ContinuousLinearEquiv.refl 𝕜 E).symm : E →L[𝕜] E)‖₊⁻¹ := by
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact Or.inl hE
    · exact Or.inr (by simpa using hC)
  let h : E ≃ₜ E := ApproximatesLinearOn.toHomeomorph
    (f' := ContinuousLinearEquiv.refl 𝕜 E) (fun x => x + f x) ha hc
  have hh : ContDiff 𝕜 n h := contDiff_id.add hf
  refine
    { toEquiv := h.toEquiv
      contMDiff_toFun := hh.contMDiff
      contMDiff_invFun := ?_ }
  by_cases hn : n = 0
  · subst n
    exact (contDiff_zero.mpr h.symm.continuous).contMDiff
  · have hi : ∀ x, IsUnit (1 + fderiv 𝕜 f x) := by
      intro x
      have hb : ‖-fderiv 𝕜 f x‖ < 1 := by
        rw [norm_neg]
        exact (norm_fderiv_le_of_lipschitz 𝕜 hlip).trans_lt (by exact_mod_cast hC)
      simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hb
    let e : E → E ≃L[𝕜] E := fun x => ContinuousLinearEquiv.ofUnit (hi x).unit
    have he : ∀ x, (e x : E →L[𝕜] E) = 1 + fderiv 𝕜 f x := by
      intro x
      exact (hi x).unit_spec
    apply (h.contDiff_symm (f₀' := e) ?_ hh).contMDiff
    intro x
    rw [he]
    exact (hasFDerivAt_id x).add ((hf.differentiable hn) x).hasFDerivAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.addLipschitz then
    throwError "Refusing to shadow existing declaration Diffeomorph.addLipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.addLipschitz ``Submission.Diffeomorph.addLipschitz

open _root_.Diffeomorph in
@[simp] theorem addLipschitz_apply (hf : ContDiff 𝕜 n f)
    (hlip : LipschitzWith C f) (hC : C < 1) (x : E) :
    addLipschitz hf hlip hC x = x + f x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.addLipschitz_apply then
    throwError "Refusing to shadow existing declaration Diffeomorph.addLipschitz_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.addLipschitz_apply ``Submission.Diffeomorph.addLipschitz_apply

open _root_.Diffeomorph in
theorem addLipschitz_apply_eq_self_iff (hf : ContDiff 𝕜 n f)
    (hlip : LipschitzWith C f) (hC : C < 1) (x : E) :
    addLipschitz hf hlip hC x = x ↔ f x = 0 := by
  rw [addLipschitz_apply, add_eq_left]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.addLipschitz_apply_eq_self_iff then
    throwError "Refusing to shadow existing declaration Diffeomorph.addLipschitz_apply_eq_self_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.addLipschitz_apply_eq_self_iff ``Submission.Diffeomorph.addLipschitz_apply_eq_self_iff

open _root_.Diffeomorph in
theorem addLipschitz_symm_apply_eq_self_iff (hf : ContDiff 𝕜 n f)
    (hlip : LipschitzWith C f) (hC : C < 1) (x : E) :
    (addLipschitz hf hlip hC).symm x = x ↔ f x = 0 := by
  rw [← addLipschitz_apply_eq_self_iff hf hlip hC x]
  constructor
  · intro hx
    have h := congrArg (addLipschitz hf hlip hC) hx
    rw [_root_.Diffeomorph.apply_symm_apply] at h
    exact h.symm
  · intro hx
    have h := congrArg (addLipschitz hf hlip hC).symm hx
    rw [_root_.Diffeomorph.symm_apply_apply] at h
    exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.addLipschitz_symm_apply_eq_self_iff then
    throwError "Refusing to shadow existing declaration Diffeomorph.addLipschitz_symm_apply_eq_self_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.addLipschitz_symm_apply_eq_self_iff ``Submission.Diffeomorph.addLipschitz_symm_apply_eq_self_iff

open _root_.Diffeomorph in
@[simp] theorem addLipschitz_zero (hC : C < 1) :
    addLipschitz (𝕜 := 𝕜) (E := E) (n := n) contDiff_zero_fun
      ((LipschitzWith.const (0 : E)).weaken (show 0 ≤ C from zero_le)) hC = Diffeomorph.refl 𝓘(𝕜, E) E n := by
  apply Diffeomorph.ext
  intro x
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.addLipschitz_zero then
    throwError "Refusing to shadow existing declaration Diffeomorph.addLipschitz_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.addLipschitz_zero ``Submission.Diffeomorph.addLipschitz_zero

open _root_.Diffeomorph in
theorem support_addLipschitz_sub_id (hf : ContDiff 𝕜 n f)
    (hlip : LipschitzWith C f) (hC : C < 1) :
    Function.support (fun x => addLipschitz hf hlip hC x - x) = Function.support f := by
  ext x
  simp only [Function.mem_support, sub_ne_zero]
  exact not_congr (addLipschitz_apply_eq_self_iff hf hlip hC x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.support_addLipschitz_sub_id then
    throwError "Refusing to shadow existing declaration Diffeomorph.support_addLipschitz_sub_id"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.support_addLipschitz_sub_id ``Submission.Diffeomorph.support_addLipschitz_sub_id

open _root_.Diffeomorph in
theorem support_addLipschitz_symm_sub_id (hf : ContDiff 𝕜 n f)
    (hlip : LipschitzWith C f) (hC : C < 1) :
    Function.support (fun x => (addLipschitz hf hlip hC).symm x - x) =
      Function.support f := by
  ext x
  simp only [Function.mem_support, sub_ne_zero]
  exact not_congr (addLipschitz_symm_apply_eq_self_iff hf hlip hC x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.support_addLipschitz_symm_sub_id then
    throwError "Refusing to shadow existing declaration Diffeomorph.support_addLipschitz_symm_sub_id"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.support_addLipschitz_symm_sub_id ``Submission.Diffeomorph.support_addLipschitz_symm_sub_id

open _root_.Diffeomorph in
theorem hasCompactSupport_addLipschitz_sub_id (hf : ContDiff 𝕜 n f)
    (hlip : LipschitzWith C f) (hC : C < 1) (hs : HasCompactSupport f) :
    HasCompactSupport (fun x => addLipschitz hf hlip hC x - x) := by
  simpa only [HasCompactSupport, tsupport, support_addLipschitz_sub_id] using hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.hasCompactSupport_addLipschitz_sub_id then
    throwError "Refusing to shadow existing declaration Diffeomorph.hasCompactSupport_addLipschitz_sub_id"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.hasCompactSupport_addLipschitz_sub_id ``Submission.Diffeomorph.hasCompactSupport_addLipschitz_sub_id

open _root_.Diffeomorph in
theorem hasCompactSupport_addLipschitz_symm_sub_id (hf : ContDiff 𝕜 n f)
    (hlip : LipschitzWith C f) (hC : C < 1) (hs : HasCompactSupport f) :
    HasCompactSupport (fun x => (addLipschitz hf hlip hC).symm x - x) := by
  simpa only [HasCompactSupport, tsupport, support_addLipschitz_symm_sub_id] using hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.hasCompactSupport_addLipschitz_symm_sub_id then
    throwError "Refusing to shadow existing declaration Diffeomorph.hasCompactSupport_addLipschitz_symm_sub_id"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.hasCompactSupport_addLipschitz_symm_sub_id ``Submission.Diffeomorph.hasCompactSupport_addLipschitz_symm_sub_id

open _root_.Diffeomorph in
theorem contDiff_addLipschitz_symm {𝕜 P E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {n : ℕ∞ω} {g : P × E → E} {C : P → ℝ≥0}
    (hg : ContDiff 𝕜 n g) (hn : n ≠ 0)
    (hlip : ∀ p, LipschitzWith (C p) (fun x => g (p, x)))
    (hC : ∀ p, C p < 1) :
    ContDiff 𝕜 n (fun z : P × E =>
      (addLipschitz (hg.comp (contDiff_const.prodMk contDiff_id))
        (hlip z.1) (hC z.1)).symm z.2) := by
  let e : P → Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) E E n := fun p =>
    addLipschitz (hg.comp (contDiff_const.prodMk contDiff_id)) (hlip p) (hC p)
  change ContDiff 𝕜 n (fun z : P × E => (e z.1).symm z.2)
  rw [contDiff_iff_contDiffAt]
  intro z
  let x : E := (e z.1).symm z.2
  let F : (P × E) × E → E := fun w => w.2 + g (w.1.1, w.2) - w.1.2
  have hF : ContDiff 𝕜 n F :=
    (contDiff_snd.add (hg.comp (contDiff_fst.fst.prodMk contDiff_snd))).sub
      contDiff_fst.snd
  have hFx : F (z, x) = 0 := by
    change e z.1 ((e z.1).symm z.2) - z.2 = 0
    rw [_root_.Diffeomorph.apply_symm_apply, sub_self]
  have hslice : DifferentiableAt 𝕜 (fun y => g (z.1, y)) x :=
    (hg.comp (contDiff_const.prodMk contDiff_id)).differentiable hn x
  have hpartial : fderiv 𝕜 F (z, x) ∘L ContinuousLinearMap.inr 𝕜 (P × E) E =
      1 + fderiv 𝕜 (fun y => g (z.1, y)) x := by
    have hrestrict := ((hF.differentiable hn) (z, x)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_right (𝕜 := 𝕜) z x)
    exact hrestrict.unique (((hasFDerivAt_id x).add hslice.hasFDerivAt).sub_const z.2)
  have hi : (fderiv 𝕜 F (z, x) ∘L ContinuousLinearMap.inr 𝕜 (P × E) E).IsInvertible := by
    rw [hpartial]
    have hb : ‖-fderiv 𝕜 (fun y => g (z.1, y)) x‖ < 1 := by
      rw [norm_neg]
      exact (norm_fderiv_le_of_lipschitz 𝕜 (hlip z.1)).trans_lt (by exact_mod_cast hC z.1)
    have hu : IsUnit (1 + fderiv 𝕜 (fun y => g (z.1, y)) x) := by
      simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hb
    exact ⟨ContinuousLinearEquiv.ofUnit hu.unit, hu.unit_spec⟩
  let ψ : P × E → E := hF.contDiffAt.implicitFunction hn hi
  have hψ : ContDiffAt 𝕜 n ψ z := hF.contDiffAt.contDiffAt_implicitFunction hn hi
  apply hψ.congr_of_eventuallyEq
  filter_upwards [hF.contDiffAt.eventually_apply_implicitFunction hn hi] with w hw
  apply (e w.1).injective
  change e w.1 ((e w.1).symm w.2) = e w.1 (ψ w)
  rw [_root_.Diffeomorph.apply_symm_apply]
  exact (sub_eq_zero.mp (hw.trans hFx)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.contDiff_addLipschitz_symm then
    throwError "Refusing to shadow existing declaration Diffeomorph.contDiff_addLipschitz_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.contDiff_addLipschitz_symm ``Submission.Diffeomorph.contDiff_addLipschitz_symm

end

section Isotopy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : E → E} {C : ℝ≥0}

omit [CompleteSpace E] in
open _root_.Diffeomorph in
private theorem lipschitzWith_smoothTransition_smul (hlip : LipschitzWith C f) (t : ℝ) :
    LipschitzWith C (fun x => Real.smoothTransition t • f x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← smul_sub, norm_smul,
    Real.norm_of_nonneg (Real.smoothTransition.nonneg t)]
  calc
    Real.smoothTransition t * ‖f x - f y‖ ≤ ‖f x - f y‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one t)
    _ ≤ (C : ℝ) * _root_.Dist.dist x y := by simpa only [dist_eq_norm] using hlip.norm_sub_le x y

run_cmd do
  let target := ``Submission.Diffeomorph.lipschitzWith_smoothTransition_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.lipschitzWith_smoothTransition_smul target :: scope.openDecls } }

open _root_.Diffeomorph in
noncomputable def addLipschitzIsotopy (hf : ContDiff ℝ ∞ f)
    (hlip : LipschitzWith C f) (hC : C < 1) (t : ℝ) : E ≃ₘ[ℝ] E :=
  addLipschitz (contDiff_const.smul hf) (lipschitzWith_smoothTransition_smul hlip t) hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.addLipschitzIsotopy then
    throwError "Refusing to shadow existing declaration Diffeomorph.addLipschitzIsotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.addLipschitzIsotopy ``Submission.Diffeomorph.addLipschitzIsotopy

open _root_.Diffeomorph in
@[simp] theorem addLipschitzIsotopy_apply (hf : ContDiff ℝ ∞ f)
    (hlip : LipschitzWith C f) (hC : C < 1) (t : ℝ) (x : E) :
    addLipschitzIsotopy hf hlip hC t x = x + Real.smoothTransition t • f x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.addLipschitzIsotopy_apply then
    throwError "Refusing to shadow existing declaration Diffeomorph.addLipschitzIsotopy_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.addLipschitzIsotopy_apply ``Submission.Diffeomorph.addLipschitzIsotopy_apply

open _root_.Diffeomorph in
theorem contDiff_addLipschitzIsotopy (hf : ContDiff ℝ ∞ f)
    (hlip : LipschitzWith C f) (hC : C < 1) :
    ContDiff ℝ ∞ (fun z : ℝ × E => addLipschitzIsotopy hf hlip hC z.1 z.2) :=
  contDiff_snd.add ((Real.smoothTransition.contDiff.comp contDiff_fst).smul
    (hf.comp contDiff_snd))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.contDiff_addLipschitzIsotopy then
    throwError "Refusing to shadow existing declaration Diffeomorph.contDiff_addLipschitzIsotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.contDiff_addLipschitzIsotopy ``Submission.Diffeomorph.contDiff_addLipschitzIsotopy

open _root_.Diffeomorph in
theorem contDiff_addLipschitzIsotopy_symm (hf : ContDiff ℝ ∞ f)
    (hlip : LipschitzWith C f) (hC : C < 1) :
    ContDiff ℝ ∞ (fun z : ℝ × E => (addLipschitzIsotopy hf hlip hC z.1).symm z.2) :=
  contDiff_addLipschitz_symm
    ((Real.smoothTransition.contDiff.comp contDiff_fst).smul (hf.comp contDiff_snd))
    (by simp) (lipschitzWith_smoothTransition_smul hlip) (fun _ => hC)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.contDiff_addLipschitzIsotopy_symm then
    throwError "Refusing to shadow existing declaration Diffeomorph.contDiff_addLipschitzIsotopy_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.contDiff_addLipschitzIsotopy_symm ``Submission.Diffeomorph.contDiff_addLipschitzIsotopy_symm

open _root_.Diffeomorph in
theorem addLipschitzIsotopy_eq_refl_of_nonpos (hf : ContDiff ℝ ∞ f)
    (hlip : LipschitzWith C f) (hC : C < 1) {t : ℝ} (ht : t ≤ 0) :
    addLipschitzIsotopy hf hlip hC t = Diffeomorph.refl 𝓘(ℝ, E) E ∞ := by
  apply Diffeomorph.ext
  intro x
  change x + Real.smoothTransition t • f x = x
  simp only [Real.smoothTransition.zero_of_nonpos ht, zero_smul, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.addLipschitzIsotopy_eq_refl_of_nonpos then
    throwError "Refusing to shadow existing declaration Diffeomorph.addLipschitzIsotopy_eq_refl_of_nonpos"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.addLipschitzIsotopy_eq_refl_of_nonpos ``Submission.Diffeomorph.addLipschitzIsotopy_eq_refl_of_nonpos

open _root_.Diffeomorph in
theorem addLipschitzIsotopy_eq_addLipschitz_of_one_le (hf : ContDiff ℝ ∞ f)
    (hlip : LipschitzWith C f) (hC : C < 1) {t : ℝ} (ht : 1 ≤ t) :
    addLipschitzIsotopy hf hlip hC t = addLipschitz hf hlip hC := by
  apply Diffeomorph.ext
  intro x
  simp only [addLipschitzIsotopy_apply, Real.smoothTransition.one_of_one_le ht,
    one_smul, addLipschitz_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.addLipschitzIsotopy_eq_addLipschitz_of_one_le then
    throwError "Refusing to shadow existing declaration Diffeomorph.addLipschitzIsotopy_eq_addLipschitz_of_one_le"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.addLipschitzIsotopy_eq_addLipschitz_of_one_le ``Submission.Diffeomorph.addLipschitzIsotopy_eq_addLipschitz_of_one_le

open _root_.Diffeomorph in
@[simp] theorem addLipschitzIsotopy_zero (hf : ContDiff ℝ ∞ f)
    (hlip : LipschitzWith C f) (hC : C < 1) :
    addLipschitzIsotopy hf hlip hC 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ :=
  addLipschitzIsotopy_eq_refl_of_nonpos hf hlip hC le_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.addLipschitzIsotopy_zero then
    throwError "Refusing to shadow existing declaration Diffeomorph.addLipschitzIsotopy_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.addLipschitzIsotopy_zero ``Submission.Diffeomorph.addLipschitzIsotopy_zero

open _root_.Diffeomorph in
@[simp] theorem addLipschitzIsotopy_one (hf : ContDiff ℝ ∞ f)
    (hlip : LipschitzWith C f) (hC : C < 1) :
    addLipschitzIsotopy hf hlip hC 1 = addLipschitz hf hlip hC :=
  addLipschitzIsotopy_eq_addLipschitz_of_one_le hf hlip hC le_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.addLipschitzIsotopy_one then
    throwError "Refusing to shadow existing declaration Diffeomorph.addLipschitzIsotopy_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.addLipschitzIsotopy_one ``Submission.Diffeomorph.addLipschitzIsotopy_one

open _root_.Diffeomorph in
theorem addLipschitzIsotopy_eq_self_of_notMem_tsupport (hf : ContDiff ℝ ∞ f)
    (hlip : LipschitzWith C f) (hC : C < 1) (t : ℝ) {x : E} (hx : x ∉ tsupport f) :
    addLipschitzIsotopy hf hlip hC t x = x ∧
      (addLipschitzIsotopy hf hlip hC t).symm x = x := by
  have hz : f x = 0 := image_eq_zero_of_notMem_tsupport hx
  have heq : addLipschitzIsotopy hf hlip hC t x = x := by
    simp only [addLipschitzIsotopy_apply, hz, smul_zero, add_zero]
  refine ⟨heq, ?_⟩
  have h := congrArg (addLipschitzIsotopy hf hlip hC t).symm heq
  simpa only [_root_.Diffeomorph.symm_apply_apply] using h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.addLipschitzIsotopy_eq_self_of_notMem_tsupport then
    throwError "Refusing to shadow existing declaration Diffeomorph.addLipschitzIsotopy_eq_self_of_notMem_tsupport"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.addLipschitzIsotopy_eq_self_of_notMem_tsupport ``Submission.Diffeomorph.addLipschitzIsotopy_eq_self_of_notMem_tsupport

open _root_.Diffeomorph in
theorem exists_isCompact_eqOn_addLipschitzIsotopy (hf : ContDiff ℝ ∞ f)
    (hlip : LipschitzWith C f) (hC : C < 1) (hs : HasCompactSupport f) :
    ∃ K : Set E, IsCompact K ∧ ∀ t : ℝ,
      Set.EqOn (addLipschitzIsotopy hf hlip hC t) id Kᶜ ∧
      Set.EqOn (addLipschitzIsotopy hf hlip hC t).symm id Kᶜ := by
  refine ⟨tsupport f, hs, fun t => ⟨?_, ?_⟩⟩
  · intro x hx
    exact (addLipschitzIsotopy_eq_self_of_notMem_tsupport hf hlip hC t hx).1
  · intro x hx
    exact (addLipschitzIsotopy_eq_self_of_notMem_tsupport hf hlip hC t hx).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.exists_isCompact_eqOn_addLipschitzIsotopy then
    throwError "Refusing to shadow existing declaration Diffeomorph.exists_isCompact_eqOn_addLipschitzIsotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.exists_isCompact_eqOn_addLipschitzIsotopy ``Submission.Diffeomorph.exists_isCompact_eqOn_addLipschitzIsotopy

end Isotopy

end Diffeomorph
