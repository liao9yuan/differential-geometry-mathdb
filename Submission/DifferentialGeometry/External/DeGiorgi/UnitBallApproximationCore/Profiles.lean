-- Modified 2026-04-28: updated internal import paths for project namespace
-- Modified 2026-05-16: style-warning cleanup
import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Chapter 02: Unit-Ball Approximation Profiles

This module contains the smooth cutoff profiles and the basic compact-support
approximation tool used in the unit-ball argument.
-/

noncomputable section

open _root_.MeasureTheory _root_.Topology _root_.Set _root_.Function
open scoped _root_.ENNReal _root_.NNReal

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

open _root_.Real in
private lemma smoothTransition_differentiable' :
    Differentiable ℝ smoothTransition :=
  smoothTransition.contDiff.differentiable_one

run_cmd do
  let target := ``Submission.DeGiorgi.smoothTransition_differentiable'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.smoothTransition_differentiable' target :: scope.openDecls } }

open _root_.Real in
private lemma smoothTransition_deriv_continuous' :
    Continuous (deriv _root_.Real.smoothTransition) := by
  exact smoothTransition.contDiff.continuous_deriv_one

run_cmd do
  let target := ``Submission.DeGiorgi.smoothTransition_deriv_continuous'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.smoothTransition_deriv_continuous' target :: scope.openDecls } }

open _root_.Real in
private lemma st_deriv_zero_neg {x : ℝ} (hx : x < 0) :
    deriv _root_.Real.smoothTransition x = 0 := by
  have h : _root_.Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact smoothTransition.zero_of_nonpos hy.le
  exact h.deriv_eq.trans (deriv_const x (0 : ℝ))

run_cmd do
  let target := ``Submission.DeGiorgi.st_deriv_zero_neg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.st_deriv_zero_neg target :: scope.openDecls } }

open _root_.Real in
private lemma st_deriv_zero_gt {x : ℝ} (hx : 1 < x) :
    deriv _root_.Real.smoothTransition x = 0 := by
  have h : _root_.Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact smoothTransition.one_of_one_le hy.le
  exact h.deriv_eq.trans (deriv_const x (1 : ℝ))

run_cmd do
  let target := ``Submission.DeGiorgi.st_deriv_zero_gt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.st_deriv_zero_gt target :: scope.openDecls } }

open _root_.Real in
private lemma smoothTransition_nnnorm_deriv_bounded :
    ∃ C : ℝ≥0, ∀ x : ℝ, ‖deriv _root_.Real.smoothTransition x‖₊ ≤ C := by
  have h1 : ContDiff ℝ 1 smoothTransition := smoothTransition.contDiff
  have h_cont : Continuous (deriv _root_.Real.smoothTransition) := h1.continuous_deriv_one
  obtain ⟨M, -, hM_max⟩ := (_root_.CompactIccSpace.isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
    (nonempty_Icc.2 zero_le_one) h_cont.norm.continuousOn
  have hbound : ∀ x : ℝ, ‖deriv _root_.Real.smoothTransition x‖ ≤ ‖deriv _root_.Real.smoothTransition M‖ := by
    intro x
    by_cases hx0 : x < 0
    · rw [st_deriv_zero_neg hx0, norm_zero]
      exact norm_nonneg _
    · by_cases hx1 : 1 < x
      · rw [st_deriv_zero_gt hx1, norm_zero]
        exact norm_nonneg _
      · push Not at hx0 hx1
        exact Filter.eventually_principal.mp hM_max x (Set.mem_Icc.2 ⟨hx0, hx1⟩)
  refine ⟨‖deriv _root_.Real.smoothTransition M‖₊, fun x => ?_⟩
  exact NNReal.coe_le_coe.mp (by simpa using hbound x)

run_cmd do
  let target := ``Submission.DeGiorgi.smoothTransition_nnnorm_deriv_bounded
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.smoothTransition_nnnorm_deriv_bounded target :: scope.openDecls } }

/-- Universal derivative bound for smooth cutoff profiles. -/
noncomputable def Mst : ℝ≥0 := smoothTransition_nnnorm_deriv_bounded.choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.Mst then
    throwError "Refusing to shadow existing declaration DeGiorgi.Mst"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.Mst ``Submission.DeGiorgi.Mst

open _root_.Real in
lemma smoothTransition_nnnorm_deriv_le :
    ∀ x : ℝ, ‖deriv _root_.Real.smoothTransition x‖₊ ≤ Mst :=
  smoothTransition_nnnorm_deriv_bounded.choose_spec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.smoothTransition_nnnorm_deriv_le then
    throwError "Refusing to shadow existing declaration DeGiorgi.smoothTransition_nnnorm_deriv_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.smoothTransition_nnnorm_deriv_le ``Submission.DeGiorgi.smoothTransition_nnnorm_deriv_le

open _root_.Real in
lemma smoothTransition_lipschitz : LipschitzWith Mst Real.smoothTransition :=
  lipschitzWith_of_nnnorm_deriv_le smoothTransition_differentiable'
    smoothTransition_nnnorm_deriv_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.smoothTransition_lipschitz then
    throwError "Refusing to shadow existing declaration DeGiorgi.smoothTransition_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.smoothTransition_lipschitz ``Submission.DeGiorgi.smoothTransition_lipschitz

def myCutoff (x₀ : E) (r R : ℝ) (x : E) : ℝ :=
  Real.smoothTransition ((R - ‖x - x₀‖) / (R - r))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.myCutoff then
    throwError "Refusing to shadow existing declaration DeGiorgi.myCutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.myCutoff ``Submission.DeGiorgi.myCutoff

omit [NeZero d] in
lemma myCutoff_nonneg (x₀ : E) (r R : ℝ) (x : E) : 0 ≤ myCutoff x₀ r R x :=
  Real.smoothTransition.nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.myCutoff_nonneg then
    throwError "Refusing to shadow existing declaration DeGiorgi.myCutoff_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.myCutoff_nonneg ``Submission.DeGiorgi.myCutoff_nonneg

omit [NeZero d] in
lemma myCutoff_le_one (x₀ : E) (r R : ℝ) (x : E) : myCutoff x₀ r R x ≤ 1 :=
  Real.smoothTransition.le_one _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.myCutoff_le_one then
    throwError "Refusing to shadow existing declaration DeGiorgi.myCutoff_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.myCutoff_le_one ``Submission.DeGiorgi.myCutoff_le_one

omit [NeZero d] in
lemma myCutoff_eq_one {x₀ : E} {r R : ℝ} (hrR : r < R) {x : E}
    (hx : x ∈ Metric.ball x₀ r) : myCutoff x₀ r R x = 1 := by
  unfold myCutoff
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (sub_pos.2 hrR)]
  have : ‖x - x₀‖ < r := by rwa [← dist_eq_norm, ← Metric.mem_ball]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.myCutoff_eq_one then
    throwError "Refusing to shadow existing declaration DeGiorgi.myCutoff_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.myCutoff_eq_one ``Submission.DeGiorgi.myCutoff_eq_one

omit [NeZero d] in
lemma myCutoff_eq_zero {x₀ : E} {r R : ℝ} (hrR : r < R) {x : E}
    (hx : x ∉ Metric.closedBall x₀ R) : myCutoff x₀ r R x = 0 := by
  unfold myCutoff
  apply Real.smoothTransition.zero_of_nonpos
  have hx' : R < _root_.Dist.dist x x₀ := by
    rw [Metric.mem_closedBall, not_le] at hx
    exact hx
  have hx'' : R < ‖x - x₀‖ := by
    simpa [dist_eq_norm] using hx'
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.myCutoff_eq_zero then
    throwError "Refusing to shadow existing declaration DeGiorgi.myCutoff_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.myCutoff_eq_zero ``Submission.DeGiorgi.myCutoff_eq_zero

omit [NeZero d] in
lemma myCutoff_support_subset (x₀ : E) {r R : ℝ} (hrR : r < R) :
    tsupport (myCutoff x₀ r R) ⊆ Metric.closedBall x₀ R := by
  apply closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
  contrapose! hx
  simp only [_root_.Function.mem_support, ne_eq, _root_.Classical.not_not]
  exact myCutoff_eq_zero hrR hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.myCutoff_support_subset then
    throwError "Refusing to shadow existing declaration DeGiorgi.myCutoff_support_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.myCutoff_support_subset ``Submission.DeGiorgi.myCutoff_support_subset

omit [NeZero d] in
lemma myCutoff_contDiff {x₀ : E} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ContDiff ℝ (⊤ : ℕ∞) (myCutoff x₀ r R) := by
  have hRr : (0 : ℝ) < R - r := sub_pos.2 hrR
  rw [contDiff_iff_contDiffAt]
  intro x
  unfold myCutoff
  rcases eq_or_ne (x - x₀) 0 with hx | hx
  · have hxx : x = x₀ := sub_eq_zero.mp hx
    subst x
    have harg : ContinuousAt (fun y : E => (R - ‖y - x₀‖) / (R - r)) x₀ := by
      apply ContinuousAt.div
      · exact continuousAt_const.sub (continuous_norm.continuousAt.comp
          (continuousAt_id.sub continuousAt_const))
      · exact continuousAt_const
      · exact hRr.ne'
    have hgt : 1 < (fun y : E => (R - ‖y - x₀‖) / (R - r)) x₀ := by
      simp only [sub_self, norm_zero, sub_zero]
      rw [one_lt_div hRr]
      linarith
    have hge1 : ∀ᶠ y in 𝓝 x₀, 1 ≤ (R - ‖y - x₀‖) / (R - r) :=
      harg.eventually (Ioi_mem_nhds hgt) |>.mono fun y hy => le_of_lt hy
    have hconst : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : E => (1 : ℝ)) x₀ := contDiffAt_const
    exact hconst.congr_of_eventuallyEq
      (hge1.mono fun y hy => Real.smoothTransition.one_of_one_le hy)
  · have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E => ‖y - x₀‖) x :=
      (contDiffAt_norm ℝ hx).comp x (contDiffAt_id.sub contDiffAt_const)
    have harg : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E => (R - ‖y - x₀‖) / (R - r)) x := by
      exact ((contDiffAt_const.sub hnorm).div contDiffAt_const hRr.ne').congr_of_eventuallyEq <|
        Filter.Eventually.of_forall fun _ => rfl
    have hsmooth : ContDiffAt ℝ (⊤ : ℕ∞) Real.smoothTransition
        ((R - ‖x - x₀‖) / (R - r)) := Real.smoothTransition.contDiffAt
    exact ContDiffAt.comp
      (f := fun y : E => (R - ‖y - x₀‖) / (R - r))
      (g := Real.smoothTransition) x hsmooth harg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.myCutoff_contDiff then
    throwError "Refusing to shadow existing declaration DeGiorgi.myCutoff_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.myCutoff_contDiff ``Submission.DeGiorgi.myCutoff_contDiff

omit [NeZero d] in
private lemma radial_lipschitz (x₀ : E) {r R : ℝ} (hrR : r < R) :
    LipschitzWith ⟨(R - r)⁻¹, inv_nonneg.mpr (sub_pos.2 hrR).le⟩
      (fun x : E => (R - ‖x - x₀‖) / (R - r)) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simp only [dist_eq_norm, Real.norm_eq_abs]
    have hpos : (0 : ℝ) < R - r := sub_pos.2 hrR
    have key : abs (‖y - x₀‖ - ‖x - x₀‖) ≤ ‖x - y‖ := calc
      abs (‖y - x₀‖ - ‖x - x₀‖) ≤ ‖(y - x₀) - (x - x₀)‖ := by
        exact abs_norm_sub_norm_le (y - x₀) (x - x₀)
      _ = ‖y - x‖ := by congr 1; abel
      _ = ‖x - y‖ := by exact norm_sub_rev y x
    have hsub : (R - ‖x - x₀‖) / (R - r) - (R - ‖y - x₀‖) / (R - r) =
        (‖y - x₀‖ - ‖x - x₀‖) / (R - r) := by ring
    rw [hsub, abs_div, abs_of_pos hpos]
    change |‖y - x₀‖ - ‖x - x₀‖| / (R - r) ≤ (R - r)⁻¹ * ‖x - y‖
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_right key hpos.le

run_cmd do
  let target := ``Submission.DeGiorgi.radial_lipschitz
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.radial_lipschitz target :: scope.openDecls } }

omit [NeZero d] in
lemma myCutoff_lipschitz (x₀ : E) {r R : ℝ} (hrR : r < R) :
    LipschitzWith (Mst * ⟨(R - r)⁻¹, inv_nonneg.mpr (sub_pos.2 hrR).le⟩)
      (myCutoff x₀ r R) :=
  smoothTransition_lipschitz.comp (radial_lipschitz x₀ hrR)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.myCutoff_lipschitz then
    throwError "Refusing to shadow existing declaration DeGiorgi.myCutoff_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.myCutoff_lipschitz ``Submission.DeGiorgi.myCutoff_lipschitz

omit [NeZero d] in
lemma myCutoff_fderiv_bound (x₀ : E) {r R : ℝ} (hrR : r < R) (x : E) :
    ‖fderiv ℝ (myCutoff x₀ r R) x‖ ≤ ↑Mst * (R - r)⁻¹ := by
  have h : ‖fderiv ℝ (myCutoff x₀ r R) x‖ ≤
      ↑(Mst * ⟨(R - r)⁻¹, inv_nonneg.mpr (sub_nonneg.mpr hrR.le)⟩) :=
    norm_fderiv_le_of_lipschitz (𝕜 := ℝ) (x₀ := x) (myCutoff_lipschitz x₀ hrR)
  change ‖fderiv ℝ (myCutoff x₀ r R) x‖ ≤ (Mst : ℝ) * (R - r)⁻¹ at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.myCutoff_fderiv_bound then
    throwError "Refusing to shadow existing declaration DeGiorgi.myCutoff_fderiv_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.myCutoff_fderiv_bound ``Submission.DeGiorgi.myCutoff_fderiv_bound

structure Cutoff (x₀ : E) (r R : ℝ) where
  toFun : E → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  nonneg : ∀ x, 0 ≤ toFun x
  le_one : ∀ x, toFun x ≤ 1
  eq_one : ∀ x ∈ Metric.ball x₀ r, toFun x = 1
  support_subset : tsupport toFun ⊆ Metric.closedBall x₀ R
  grad_bound : ∀ x, ‖fderiv ℝ toFun x‖ ≤ ↑Mst * (R - r)⁻¹

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.Cutoff then
    throwError "Refusing to shadow existing declaration DeGiorgi.Cutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.Cutoff ``Submission.DeGiorgi.Cutoff

omit [NeZero d] in
theorem Cutoff.exists (x₀ : E) {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    ∃ _η : Cutoff x₀ r R, True :=
  ⟨⟨myCutoff x₀ r R,
    by simpa using (myCutoff_contDiff (x₀ := x₀) hr hR),
    myCutoff_nonneg x₀ r R,
    myCutoff_le_one x₀ r R,
    fun x hx => myCutoff_eq_one (x₀ := x₀) hR hx,
    myCutoff_support_subset x₀ hR,
    fun x => myCutoff_fderiv_bound x₀ hR x⟩, trivial⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DeGiorgi.Cutoff
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.Cutoff.exists then
    throwError "Refusing to shadow existing declaration DeGiorgi.Cutoff.exists"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.Cutoff.exists ``Submission.DeGiorgi.Cutoff.exists

omit [NeZero d] in
theorem Lp_approx_by_continuous_compactly_supported
    {f : E → ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hf : _root_.MeasureTheory.MemLp f p _root_.MeasureTheory.MeasureSpace.volume)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ g : E → ℝ, Continuous g ∧ HasCompactSupport g ∧
      eLpNorm (f - g) p _root_.MeasureTheory.MeasureSpace.volume < δ := by
  obtain ⟨ε, hε_pos, hε_lt⟩ : ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε < δ := by
    by_cases hδ_top : δ = ⊤
    · exact ⟨1, one_pos, hδ_top ▸ ENNReal.ofReal_lt_top⟩
    · have hδ_lt_top : δ < ⊤ := lt_top_iff_ne_top.mpr hδ_top
      refine ⟨(δ / 2).toReal,
        ENNReal.toReal_pos (ENNReal.div_pos hδ.ne' (by norm_num)).ne'
          (ENNReal.div_lt_top hδ_lt_top.ne (by norm_num)).ne, ?_⟩
      calc
        ENNReal.ofReal (δ / 2).toReal = δ / 2 :=
          ENNReal.ofReal_toReal (ENNReal.div_lt_top hδ_lt_top.ne (by norm_num)).ne
        _ < δ := ENNReal.half_lt_self hδ.ne' hδ_top
  obtain ⟨g, hg_supp, hg_smooth, hg_norm⟩ := hf.exist_eLpNorm_sub_le hp' hp hε_pos
  exact ⟨g, hg_smooth.continuous, hg_supp, lt_of_le_of_lt hg_norm hε_lt⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.Lp_approx_by_continuous_compactly_supported then
    throwError "Refusing to shadow existing declaration DeGiorgi.Lp_approx_by_continuous_compactly_supported"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.Lp_approx_by_continuous_compactly_supported ``Submission.DeGiorgi.Lp_approx_by_continuous_compactly_supported


end DeGiorgi
