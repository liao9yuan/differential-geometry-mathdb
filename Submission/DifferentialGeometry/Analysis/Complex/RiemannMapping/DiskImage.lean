import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Calculus.ContDiff.RCLike

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Metric _root_.Filter
open scoped _root_.Topology _root_.ContDiff

namespace Complex
open _root_.Complex

open _root_.Complex in
private theorem closed_unit_disk_subset_source
    (e : OpenPartialHomeomorph ℂ ℂ) {r : ℝ} (hr : 1 < r)
    (hsource : e.source = _root_.Metric.ball (0 : ℂ) r) :
    closedBall (0 : ℂ) 1 ⊆ e.source := by
  rw [hsource]
  exact _root_.Metric.closedBall_subset_ball hr

run_cmd do
  let target := ``Submission.Complex.closed_unit_disk_subset_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Complex.closed_unit_disk_subset_source target :: scope.openDecls } }

open _root_.Complex in
theorem buffered_disk_image_geometry
    (e : OpenPartialHomeomorph ℂ ℂ) {r : ℝ} (hr : 1 < r)
    (hsource : e.source = _root_.Metric.ball (0 : ℂ) r) :
    IsOpen (e '' _root_.Metric.ball (0 : ℂ) 1) ∧
      IsCompact (e '' _root_.Metric.closedBall (0 : ℂ) 1) ∧
      closure (e '' _root_.Metric.ball (0 : ℂ) 1) = e '' _root_.Metric.closedBall (0 : ℂ) 1 ∧
      frontier (e '' _root_.Metric.ball (0 : ℂ) 1) = e '' _root_.Metric.sphere (0 : ℂ) 1 ∧
      e '' _root_.Metric.closedBall (0 : ℂ) 1 ⊆ e.target ∧
      e '' _root_.Metric.sphere (0 : ℂ) 1 ⊆ e.target ∧
      Bornology.IsBounded (e '' _root_.Metric.ball (0 : ℂ) 1) := by
  have hclosed := closed_unit_disk_subset_source e hr hsource
  have hball : _root_.Metric.ball (0 : ℂ) 1 ⊆ e.source := ball_subset_closedBall.trans hclosed
  have hsphere : _root_.Metric.sphere (0 : ℂ) 1 ⊆ e.source := sphere_subset_closedBall.trans hclosed
  have hcompact : IsCompact (e '' _root_.Metric.closedBall (0 : ℂ) 1) :=
    (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn (e.continuousOn.mono hclosed)
  have htarget : e '' _root_.Metric.closedBall (0 : ℂ) 1 ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hclosed hx)
  have hclsub : closure (e '' _root_.Metric.ball (0 : ℂ) 1) ⊆ e '' _root_.Metric.closedBall (0 : ℂ) 1 :=
    closure_minimal (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall) hcompact.isClosed
  have himage : e.IsImage (_root_.Metric.ball (0 : ℂ) 1) (e '' _root_.Metric.ball (0 : ℂ) 1) := by
    intro x hx
    constructor
    · rintro ⟨y, hy, heq⟩
      have hyx := e.injOn (hball hy) hx heq
      simpa only [hyx] using hy
    · intro h
      exact _root_.Set.mem_image_of_mem e h
  have hclosure : closure (e '' _root_.Metric.ball (0 : ℂ) 1) = e '' _root_.Metric.closedBall (0 : ℂ) 1 := by
    have h := himage.closure.image_eq
    rw [closure_ball (0 : ℂ) one_ne_zero,
      inter_eq_right.mpr hclosed, inter_eq_right.mpr (hclsub.trans htarget)] at h
    exact h.symm
  have hfrontier : frontier (e '' _root_.Metric.ball (0 : ℂ) 1) = e '' _root_.Metric.sphere (0 : ℂ) 1 := by
    have h := himage.frontier.image_eq
    have hfsub : frontier (e '' _root_.Metric.ball (0 : ℂ) 1) ⊆ e.target :=
      frontier_subset_closure.trans (hclsub.trans htarget)
    rw [frontier_ball (0 : ℂ) one_ne_zero, inter_eq_right.mpr hsphere,
      inter_eq_right.mpr hfsub] at h
    exact h.symm
  refine ⟨e.isOpen_image_of_subset_source _root_.Metric.isOpen_ball hball, hcompact, hclosure,
    hfrontier, htarget, ?_, ?_⟩
  · exact (_root_.Set.image_mono _root_.Metric.sphere_subset_closedBall).trans htarget
  · exact hcompact.isBounded.subset (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.buffered_disk_image_geometry then
    throwError "Refusing to shadow existing declaration Complex.buffered_disk_image_geometry"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.buffered_disk_image_geometry ``Submission.Complex.buffered_disk_image_geometry

open _root_.Complex in
theorem buffered_disk_image_defining_function
    (e : OpenPartialHomeomorph ℂ ℂ) {r : ℝ} (hr : 1 < r)
    (hsource : e.source = _root_.Metric.ball (0 : ℂ) r)
    (he : ContDiffOn ℝ ∞ e e.source) (hinv : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (fun y => ‖e.symm y‖ ^ 2 - 1) e.target ∧
      (∀ y ∈ closure (e '' _root_.Metric.ball (0 : ℂ) 1), ‖e.symm y‖ ^ 2 - 1 ≤ 0) ∧
      ∀ y ∈ frontier (e '' _root_.Metric.ball (0 : ℂ) 1),
        ‖e.symm y‖ ^ 2 - 1 = 0 ∧
          fderiv ℝ (fun z => ‖e.symm z‖ ^ 2 - 1) y ≠ 0 := by
  let g : ℂ → ℝ := fun y => ‖e.symm y‖ ^ 2 - 1
  have hgs : ContDiffOn ℝ ∞ g e.target :=
    (ContDiffOn.norm_sq (𝕜 := ℝ) hinv).sub contDiffOn_const
  have hclosed := closed_unit_disk_subset_source e hr hsource
  obtain ⟨_, _, hclosure, hfrontier, _, _, _⟩ := buffered_disk_image_geometry e hr hsource
  refine ⟨hgs, ?_, ?_⟩
  · intro y hy
    rw [hclosure] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [e.left_inv (hclosed hx)]
    have hxnorm : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    nlinarith [norm_nonneg x]
  · intro y hy
    rw [hfrontier] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxs : x ∈ e.source := hclosed (_root_.Metric.sphere_subset_closedBall hx)
    have hxnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    constructor
    · rw [e.left_inv hxs, hxnorm]
      norm_num
    · intro hzero
      have hdg : DifferentiableAt ℝ g (e x) :=
        (hgs.contDiffAt (e.open_target.mem_nhds (e.map_source hxs))).differentiableAt (by simp)
      have hde : DifferentiableAt ℝ e x :=
        (he.contDiffAt (e.open_source.mem_nhds hxs)).differentiableAt (by simp)
      have hgerm : g ∘ e =ᶠ[𝓝 x] (fun z : ℂ => ‖z‖ ^ 2 - 1) := by
        filter_upwards [e.open_source.mem_nhds hxs] with z hz
        simp only [Function.comp_apply, g, e.left_inv hz]
      have hchain := fderiv_comp x hdg hde
      change fderiv ℝ (g ∘ e) x = _ at hchain
      have hrad : HasFDerivAt (fun z : ℂ => ‖z‖ ^ 2 - 1) ((2 : ℕ) • innerSL ℝ x) x :=
        (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const 1
      rw [hgerm.fderiv_eq, hrad.fderiv] at hchain
      change fderiv ℝ g (e x) = 0 at hzero
      rw [hzero, ContinuousLinearMap.zero_comp] at hchain
      have hv := congrArg (fun L : ℂ →L[ℝ] ℝ => L x) hchain
      simp only [two_smul, _root_.add_apply, _root_.zero_apply] at hv
      change _root_.Inner.inner ℝ x x + _root_.Inner.inner ℝ x x = 0 at hv
      rw [real_inner_self_eq_norm_sq, hxnorm] at hv
      norm_num at hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.buffered_disk_image_defining_function then
    throwError "Refusing to shadow existing declaration Complex.buffered_disk_image_defining_function"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.buffered_disk_image_defining_function ``Submission.Complex.buffered_disk_image_defining_function

end Complex

end

end

section

noncomputable section

open _root_.Set _root_.Metric _root_.Filter
open scoped _root_.Topology _root_.ContDiff _root_.NNReal

namespace Complex
open _root_.Complex

open _root_.Complex in
theorem interior_closure_buffered_disk_image
    (e : OpenPartialHomeomorph ℂ ℂ) {r : ℝ} (hr : 1 < r)
    (hsource : e.source = _root_.Metric.ball (0 : ℂ) r) :
    interior (closure (e '' _root_.Metric.ball (0 : ℂ) 1)) = e '' _root_.Metric.ball (0 : ℂ) 1 := by
  obtain ⟨_, _, hclosure, _, hKtarget, _, _⟩ := buffered_disk_image_geometry e hr hsource
  have hclosed : _root_.Metric.closedBall (0 : ℂ) 1 ⊆ e.source := by
    rw [hsource]
    exact _root_.Metric.closedBall_subset_ball hr
  have hball : _root_.Metric.ball (0 : ℂ) 1 ⊆ e.source := ball_subset_closedBall.trans hclosed
  have htarget : e '' _root_.Metric.ball (0 : ℂ) 1 ⊆ e.target :=
    (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall).trans hKtarget
  have himage : e.IsImage (_root_.Metric.ball (0 : ℂ) 1) (e '' _root_.Metric.ball (0 : ℂ) 1) := by
    apply OpenPartialHomeomorph.IsImage.of_image_eq
    rw [inter_eq_right.mpr hball, inter_eq_right.mpr htarget]
  have hi : interior (closure (e '' _root_.Metric.ball (0 : ℂ) 1)) ⊆ e.target := by
    apply interior_subset.trans
    rw [hclosure]
    exact hKtarget
  have h := himage.closure.interior.image_eq
  rw [closure_ball (0 : ℂ) one_ne_zero, interior_closedBall (0 : ℂ) one_ne_zero,
    inter_eq_right.mpr hball, inter_eq_right.mpr hi] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.interior_closure_buffered_disk_image then
    throwError "Refusing to shadow existing declaration Complex.interior_closure_buffered_disk_image"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.interior_closure_buffered_disk_image ``Submission.Complex.interior_closure_buffered_disk_image

open _root_.Complex in
theorem exists_exterior_point_near_frontier_buffered_disk_image
    (e : OpenPartialHomeomorph ℂ ℂ) {r : ℝ} (hr : 1 < r)
    (hsource : e.source = _root_.Metric.ball (0 : ℂ) r)
    {p : ℂ} (hp : p ∈ frontier (e '' _root_.Metric.ball (0 : ℂ) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ _root_.Metric.ball p ε, z ∉ closure (e '' _root_.Metric.ball (0 : ℂ) 1) := by
  have hU := (buffered_disk_image_geometry e hr hsource).1
  have hpout : p ∉ e '' _root_.Metric.ball (0 : ℂ) 1 := by
    rw [hU.frontier_eq] at hp
    exact hp.2
  have hpext : p ∈ closure (closure (e '' _root_.Metric.ball (0 : ℂ) 1))ᶜ := by
    rw [closure_compl, interior_closure_buffered_disk_image e hr hsource]
    exact hpout
  obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.mp hpext ε hε
  exact ⟨z, by simpa only [_root_.Metric.mem_ball, dist_comm] using hdist, hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.exists_exterior_point_near_frontier_buffered_disk_image then
    throwError "Refusing to shadow existing declaration Complex.exists_exterior_point_near_frontier_buffered_disk_image"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.exists_exterior_point_near_frontier_buffered_disk_image ``Submission.Complex.exists_exterior_point_near_frontier_buffered_disk_image

open _root_.Complex in
theorem exists_lipschitzOnWith_inverse_ball_of_contDiffOn
    (e : OpenPartialHomeomorph ℂ ℂ) (hinv : ContDiffOn ℝ 1 e.symm e.target)
    {p : ℂ} (hp : p ∈ e.target) :
    ∃ ε : ℝ, 0 < ε ∧ _root_.Metric.ball p ε ⊆ e.target ∧
      ∃ C : ℝ≥0, LipschitzOnWith C e.symm (_root_.Metric.ball p ε) := by
  obtain ⟨C, s, hs, hLip⟩ :=
    (hinv.contDiffAt (e.open_target.mem_nhds hp)).exists_lipschitzOnWith
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (_root_.Filter.inter_mem hs (e.open_target.mem_nhds hp))
  exact ⟨ε, hε, hsub.trans _root_.Set.inter_subset_right, C, hLip.mono (hsub.trans _root_.Set.inter_subset_left)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.exists_lipschitzOnWith_inverse_ball_of_contDiffOn then
    throwError "Refusing to shadow existing declaration Complex.exists_lipschitzOnWith_inverse_ball_of_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.exists_lipschitzOnWith_inverse_ball_of_contDiffOn ``Submission.Complex.exists_lipschitzOnWith_inverse_ball_of_contDiffOn

end Complex

end

end
