/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.Homeomorph.ClosedPasting
import Submission.DifferentialGeometry.Topology.Homeomorph.JordanDiskMove
import Submission.DifferentialGeometry.Topology.Homeomorph.PlanarExtension
import Submission.DifferentialGeometry.Topology.Homeomorph.PlanarSphereExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric _root_.Submission.Metric _root_.Filter _root_.Topology _root_.Submission.Schoenflies
open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Topology.PlanarJordan

namespace Homeomorph
open _root_.Homeomorph

open _root_.Homeomorph in
private theorem image_closedBall_zero_of_norm
    {E : Type*} [NormedAddCommGroup E] (g : E ≃ₜ E) (hg : ∀ x, ‖g x‖ = ‖x‖) (r : ℝ) :
    g '' _root_.Metric.closedBall 0 r = _root_.Metric.closedBall 0 r := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    simpa only [_root_.Metric.mem_closedBall, dist_zero_right, hg] using hx
  · intro y hy
    refine ⟨g.symm y, ?_, g.apply_symm_apply y⟩
    have h := hg (g.symm y)
    rw [g.apply_symm_apply] at h
    simpa only [_root_.Metric.mem_closedBall, dist_zero_right, ← h] using hy

run_cmd do
  let target := ``Submission.Homeomorph.image_closedBall_zero_of_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.image_closedBall_zero_of_norm target :: scope.openDecls } }

open _root_.Homeomorph in
theorem exists_supported_eqOn_closedBall_or_reflection (f : Plane ≃ₜ Plane) :
    ∃ L : Plane ≃ₗᵢ[ℝ] Plane,
      (L = LinearIsometryEquiv.refl ℝ _ ∨ L = planarReflection) ∧
      ∃ g : Plane ≃ₜ Plane, ∃ R > 0,
        EqOn g (f ∘ L) (_root_.Metric.closedBall 0 1) ∧ _root_.Set.EqOn g id (_root_.Metric.ball 0 R)ᶜ := by
  let K : Set Plane := _root_.Metric.closedBall 0 1
  let J : Set Plane := _root_.Metric.sphere 0 1
  have hK : IsCompact K := _root_.ProperSpace.isCompact_closedBall 0 1
  have hJ : IsJordanCurve J := by
    simpa only [Subtype.range_coe] using isJordanCurve_range_of_isEmbedding_circle
      (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (Subtype.val : J → Plane))
  have hfront : frontier K = J := frontier_closedBall (0 : Plane) one_ne_zero
  have hregion : closure (inside J) = K := by
    rw [← hfront]
    apply closure_inside_frontier_eq_of_isCompact hK (hfront.symm ▸ hJ)
    rw [interior_closedBall (0 : Plane) one_ne_zero]
    exact nonempty_ball.mpr zero_lt_one
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : Plane)).mp
    (hK.union (hK.image f.continuous)).isBounded
  have hRpos : 0 < R := by
    have h := hR (Or.inl (show (0 : Plane) ∈ K by simp [K]))
    simpa using h
  have hKR : K ⊆ _root_.Metric.ball 0 R := fun x hx => hR (Or.inl hx)
  have hfKR : f '' K ⊆ _root_.Metric.ball 0 R := fun x hx => hR (Or.inr hx)
  have hfr : closure (inside (f '' J)) = f '' K := by
    rw [← image_inside, ← f.image_closure, hregion]
  obtain ⟨h, hhK, hhfix⟩ := exists_image_closed_region_eqOn_compl hJ
    (isJordanCurve_image f hJ) _root_.Metric.isOpen_ball (convex_ball (0 : Plane) R).isPreconnected
    (hregion ▸ hKR) (hfr ▸ hfKR)
  rw [hregion, hfr] at hhK
  let q := f.trans h.symm
  have hqK : q '' K = K := by
    change (h.symm ∘ f) '' K = K
    rw [_root_.Set.image_comp, ← hhK]
    exact h.symm_image_image K
  have hqJ : q '' J = J := by
    rw [← hfront, q.image_frontier, hqK]
  let ψ : J ≃ₜ J := (q.image J).trans (Homeomorph.setCongr hqJ)
  obtain ⟨L, hL, a, hanorm, haJ, hafix⟩ := exists_supported_homeomorph_sphere_or_reflection ψ
  let p := L.toHomeomorph.trans q
  have hpK : p '' K = K := by
    change (q ∘ L) '' K = K
    have hLK : L '' K = K := image_closedBall_zero_of_norm L.toHomeomorph L.norm_map 1
    rw [_root_.Set.image_comp, hLK, hqK]
  have haK : a '' K = K := image_closedBall_zero_of_norm a hanorm 1
  have hpa : _root_.Set.EqOn p a (frontier K) := by
    intro x hx
    have hxJ : x ∈ J := hfront ▸ hx
    exact (haJ ⟨x, hxJ⟩).symm
  obtain ⟨b, hbp, hba⟩ := p.exists_pasting_of_image_eq a hK.isClosed (hpK.trans haK.symm) hpa
  have hbfix : _root_.Set.EqOn b id (_root_.Metric.ball 0 2)ᶜ := by
    intro x hx
    have hxK : x ∉ interior K := by
      rw [interior_closedBall (0 : Plane) one_ne_zero]
      exact fun hmem => hx (_root_.Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hmem)
    exact (hba hxK).trans (hafix hx)
  refine ⟨L, hL, b.trans h, _root_.Max.max R 2, hRpos.trans_le (le_max_left _ _), ?_, ?_⟩
  · intro x hx
    change h (b x) = f (L x)
    rw [hbp hx]
    exact h.apply_symm_apply (f (L x))
  · intro x hx
    have hxR : x ∉ _root_.Metric.ball (0 : Plane) R :=
      fun hmem => hx (_root_.Metric.ball_subset_ball (le_max_left _ _) hmem)
    have hx2 : x ∉ _root_.Metric.ball (0 : Plane) 2 :=
      fun hmem => hx (_root_.Metric.ball_subset_ball (le_max_right _ _) hmem)
    change h (b x) = x
    rw [hbfix hx2, id_eq, hhfix hxR]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.exists_supported_eqOn_closedBall_or_reflection then
    throwError "Refusing to shadow existing declaration Homeomorph.exists_supported_eqOn_closedBall_or_reflection"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.exists_supported_eqOn_closedBall_or_reflection ``Submission.Homeomorph.exists_supported_eqOn_closedBall_or_reflection

end Homeomorph

namespace OpenPartialHomeomorph
open _root_.OpenPartialHomeomorph

open _root_.OpenPartialHomeomorph in
theorem exists_supported_eventuallyEq_or_reflection (e : OpenPartialHomeomorph Plane Plane)
    (h0 : (0 : Plane) ∈ e.source) :
    ∃ L : Plane ≃ₗᵢ[ℝ] Plane,
      (L = LinearIsometryEquiv.refl ℝ _ ∨ L = planarReflection) ∧
      ∃ g : Plane ≃ₜ Plane, ∃ R > 0,
        (g : Plane → Plane) =ᶠ[𝓝 0] (e ∘ L) ∧ _root_.Set.EqOn g id (_root_.Metric.ball 0 R)ᶜ := by
  obtain ⟨f, hf, _⟩ := e.exists_homeomorph_eventuallyEq h0
  obtain ⟨L, hL, g, R, hR, hg, hfix⟩ := f.exists_supported_eqOn_closedBall_or_reflection
  have hL0 : _root_.Filter.Tendsto L (𝓝 (0 : Plane)) (𝓝 0) := by
    simpa only [ContinuousAt, map_zero] using L.continuous.continuousAt (x := (0 : Plane))
  refine ⟨L, hL, g, R, hR, ?_, hfix⟩
  filter_upwards [hf.comp_tendsto hL0, _root_.Metric.ball_mem_nhds (0 : Plane) zero_lt_one] with x hx hxb
  exact (hg (_root_.Metric.ball_subset_closedBall hxb)).trans hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.exists_supported_eventuallyEq_or_reflection then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.exists_supported_eventuallyEq_or_reflection"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.exists_supported_eventuallyEq_or_reflection ``Submission.OpenPartialHomeomorph.exists_supported_eventuallyEq_or_reflection

end OpenPartialHomeomorph
