import Submission.DifferentialGeometry.Analysis.Complex.RiemannMapping.BoundaryHomeomorphism
import Submission.DifferentialGeometry.Analysis.Complex.SmoothImageCircle
import Submission.DifferentialGeometry.Analysis.Complex.HolomorphicBoundaryRegularity
import Mathlib.Analysis.Calculus.ContDiff.RCLike

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Metric
open _root_.Submission.DifferentialGeometry.Geometry
open scoped _root_.ContDiff _root_.NNReal

namespace Complex
open _root_.Complex

open _root_.Complex in
theorem exists_bilipschitz_riemann_map_comp_extension_of_buffered_disk
    (W f : OpenPartialHomeomorph ℂ ℂ) {r : ℝ} (hr : 1 < r)
    (hWsource : W.source = _root_.Metric.ball (0 : ℂ) r)
    (hW : ContDiffOn ℝ ∞ W W.source) (hWi : ContDiffOn ℝ ∞ W.symm W.target)
    (hfsource : f.source = W '' _root_.Metric.ball (0 : ℂ) 1)
    (hftarget : f.target = _root_.Metric.ball (0 : ℂ) 1)
    (hf : DifferentiableOn ℂ f f.source) :
    ∃ (C D : ℝ≥0) (H : _root_.Metric.closedBall (0 : ℂ) 1 ≃ₜ _root_.Metric.closedBall (0 : ℂ) 1),
      LipschitzWith C H ∧ LipschitzWith D H.symm ∧
      ContDiffOn ℝ ∞ (fun z => (H.symm (diskRetraction z) : ℂ)) (_root_.Metric.closedBall (0 : ℂ) 1) ∧
      (∀ z (hz : z ∈ _root_.Metric.ball (0 : ℂ) 1),
        (H ⟨z, _root_.Metric.ball_subset_closedBall hz⟩ : ℂ) = f (W z)) ∧
      (∀ z (hz : z ∈ _root_.Metric.ball (0 : ℂ) 1),
        (H.symm ⟨z, _root_.Metric.ball_subset_closedBall hz⟩ : ℂ) = W.symm (f.symm z)) := by
  obtain ⟨C, H, hHLip, hH, hHi⟩ :=
    exists_lipschitz_homeomorph_riemann_map_comp_of_buffered_disk
      W f hr hWsource hW hWi hfsource hftarget hf
  have hclosed : _root_.Metric.closedBall (0 : ℂ) 1 ⊆ W.source := by
    rw [hWsource]
    exact _root_.Metric.closedBall_subset_ball hr
  let v : ℂ → ℂ := fun z => (H.symm (diskRetraction z) : ℂ)
  let U : ℂ → ℂ := W ∘ v
  have hvc : Continuous v := continuous_subtype_val.comp
    (H.symm.continuous.comp diskRetraction_lipschitz.continuous)
  have hvsource (z : ℂ) : v z ∈ W.source := hclosed (H.symm (diskRetraction z)).property
  have hUc : Continuous U := W.continuousOn.comp_continuous hvc hvsource
  have hUeq (z : ℂ) (hz : z ∈ _root_.Metric.ball (0 : ℂ) 1) : U z = f.symm z := by
    change W (H.symm (diskRetraction z)) = f.symm z
    rw [diskRetraction_coe ⟨z, _root_.Metric.ball_subset_closedBall hz⟩, hHi z hz]
    apply W.right_inv
    obtain ⟨x, hx, hxf⟩ := hfsource ▸ f.map_target (hftarget ▸ hz)
    rw [← hxf]
    exact W.map_source (hclosed (_root_.Metric.ball_subset_closedBall hx))
  have hUi : DifferentiableOn ℂ U (_root_.Metric.ball (0 : ℂ) 1) := by
    have hi := differentiableOn_symm_of_differentiableOn f hf
    rw [hftarget] at hi
    exact hi.congr hUeq
  obtain ⟨γ, hγ, hγs, hγd, hγrange⟩ := exists_regular_parametrization_image_circle
    W (sphere_subset_closedBall.trans hclosed) hW (hWi.differentiableOn (by simp))
  have htrace (z : ℂ) (hz : ‖z‖ = 1) : U z ∈ _root_.Set.range γ := by
    rw [hγrange]
    refine ⟨v z, ?_, rfl⟩
    apply mem_sphere_zero_iff_norm.mpr
    apply le_antisymm (mem_closedBall_zero_iff.mp (H.symm (diskRetraction z)).property)
    by_contra! hlt
    have hvi : v z ∈ _root_.Metric.ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hlt
    have hh : (H (H.symm (diskRetraction z)) : ℂ) ∈ _root_.Metric.ball (0 : ℂ) 1 := by
      rw [hH _ hvi]
      exact hftarget ▸ f.map_source (hfsource ▸ _root_.Set.mem_image_of_mem W hvi)
    have hzcl : z ∈ _root_.Metric.closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr hz.le
    rw [H.apply_symm_apply, diskRetraction_coe ⟨z, hzcl⟩] at hh
    exact (ne_of_lt (mem_ball_zero_iff.mp hh)) hz
  have hUs : ContDiffOn ℝ ∞ U (_root_.Metric.closedBall (0 : ℂ) 1) :=
    contDiffOn_closedDisk_of_differentiableOn_of_embedded_loop
      Real.two_pi_pos hγ hγs hγd hUc.continuousOn hUi htrace
  have hvs : ContDiffOn ℝ ∞ v (_root_.Metric.closedBall (0 : ℂ) 1) :=
    (hWi.comp hUs (fun z _ => W.map_source (hvsource z))).congr
      (fun z _ => (W.left_inv (hvsource z)).symm)
  obtain ⟨D, hD⟩ := hvs.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : ℂ) 1) (_root_.ProperSpace.isCompact_closedBall (0 : ℂ) 1)
  have hDLip : LipschitzWith D H.symm := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change _root_.Dist.dist (H.symm x : ℂ) (H.symm y : ℂ) ≤ (D : ℝ) * _root_.Dist.dist (x : ℂ) (y : ℂ)
    simpa only [v, diskRetraction_coe] using hD.dist_le_mul x x.2 y y.2
  exact ⟨C, D, H, hHLip, hDLip, hvs, hH, hHi⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.exists_bilipschitz_riemann_map_comp_extension_of_buffered_disk then
    throwError "Refusing to shadow existing declaration Complex.exists_bilipschitz_riemann_map_comp_extension_of_buffered_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.exists_bilipschitz_riemann_map_comp_extension_of_buffered_disk ``Submission.Complex.exists_bilipschitz_riemann_map_comp_extension_of_buffered_disk

end Complex

end

end
