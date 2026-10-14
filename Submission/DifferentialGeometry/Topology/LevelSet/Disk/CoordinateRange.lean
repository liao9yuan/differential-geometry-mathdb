import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis

variable {d : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem mapsTo_Ioo_of_noncritical_coordinate_boundary
    {R : ℝ} {v : V → ℝ} (hc : ContinuousOn v (Metric.closedBall (0 : V) R)) (j : Fin d)
    (hbd : ∀ x ∈ Metric.sphere (0 : V) R, v x = x j)
    (hn : ∀ x ∈ Metric.ball (0 : V) R, fderiv ℝ v x ≠ 0) :
    MapsTo v (Metric.ball (0 : V) R) (_root_.Set.Ioo (-R) R) := by
  have hupper {f : V → ℝ} (hfc : ContinuousOn f (Metric.closedBall (0 : V) R))
      (hfb : ∀ x ∈ Metric.sphere (0 : V) R, f x ≤ R)
      (hfn : ∀ x ∈ Metric.ball (0 : V) R, fderiv ℝ f x ≠ 0) :
      ∀ x ∈ Metric.ball (0 : V) R, f x < R := by
    intro x hx
    obtain ⟨y, hy, hm⟩ := (_root_.ProperSpace.isCompact_closedBall (0 : V) R).exists_isMaxOn
      ⟨x, Metric.ball_subset_closedBall hx⟩ hfc
    have hyn : y ∉ Metric.ball (0 : V) R := by
      intro hyb
      apply hfn y hyb
      exact (hm.isLocalMax (_root_.Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hyb)
        Metric.ball_subset_closedBall)).fderiv_eq_zero
    have hys : y ∈ Metric.sphere (0 : V) R := by
      rw [Metric.mem_sphere]
      exact le_antisymm hy (not_lt.mp hyn)
    have hle : f x ≤ R := (hm (Metric.ball_subset_closedBall hx)).trans (hfb y hys)
    apply lt_of_le_of_ne hle
    intro heq
    apply hfn x hx
    have hlocal : IsLocalMax f x := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
      have hmax := (hm (Metric.ball_subset_closedBall hz)).trans (hfb y hys)
      rwa [← heq] at hmax
    exact hlocal.fderiv_eq_zero
  have hu := hupper hc (fun x hx => by
    rw [hbd x hx]
    have he : ‖x‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
    exact (le_abs_self _).trans ((PiLp.norm_apply_le x j).trans_eq he)) hn
  have hl := hupper hc.neg (fun x hx => by
    change -v x ≤ R
    rw [hbd x hx]
    have he : ‖x‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
    exact (neg_le_abs _).trans ((PiLp.norm_apply_le x j).trans_eq he))
    (fun x hx => by rw [fderiv_neg]; exact neg_ne_zero.mpr (hn x hx))
  exact fun x hx => ⟨by have hh := hl x hx; change -v x < R at hh; linarith, hu x hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.mapsTo_Ioo_of_noncritical_coordinate_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.mapsTo_Ioo_of_noncritical_coordinate_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.mapsTo_Ioo_of_noncritical_coordinate_boundary ``Submission.DifferentialGeometry.Analysis.mapsTo_Ioo_of_noncritical_coordinate_boundary

end DifferentialGeometry.Analysis

end

end
