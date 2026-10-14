import Submission.DifferentialGeometry.Analysis.Complex.LogarithmicGradient
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.Shift

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Metric _root_.InnerProductSpace _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis

theorem norm_gradient_le_of_harmonicOnNhd_ball
    {u : ℂ → ℝ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hu : _root_.InnerProductSpace.HarmonicOnNhd u (_root_.Metric.ball c R))
    (hbound : ∀ z ∈ _root_.Metric.ball c R, |u z| ≤ M) :
    ‖gradient u c‖ ≤ 8 * M / R := by
  have hc : c ∈ _root_.Metric.ball c R := _root_.Metric.mem_ball_self hR
  have hM : 0 ≤ M := (abs_nonneg (u c)).trans (hbound c hc)
  rcases eq_or_lt_of_le hM with hMzero | hMpos
  · have hueq : u =ᶠ[𝓝 c] (fun _ => 0) := by
      filter_upwards [_root_.Metric.ball_mem_nhds c hR] with z hz
      have hh : |u z| ≤ 0 := by simpa [← hMzero] using hbound z hz
      exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
    rw [hueq.gradient_eq]
    simp [← hMzero]
  obtain ⟨F, hF, hFu⟩ := hu.exists_analyticOnNhd_ball_re_eq
  let G : ℂ → ℂ := fun z => F (c + z) - F c
  have htranslate (z : ℂ) (hz : z ∈ _root_.Metric.ball 0 R) : c + z ∈ _root_.Metric.ball c R := by
    simpa only [_root_.Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hz
  have hG : DifferentiableOn ℂ G (_root_.Metric.ball 0 R) := by
    intro z hz
    exact (((hF (c + z) (htranslate z hz)).differentiableAt.comp z
      ((differentiableAt_const c).add differentiableAt_id)).sub_const (F c)).differentiableWithinAt
  have hGre : _root_.Set.MapsTo G (_root_.Metric.ball 0 R) {z : ℂ | z.re ≤ 2 * M} := by
    intro z hz
    change (F (c + z)).re - (F c).re ≤ 2 * M
    have hez : (F (c + z)).re = u (c + z) := hFu (htranslate z hz)
    have hec : (F c).re = u c := hFu hc
    rw [hez, hec]
    have h1 := (abs_le.mp (hbound (c + z) (htranslate z hz))).2
    have h2 := (abs_le.mp (hbound c hc)).1
    linarith
  have hG0 : G 0 = 0 := by simp [G]
  have hGcirc (z : ℂ) (hz : z ∈ _root_.Metric.sphere 0 (R / 2)) : ‖G z‖ ≤ 4 * M := by
    have hzn : ‖z‖ = R / 2 := by simpa only [_root_.Metric.mem_sphere, dist_zero_right] using hz
    have hzB : z ∈ _root_.Metric.ball 0 R := by rw [mem_ball_zero_iff, hzn]; linarith
    have hh := Complex.borelCaratheodory_zero (by positivity : 0 < 2 * M)
      hG hGre hR hzB hG0
    rw [hzn] at hh
    have hconst : 2 * (2 * M) * (R / 2) / (R - R / 2) = 4 * M := by
      field_simp [hR.ne']
      ring
    rwa [hconst] at hh
  have hGderiv := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (half_pos hR) (hG.diffContOnCl_ball (_root_.Metric.closedBall_subset_ball (by linarith))) hGcirc
  have hdG : deriv G 0 = deriv F c := by
    dsimp only [G]
    rw [deriv_sub_const, deriv_comp_const_add, add_zero]
  rw [hdG] at hGderiv
  have hgrad : gradient u c = gradient (fun z => (F z).re) c :=
    (hFu.eventuallyEq_of_mem (_root_.Metric.ball_mem_nhds c hR)).gradient_eq.symm
  rw [hgrad, norm_gradient_re_eq_norm_deriv (hF c hc).differentiableAt]
  calc
    _ ≤ 4 * M / (R / 2) := hGderiv
    _ = 8 * M / R := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.norm_gradient_le_of_harmonicOnNhd_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.norm_gradient_le_of_harmonicOnNhd_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.norm_gradient_le_of_harmonicOnNhd_ball ``Submission.DifferentialGeometry.Analysis.norm_gradient_le_of_harmonicOnNhd_ball

end DifferentialGeometry.Analysis

end

end
