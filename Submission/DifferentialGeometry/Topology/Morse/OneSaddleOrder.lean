import Submission.DifferentialGeometry.Topology.Morse.OneSaddleComponents
import Submission.DifferentialGeometry.Topology.Morse.ExtremumChart
import Submission.DifferentialGeometry.Topology.Morse.SphereLevelComponents
import Submission.DifferentialGeometry.Topology.Morse.QuadraticComponent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Metric _root_.Submission.Metric _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold
namespace DifferentialGeometry.Topology.Morse
local notation "S₂" => _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

theorem exists_ordered_criticalPoints_of_one_saddle
    {f : S₂ → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hnd : ∀ x, IsCriticalPointAt (𝓡 2) f x → IsNondegenerateCriticalPointAt (𝓡 2) f x)
    (hinj : _root_.Set.InjOn f {x | IsCriticalPointAt (𝓡 2) f x})
    (hone : {p | IsCriticalPointAt (𝓡 2) f p ∧ sigNeg (chartHessianAt
      (fun y => f ((extChartAt (𝓡 2) p).symm y)) (extChartAt (𝓡 2) p p)) = 1}.ncard = 1)
    (hconn : ∀ a : ℝ, IsPreconnected {x | f x < a}) :
    ∃ m s p q : S₂,
      f m < f s ∧ f s < f p ∧ f p < f q ∧
      IsMinOn f _root_.Set.univ m ∧ IsMaxOn f _root_.Set.univ q ∧ IsLocalMax f p ∧
      {x | IsCriticalPointAt (𝓡 2) f x} = {m, s, p, q} ∧
      sigNeg (chartHessianAt (fun y => f ((extChartAt (𝓡 2) s).symm y))
        (extChartAt (𝓡 2) s s)) = 1 ∧
      ∀ a ∈ _root_.Set.Ioo (f s) (f p), ∀ x, f x ∈ _root_.Set.Ico a (f p) →
        ¬ IsCriticalPointAt (𝓡 2) f x := by
  obtain ⟨m, s, p, q, hms, hmp, hpq, hsq, hm, hq, hpmax, hC, _, hsindex, hpindex, _⟩ :=
    exists_min_saddle_two_max_of_one_saddle hf hnd hinj hone hconn
  have hmc : IsCriticalPointAt (𝓡 2) f m := hC.symm.subset (by simp)
  have hsc : IsCriticalPointAt (𝓡 2) f s := hC.symm.subset (by simp)
  have hpc : IsCriticalPointAt (𝓡 2) f p := hC.symm.subset (by simp)
  have hmin (x : S₂) (hxm : x ≠ m) : f m < f x := by
    apply lt_of_le_of_ne (hm (_root_.Set.mem_univ x))
    intro h
    exact hxm (eq_of_isMin_of_injOn_criticalPoints hinj
      (fun y => (show f x = f m from h.symm).le.trans (hm (_root_.Set.mem_univ y))) (fun y => hm (_root_.Set.mem_univ y)))
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  have hsp : f s < f p := by
    by_contra hnot
    have hps : f p < f s := lt_of_le_of_ne (le_of_not_gt hnot) (by
      intro h
      have hspoint := hinj hpc hsc h
      rw [hspoint] at hpindex
      omega)
    have hchart₁ := exists_quadratic_chart_of_isLocalMax hf (hnd p hpc) hpmax
    rw [hdim] at hchart₁
    obtain ⟨R₁, hR₁, χ₁, hsource₁, hχ₁0, hnormal₁⟩ := hchart₁
    obtain ⟨r₁, hr₁, hr₁small⟩ := exists_between
      (lt_min hR₁ (Real.sqrt_pos.mpr (sub_pos.mpr hmp)))
    have hr₁sq : r₁ ^ 2 < f p - f m := by
      have h := sq_lt_sq₀ hr₁.le (Real.sqrt_nonneg (f p - f m)) |>.mpr
        (hr₁small.trans_le (min_le_right _ _))
      rwa [Real.sq_sqrt (sub_pos.mpr hmp).le] at h
    let a := f p + (-1) / 2 * r₁ ^ 2
    have hma : f m < a := by dsimp [a]; nlinarith [sq_nonneg r₁]
    have hap : a < f p := by dsimp [a]; nlinarith [sq_pos_of_pos hr₁]
    have hhigh : IsPreconnected {x | a < f x} := by
      apply (isConnected_superlevel_of_no_critical_values_above_minimum
        1 hf (hnd m hmc) hmin hma ?_).isPreconnected
      intro x hx hc
      have hmem : x ∈ {y | IsCriticalPointAt (𝓡 2) f y} := hc
      rw [hC] at hmem
      change f m < f x ∧ f x ≤ a at hx
      rcases hmem with rfl | rfl | rfl | rfl <;> linarith
    have hqcomp : q ∈ connectedComponentIn {x | a ≤ f x} p :=
      hhigh.subset_connectedComponentIn (show p ∈ {x | a < f x} from hap)
        (by intro x hx; exact (show a < f x from hx).le) (hap.trans hpq)
    have hr₁src : _root_.Metric.closedBall 0 r₁ ⊆ χ₁.source := by
      rw [hsource₁]
      exact _root_.Metric.closedBall_subset_ball (hr₁small.trans_le (min_le_left _ _))
    have hcomp := χ₁.toOpenPartialHomeomorph.closedBall_image_eq_connectedComponentIn_superlevel
      hr₁.le (_root_.ProperSpace.isCompact_closedBall 0 r₁) hr₁src (by norm_num : (-1 : ℝ) < 0)
      (f := f) (fun y hy => by
        change f (χ₁ y) = f (χ₁ 0) + (-1) / 2 * ‖y‖ ^ 2
        rw [hχ₁0, hnormal₁ y hy]
        ring)
    simp only [show χ₁.toOpenPartialHomeomorph 0 = p from hχ₁0] at hcomp
    change χ₁ '' _root_.Metric.closedBall 0 r₁ = connectedComponentIn {x | a ≤ f x} p at hcomp
    rw [← hcomp] at hqcomp
    obtain ⟨y, hy, hyq⟩ := hqcomp
    have hnormal := hnormal₁ y (hr₁src hy)
    rw [hyq] at hnormal
    nlinarith [sq_nonneg ‖y‖]
  refine ⟨m, s, p, q, hms, hsp, hpq, hm, hq, hpmax, hC, hsindex, ?_⟩
  intro a ha x hx hc
  have hmem : x ∈ {y | IsCriticalPointAt (𝓡 2) f y} := hc
  rw [hC] at hmem
  change a ≤ f x ∧ f x < f p at hx
  have hsa : f s < a := ha.1
  rcases hmem with rfl | rfl | rfl | rfl <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Morse.exists_ordered_criticalPoints_of_one_saddle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Morse.exists_ordered_criticalPoints_of_one_saddle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Morse.exists_ordered_criticalPoints_of_one_saddle ``Submission.DifferentialGeometry.Topology.Morse.exists_ordered_criticalPoints_of_one_saddle

end DifferentialGeometry.Topology.Morse
