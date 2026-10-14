import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Manifold _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.ENNReal

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem inner_le_exp_mul_inner_of_abs_deriv_le
    (g : ℝ → SmoothRiemannianMetric I M) {a b K s t : ℝ}
    (x : M) (v : TangentSpace I x)
    (hderiv : ∀ r ∈ _root_.Set.Icc a b,
      ∃ d : ℝ, HasDerivWithinAt (fun u => (g u).inner x v v) d (_root_.Set.Icc a b) r ∧
        |d| ≤ K * (g r).inner x v v)
    (hs : s ∈ _root_.Set.Icc a b) (ht : t ∈ _root_.Set.Icc a b) :
    (g s).inner x v v ≤ Real.exp (K * |s - t|) * (g t).inner x v v := by
  classical
  by_cases hst : s = t
  · subst s
    simp only [sub_self, abs_zero, _root_.MulZeroClass.mul_zero, Real.exp_zero, one_mul, le_refl]
  rcases eq_or_ne v 0 with rfl | hv
  · simp only [map_zero, _root_.MulZeroClass.mul_zero, le_refl]
  have hpos (r : ℝ) : 0 < (g r).inner x v v := (g r).pos x v hv
  choose d hd hbound using hderiv
  let f' : ℝ → ℝ := fun r => if hr : r ∈ _root_.Set.Icc a b then d r hr / (g r).inner x v v else 0
  have hlogderiv (r : ℝ) (hr : r ∈ _root_.Set.Icc a b) :
      HasDerivWithinAt (fun u => Real.log ((g u).inner x v v))
        (f' r) (_root_.Set.Icc a b) r := by
    simpa only [f', dif_pos hr] using (hd r hr).log (hpos r).ne'
  have hlogbound (r : ℝ) (hr : r ∈ _root_.Set.Icc a b) : ‖f' r‖ ≤ K := by
    dsimp only [f']
    rw [dif_pos hr]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hpos r), div_le_iff₀ (hpos r)]
    exact hbound r hr
  have hlog := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    hlogderiv hlogbound ht hs
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hlog
  have hle : Real.log ((g s).inner x v v) ≤
      K * |s - t| + Real.log ((g t).inner x v v) := by
    linarith [le_abs_self (Real.log ((g s).inner x v v) - Real.log ((g t).inner x v v))]
  calc
    (g s).inner x v v = Real.exp (Real.log ((g s).inner x v v)) :=
      (Real.exp_log (hpos s)).symm
    _ ≤ Real.exp (K * |s - t| + Real.log ((g t).inner x v v)) :=
      Real.exp_le_exp.mpr hle
    _ = Real.exp (K * |s - t|) * (g t).inner x v v := by
      rw [Real.exp_add, Real.exp_log (hpos t)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.inner_le_exp_mul_inner_of_abs_deriv_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.inner_le_exp_mul_inner_of_abs_deriv_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.inner_le_exp_mul_inner_of_abs_deriv_le ``Submission.DifferentialGeometry.inner_le_exp_mul_inner_of_abs_deriv_le

theorem riemannianEDistOf_le_exp_mul_of_abs_deriv_le
    (g : ℝ → SmoothRiemannianMetric I M) {a b K s t : ℝ}
    (hderiv : ∀ r ∈ _root_.Set.Icc a b, ∀ x : M, ∀ v : TangentSpace I x,
      ∃ d : ℝ, HasDerivWithinAt (fun u => (g u).inner x v v) d (_root_.Set.Icc a b) r ∧
        |d| ≤ K * (g r).inner x v v)
    (hs : s ∈ _root_.Set.Icc a b) (ht : t ∈ _root_.Set.Icc a b) (x y : M) :
    riemannianEDistOf (g s) x y ≤
      ENNReal.ofReal (Real.exp ((K / 2) * |s - t|)) * riemannianEDistOf (g t) x y := by
  have h := edistOf_le_of_quad (g t) (g s) (Real.exp_pos (K * |s - t|))
    (fun z v => inner_le_exp_mul_inner_of_abs_deriv_le g z v
      (fun r hr => hderiv r hr z v) hs ht) x y
  rw [← Real.exp_half, show K * |s - t| / 2 = (K / 2) * |s - t| by ring] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.riemannianEDistOf_le_exp_mul_of_abs_deriv_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.riemannianEDistOf_le_exp_mul_of_abs_deriv_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.riemannianEDistOf_le_exp_mul_of_abs_deriv_le ``Submission.DifferentialGeometry.riemannianEDistOf_le_exp_mul_of_abs_deriv_le

end DifferentialGeometry
