import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.TruncatedCampanato
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Poincare.Convex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Metric
open scoped _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "D" => _root_.Metric.ball (0 : E) 1

private theorem norm_setAverage_truncated_sub_double_le
    {v : E → F} (hvm : _root_.MeasureTheory.MemLp v 2 (volume.restrict D)) {x y : E}
    (hy : y ∈ _root_.Metric.closedBall (0 : E) 1) {r α V : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hV : 0 ≤ V)
    (hsub : D ∩ _root_.Metric.ball y r ⊆ D ∩ _root_.Metric.ball x (2 * r))
    (hvar : (∫ z in D ∩ _root_.Metric.ball x (2 * r),
      ‖v z - ⨍ w in D ∩ _root_.Metric.ball x (2 * r), v w‖ ^ 2) ≤ V * (2 * r) ^ (2 + 2 * α)) :
    ‖(⨍ z in D ∩ _root_.Metric.ball y r, v z) - (⨍ z in D ∩ _root_.Metric.ball x (2 * r), v z)‖ ≤
      Real.sqrt (16 * V / Real.pi) * (2 * r) ^ α := by
  let S := D ∩ _root_.Metric.ball y r
  let T := D ∩ _root_.Metric.ball x (2 * r)
  have hdensity : Real.pi * r ^ 2 / 4 ≤ volume.real S :=
    volume_real_ball_inter_ball_fin_two_lower_bound (by norm_num : (0 : ℝ) < 1)
      hy hr (by linarith)
  have hSpos : 0 < volume.real S := (by positivity : 0 < Real.pi * r ^ 2 / 4).trans_le hdensity
  have hTfin : _root_.MeasureTheory.MeasureSpace.volume T ≠ ∞ :=
    ((_root_.MeasureTheory.measure_mono _root_.Set.inter_subset_left).trans_lt _root_.MeasureTheory.measure_ball_lt_top).ne
  have hfT : _root_.MeasureTheory.MemLp v 2 (volume.restrict T) :=
    hvm.mono_measure (Measure.restrict_mono _root_.Set.inter_subset_left le_rfl)
  have hmean := norm_setAverage_sub_setAverage_sq_le hsub hSpos hTfin hfT
  have hinv : (volume.real S)⁻¹ ≤ (Real.pi * r ^ 2 / 4)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hdensity
  have hrpow : (2 * r) ^ (2 + 2 * α) = (2 * r) ^ 2 * ((2 * r) ^ α) ^ 2 := by
    rw [Real.rpow_add (by positivity : 0 < 2 * r), Real.rpow_two]
    congr 1
    rw [mul_comm (2 : ℝ) α, Real.rpow_mul (by positivity : 0 ≤ 2 * r), Real.rpow_two]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
    (Real.rpow_nonneg (by positivity : 0 ≤ 2 * r) _))).mp
  calc
    _ ≤ (volume.real S)⁻¹ * ∫ z in T, ‖v z - ⨍ w in T, v w‖ ^ 2 := hmean
    _ ≤ (volume.real S)⁻¹ * (V * (2 * r) ^ (2 + 2 * α)) :=
      mul_le_mul_of_nonneg_left hvar (inv_nonneg.mpr hSpos.le)
    _ ≤ (Real.pi * r ^ 2 / 4)⁻¹ * (V * (2 * r) ^ (2 + 2 * α)) :=
      mul_le_mul_of_nonneg_right hinv (mul_nonneg hV (Real.rpow_nonneg (by positivity) _))
    _ = (Real.sqrt (16 * V / Real.pi) * (2 * r) ^ α) ^ 2 := by
      rw [hrpow]
      simp only [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 16 * V / Real.pi)]
      field_simp
      ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.norm_setAverage_truncated_sub_double_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.norm_setAverage_truncated_sub_double_le target :: scope.openDecls } }

theorem exists_uniform_holder_bound_of_truncated_variance_bound
    {V α R₀ : ℝ} (hV : 0 ≤ V) (hα : 0 < α) (hR₀ : R₀ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : E → F,
      _root_.MeasureTheory.MemLp v 2 (volume.restrict D) → ContinuousOn v D →
      (∀ x ∈ _root_.Metric.closedBall (0 : E) 1, ∀ r : ℝ, 0 < r → r ≤ R₀ →
        (∫ y in D ∩ _root_.Metric.ball x r, ‖v y - ⨍ z in D ∩ _root_.Metric.ball x r, v z‖ ^ 2) ≤
          V * r ^ (2 + 2 * α)) →
      ∀ x ∈ D, ∀ y ∈ D, _root_.Dist.dist x y < R₀ / 2 →
        ‖v x - v y‖ ≤ C * (_root_.Dist.dist x y) ^ α := by
  let A := Real.sqrt (16 * V / Real.pi)
  let q := (1 / 2 : ℝ) ^ α
  have hq : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hden : 0 < 1 - q := sub_pos.mpr hq
  let C := 2 * A * ((1 - q)⁻¹ + (2 : ℝ) ^ α)
  have hC : 0 ≤ C := by dsimp only [C, A]; positivity
  refine ⟨C, hC, ?_⟩
  intro v hvm hv hvar x hx y hy hdist
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero, dist_self, Real.zero_rpow hα.ne', _root_.MulZeroClass.mul_zero, le_refl]
  let r := _root_.Dist.dist x y
  have hr : 0 < r := dist_pos.mpr hxy
  have hrR : r ≤ R₀ := by dsimp only [r]; linarith
  have hr1 : r ≤ 1 := hrR.trans hR₀
  have h2rR : 2 * r ≤ R₀ := by dsimp only [r]; linarith
  let mx := ⨍ z in D ∩ _root_.Metric.ball x r, v z
  let my := ⨍ z in D ∩ _root_.Metric.ball y r, v z
  let m := ⨍ z in D ∩ _root_.Metric.ball x (2 * r), v z
  have htailx : ‖v x - mx‖ ≤ A * r ^ α / (1 - q) :=
    norm_sub_setAverage_truncated_ball_le_of_variance_bound hvm hv hV hα hR₀ hx
      (hvar x (_root_.Metric.ball_subset_closedBall hx)) hr hrR
  have htaily : ‖v y - my‖ ≤ A * r ^ α / (1 - q) :=
    norm_sub_setAverage_truncated_ball_le_of_variance_bound hvm hv hV hα hR₀ hy
      (hvar y (_root_.Metric.ball_subset_closedBall hy)) hr hrR
  have hdouble := hvar x (_root_.Metric.ball_subset_closedBall hx) (2 * r) (by positivity) h2rR
  have hcrossx : ‖mx - m‖ ≤ A * (2 * r) ^ α :=
    norm_setAverage_truncated_sub_double_le hvm (_root_.Metric.ball_subset_closedBall hx) hr hr1 hV
      (_root_.Set.inter_subset_inter_right D (_root_.Metric.ball_subset_ball (by linarith))) hdouble
  have hsuby : D ∩ _root_.Metric.ball y r ⊆ D ∩ _root_.Metric.ball x (2 * r) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    have hzy : _root_.Dist.dist z y < r := hz.2
    have hyx : _root_.Dist.dist y x = r := dist_comm y x
    exact (dist_triangle z y x).trans_lt (by linarith)
  have hcrossy : ‖my - m‖ ≤ A * (2 * r) ^ α :=
    norm_setAverage_truncated_sub_double_le hvm (_root_.Metric.ball_subset_closedBall hy) hr hr1 hV hsuby hdouble
  have htri : ‖v x - v y‖ ≤ ‖v x - mx‖ + ‖mx - m‖ + ‖my - m‖ + ‖v y - my‖ := by
    have h₁ := norm_sub_le_norm_sub_add_norm_sub (v x) mx (v y)
    have h₂ := norm_sub_le_norm_sub_add_norm_sub mx m (v y)
    have h₃ := norm_sub_le_norm_sub_add_norm_sub m my (v y)
    rw [norm_sub_rev m my, norm_sub_rev my (v y)] at h₃
    linarith
  calc
    ‖v x - v y‖ ≤ 2 * (A * r ^ α / (1 - q)) + 2 * (A * (2 * r) ^ α) := by
      linarith
    _ = C * (_root_.Dist.dist x y) ^ α := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le]
      dsimp only [C, r]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_uniform_holder_bound_of_truncated_variance_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_uniform_holder_bound_of_truncated_variance_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_uniform_holder_bound_of_truncated_variance_bound ``Submission.DifferentialGeometry.Analysis.exists_uniform_holder_bound_of_truncated_variance_bound

end DifferentialGeometry.Analysis

end

end

section

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Metric
open scoped _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem exists_uniform_holder_bound_of_truncated_weak_gradient_power
    {A p δ : ℝ} (hA : 0 ≤ A) (hp : 0 < p) (hδ : δ ≤ 1) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ f : Plane → ℝ,
      ∀ hw : DeGiorgi.MemW1pWitness 2 f (_root_.Metric.ball (0 : Plane) 1),
      ContinuousOn f (_root_.Metric.ball (0 : Plane) 1) →
      (∀ x ∈ _root_.Metric.closedBall (0 : Plane) 1, ∀ s : ℝ, 0 < s → s ≤ δ →
        (∫ y in _root_.Metric.ball (0 : Plane) 1 ∩ _root_.Metric.ball x s, ‖hw.weakGrad y‖ ^ 2) ≤ A * s ^ p) →
      ∀ x ∈ _root_.Metric.ball (0 : Plane) 1, ∀ y ∈ _root_.Metric.ball (0 : Plane) 1, _root_.Dist.dist x y < δ / 2 →
        |f x - f y| ≤ H * (_root_.Dist.dist x y) ^ (p / 2) := by
  obtain ⟨H, hH, hbound⟩ :=
    DifferentialGeometry.Analysis.exists_uniform_holder_bound_of_truncated_variance_bound
    (F := ℝ) (V := 16 * A) (α := p / 2) (R₀ := δ) (by positivity) (half_pos hp) hδ
  refine ⟨H, hH, ?_⟩
  intro f hw hfc hgrad x hx y hy hxy
  have hvar : ∀ c ∈ _root_.Metric.closedBall (0 : Plane) 1, ∀ s : ℝ, 0 < s → s ≤ δ →
      (∫ z in _root_.Metric.ball (0 : Plane) 1 ∩ _root_.Metric.ball c s,
        ‖f z - ⨍ w in _root_.Metric.ball (0 : Plane) 1 ∩ _root_.Metric.ball c s, f w‖ ^ 2) ≤
        (16 * A) * s ^ (2 + 2 * (p / 2)) := by
    intro c hc s hs hsδ
    have hdiam : ∀ x ∈ _root_.Metric.ball (0 : Plane) 1 ∩ _root_.Metric.ball c s,
        ∀ y ∈ _root_.Metric.ball (0 : Plane) 1 ∩ _root_.Metric.ball c s, ‖x - y‖ ≤ 2 * s := by
      intro x hx y hy
      have hh := dist_triangle x c y
      rw [dist_comm c y] at hh
      rw [← dist_eq_norm]
      exact hh.trans (by linarith [mem_ball.mp hx.2, mem_ball.mp hy.2])
    have hP := integral_sub_average_sq_le_of_convex_subset_unitBall
      (isOpen_ball.inter _root_.Metric.isOpen_ball).measurableSet
      ((convex_ball (0 : Plane) 1).inter (convex_ball c s)) _root_.Set.inter_subset_left hw hdiam
    have hg := hgrad c hc s hs hsδ
    have hcoeff : (2 : ℝ) ^ 2 * (2 * s) ^ 2 = 16 * s ^ 2 := by ring
    rw [hcoeff] at hP
    simp only [Real.norm_eq_abs, sq_abs]
    calc
      _ ≤ 16 * s ^ 2 * ∫ z in _root_.Metric.ball (0 : Plane) 1 ∩ _root_.Metric.ball c s, ‖hw.weakGrad z‖ ^ 2 := hP
      _ ≤ 16 * s ^ 2 * (A * s ^ p) := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by
        rw [show 2 + 2 * (p / 2) = 2 + p by ring, Real.rpow_add hs, Real.rpow_two]
        ring
  simpa only [Real.norm_eq_abs] using hbound f hw.memLp hfc hvar x hx y hy hxy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_uniform_holder_bound_of_truncated_weak_gradient_power then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_uniform_holder_bound_of_truncated_weak_gradient_power"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_uniform_holder_bound_of_truncated_weak_gradient_power ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_uniform_holder_bound_of_truncated_weak_gradient_power

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end
