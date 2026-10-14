import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.Basic
import Mathlib.Topology.MetricSpace.Holder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set
open scoped _root_.Convolution _root_.NNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}

private theorem integrable_mollifier_mul {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f)
    (x : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun y => mollifierEps hε y * f (x - y)) volume := by
  exact ((mollifierEps_continuous hε).mul
    (hf.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      ((mollifierEps_compactSupport hε).mul_right)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.integrable_mollifier_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.integrable_mollifier_mul target :: scope.openDecls } }

theorem le_mollifyEps_of_le {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f) {c : ℝ}
    (hc : ∀ x, c ≤ f x) (x : EuclideanSpace ℝ (Fin d)) :
    c ≤ mollifyEps hε f x := by
  calc
    c = ∫ y : EuclideanSpace ℝ (Fin d), mollifierEps hε y * c := by
      rw [_root_.MeasureTheory.integral_mul_const, mollifierEps_integral_eq_one, one_mul]
    _ ≤ mollifyEps hε f x := by
      rw [mollifyEps_apply]
      exact _root_.MeasureTheory.integral_mono ((mollifierEps_integrable hε).mul_const c)
        (integrable_mollifier_mul hε hf x) (fun y =>
          mul_le_mul_of_nonneg_left (hc _) (mollifierEps_nonneg hε y))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.le_mollifyEps_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.le_mollifyEps_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.le_mollifyEps_of_le ``Submission.DifferentialGeometry.Analysis.Sobolev.le_mollifyEps_of_le

theorem mollifyEps_le_of_le {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f) {c : ℝ}
    (hc : ∀ x, f x ≤ c) (x : EuclideanSpace ℝ (Fin d)) :
    mollifyEps hε f x ≤ c := by
  calc
    mollifyEps hε f x ≤ ∫ y : EuclideanSpace ℝ (Fin d), mollifierEps hε y * c := by
      rw [mollifyEps_apply]
      exact _root_.MeasureTheory.integral_mono (integrable_mollifier_mul hε hf x)
        ((mollifierEps_integrable hε).mul_const c) (fun y =>
          mul_le_mul_of_nonneg_left (hc _) (mollifierEps_nonneg hε y))
    _ = c := by rw [_root_.MeasureTheory.integral_mul_const, mollifierEps_integral_eq_one, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifyEps_le_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifyEps_le_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifyEps_le_of_le ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifyEps_le_of_le

private theorem norm_mollifyEps_sub_le {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f)
    {x y : EuclideanSpace ℝ (Fin d)} {C : ℝ}
    (hC : ∀ z, ‖f (x - z) - f (y - z)‖ ≤ C) :
    ‖mollifyEps hε f x - mollifyEps hε f y‖ ≤ C := by
  rw [mollifyEps_apply, mollifyEps_apply,
    ← _root_.MeasureTheory.integral_sub (integrable_mollifier_mul hε hf x) (integrable_mollifier_mul hε hf y)]
  calc
    ‖∫ z, mollifierEps hε z * f (x - z) - mollifierEps hε z * f (y - z)‖ ≤
        ∫ z, mollifierEps hε z * C := by
      apply _root_.MeasureTheory.norm_integral_le_of_norm_le ((mollifierEps_integrable hε).mul_const C)
      filter_upwards with z
      rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_nonneg (mollifierEps_nonneg hε z)]
      exact mul_le_mul_of_nonneg_left (hC z) (mollifierEps_nonneg hε z)
    _ = C := by rw [_root_.MeasureTheory.integral_mul_const, mollifierEps_integral_eq_one, one_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.norm_mollifyEps_sub_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.norm_mollifyEps_sub_le target :: scope.openDecls } }

theorem holderWith_mollifyEps {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {K α : ℝ≥0}
    (hα : 0 < α) (hf : HolderWith K α f) :
    HolderWith K α (mollifyEps hε f) := by
  intro x y
  have hnorm : _root_.Dist.dist (mollifyEps hε f x) (mollifyEps hε f y) ≤
      (K : ℝ) * _root_.Dist.dist x y ^ (α : ℝ) := by
    rw [dist_eq_norm]
    apply norm_mollifyEps_sub_le hε (hf.continuous hα)
    intro z
    simpa only [← dist_eq_norm, dist_sub_right] using hf.dist_le (x - z) (y - z)
  rw [edist_dist, edist_dist]
  calc
    ENNReal.ofReal (_root_.Dist.dist (mollifyEps hε f x) (mollifyEps hε f y)) ≤
        ENNReal.ofReal ((K : ℝ) * _root_.Dist.dist x y ^ (α : ℝ)) := ENNReal.ofReal_le_ofReal hnorm
    _ = _ := by
      rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.holderWith_mollifyEps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.holderWith_mollifyEps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.holderWith_mollifyEps ``Submission.DifferentialGeometry.Analysis.Sobolev.holderWith_mollifyEps

theorem norm_mollifyEps_sub_le_of_holderWith {ε : ℝ} (hε : 0 < ε)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {K α : ℝ≥0}
    (hα : 0 < α) (hf : HolderWith K α f) (x : EuclideanSpace ℝ (Fin d)) :
    ‖mollifyEps hε f x - f x‖ ≤ (K : ℝ) * ε ^ (α : ℝ) := by
  have hc : (∫ y : EuclideanSpace ℝ (Fin d), mollifierEps hε y * f x) = f x := by
    rw [_root_.MeasureTheory.integral_mul_const, mollifierEps_integral_eq_one, one_mul]
  rw [mollifyEps_apply, ← hc,
    ← _root_.MeasureTheory.integral_sub (integrable_mollifier_mul hε (hf.continuous hα) x)
      ((mollifierEps_integrable hε).mul_const (f x))]
  calc
    ‖∫ y, mollifierEps hε y * f (x - y) - mollifierEps hε y * f x‖ ≤
      ∫ y : EuclideanSpace ℝ (Fin d), mollifierEps hε y *
        ((K : ℝ) * ε ^ (α : ℝ)) := by
      apply _root_.MeasureTheory.norm_integral_le_of_norm_le
        ((mollifierEps_integrable hε).mul_const ((K : ℝ) * ε ^ (α : ℝ)))
      filter_upwards with y
      by_cases hy : mollifierEps hε y = 0
      · simp only [hy, _root_.MulZeroClass.zero_mul, sub_self, norm_zero, le_refl]
      · have hynorm : ‖y‖ ≤ ε := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using
            mollifierEps_support_subset_closedBall_eps hε hy
        have hdist : _root_.Dist.dist (x - y) x ≤ ε := by
          simpa [dist_eq_norm] using hynorm
        have hbound : ‖f (x - y) - f x‖ ≤ (K : ℝ) * ε ^ (α : ℝ) := by
          simpa only [← dist_eq_norm] using hf.dist_le_of_le hdist
        rw [← mul_sub, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg (mollifierEps_nonneg hε y)]
        exact mul_le_mul_of_nonneg_left hbound (mollifierEps_nonneg hε y)
    _ = _ := by rw [_root_.MeasureTheory.integral_mul_const, mollifierEps_integral_eq_one, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.norm_mollifyEps_sub_le_of_holderWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.norm_mollifyEps_sub_le_of_holderWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.norm_mollifyEps_sub_le_of_holderWith ``Submission.DifferentialGeometry.Analysis.Sobolev.norm_mollifyEps_sub_le_of_holderWith

end DifferentialGeometry.Analysis.Sobolev
