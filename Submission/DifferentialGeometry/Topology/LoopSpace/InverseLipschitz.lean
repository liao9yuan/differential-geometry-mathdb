import Submission.DifferentialGeometry.Topology.LoopSpace.CircleMetric
import Mathlib.Topology.MetricSpace.Antilipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
theorem abs_sub_le_mul_norm_sub_of_antilipschitz_loop
    {Γ : loopCircle → F} {L : ℝ≥0} (hΓ : AntilipschitzWith L Γ)
    {a b : ℝ} (hab : |a - b| ≤ 1 / 2) :
    |a - b| ≤ (L : ℝ) * ‖Γ (a : loopCircle) - Γ (b : loopCircle)‖ := by
  have hnorm : ‖((a - b : ℝ) : loopCircle)‖ = |a - b| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr (by simpa using hab)
  have h := hΓ.le_mul_dist (a : loopCircle) (b : loopCircle)
  simpa only [dist_eq_norm, ← AddCircle.coe_sub, hnorm] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.abs_sub_le_mul_norm_sub_of_antilipschitz_loop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.abs_sub_le_mul_norm_sub_of_antilipschitz_loop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.abs_sub_le_mul_norm_sub_of_antilipschitz_loop ``Submission.DifferentialGeometry.Topology.abs_sub_le_mul_norm_sub_of_antilipschitz_loop

omit [NormedSpace ℝ F] in
theorem sub_le_two_mul_norm_sub_of_antilipschitz_loop
    {Γ : loopCircle → F} {L : ℝ≥0} (hΓ : AntilipschitzWith L Γ)
    {a b : ℝ} (hab : a ≤ b) (hshort : b - a ≤ 2 / 3) :
    b - a ≤ 2 * (L : ℝ) * ‖Γ (b : loopCircle) - Γ (a : loopCircle)‖ := by
  have hcircle : b - a ≤ 2 * _root_.Dist.dist (b : loopCircle) (a : loopCircle) := by
    rw [dist_eq_norm, ← AddCircle.coe_sub]
    by_cases hhalf : b - a ≤ 1 / 2
    · have hnorm : ‖((b - a : ℝ) : loopCircle)‖ = b - a := by
        rw [(AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr]
        · exact abs_of_nonneg (sub_nonneg.mpr hab)
        · simpa only [abs_one, abs_of_nonneg (sub_nonneg.mpr hab)] using hhalf
      rw [hnorm]
      linarith
    · have hnorm : ‖((b - a - 1 : ℝ) : loopCircle)‖ = |b - a - 1| :=
        (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr (by
          rw [abs_one, abs_le]
          constructor <;> linarith)
      have hcoe : ((b - a - 1 : ℝ) : loopCircle) = ((b - a : ℝ) : loopCircle) := by
        rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
      rw [hcoe] at hnorm
      rw [hnorm, abs_of_nonpos (by linarith : b - a - 1 ≤ 0)]
      linarith
  exact hcircle.trans (by
    have h := mul_le_mul_of_nonneg_left
      (hΓ.le_mul_dist (b : loopCircle) (a : loopCircle)) (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [dist_eq_norm, mul_assoc] using h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sub_le_two_mul_norm_sub_of_antilipschitz_loop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sub_le_two_mul_norm_sub_of_antilipschitz_loop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sub_le_two_mul_norm_sub_of_antilipschitz_loop ``Submission.DifferentialGeometry.Topology.sub_le_two_mul_norm_sub_of_antilipschitz_loop

end DifferentialGeometry.Topology

open _root_.AntilipschitzWith in
theorem AntilipschitzWith.lipschitzWith_of_comp
    {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]
    {f : Y → Z} {g : X → Y} {K L : ℝ≥0} (hf : AntilipschitzWith K f)
    (hg : LipschitzWith L (f ∘ g)) : LipschitzWith (K * L) g := by
  intro x y
  apply (hf (g x) (g y)).trans
  calc
    (K : ℝ≥0∞) * _root_.EDist.edist (f (g x)) (f (g y)) ≤
        (K : ℝ≥0∞) * ((L : ℝ≥0∞) * _root_.EDist.edist x y) := by
      gcongr
      exact hg x y
    _ = (↑(K * L) : ℝ≥0∞) * _root_.EDist.edist x y := by
      simp only [ENNReal.coe_mul, mul_assoc]

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.AntilipschitzWith
  let env ← Lean.getEnv
  if env.contains `AntilipschitzWith.lipschitzWith_of_comp then
    throwError "Refusing to shadow existing declaration AntilipschitzWith.lipschitzWith_of_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `AntilipschitzWith.lipschitzWith_of_comp ``Submission.AntilipschitzWith.lipschitzWith_of_comp

end
