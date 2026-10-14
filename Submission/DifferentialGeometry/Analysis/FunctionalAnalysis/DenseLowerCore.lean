import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def lowerBall (J : X →L[ℝ] Y) (R : ℝ) : Set X := {x | ‖J x‖ ≤ R}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.lowerBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.lowerBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.lowerBall ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.lowerBall

def lowerCore (D : Set X) (J : X →L[ℝ] Y) (R : ℝ) :
    Set (lowerBall J R) := {x | (x : X) ∈ D}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.lowerCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.lowerCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.lowerCore ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.lowerCore

theorem dense_lowerCore {D : Set X} (hD : Dense D)
    (J : X →L[ℝ] Y) {R : ℝ} (hR : 0 < R) :
    Dense (lowerCore D J R) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨u, hu⟩ := hUne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU u hu
  set η : ℝ := _root_.Min.min (1 / 2) (ε / (2 * (‖(u : X)‖ + 1))) with hηdef
  have hden : 0 < 2 * (‖(u : X)‖ + 1) := by positivity
  have hη : 0 < η := by
    rw [hηdef]
    exact lt_min (by norm_num) (div_pos hε hden)
  have hηhalf : η ≤ 1 / 2 := by rw [hηdef]; exact min_le_left _ _
  have hηeps : η ≤ ε / (2 * (‖(u : X)‖ + 1)) := by
    rw [hηdef]
    exact min_le_right _ _
  set c : ℝ := 1 - η with hcdef
  have hc : 0 ≤ c := by rw [hcdef]; linarith
  have hc1 : c < 1 := by rw [hcdef]; linarith
  set x : X := c • (u : X) with hxdef
  have hxu : _root_.Dist.dist x (u : X) < ε := by
    have hmul : η * ‖(u : X)‖ ≤
        (ε / (2 * (‖(u : X)‖ + 1))) * ‖(u : X)‖ :=
      mul_le_mul_of_nonneg_right hηeps (norm_nonneg _)
    have hstrict :
        (ε / (2 * (‖(u : X)‖ + 1))) * ‖(u : X)‖ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith [norm_nonneg (u : X)]
    rw [dist_eq_norm, hxdef, hcdef,
      show (1 - η) • (u : X) - (u : X) = (-η) • (u : X) by module]
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hη]
    exact hmul.trans_lt hstrict
  have hxlow : ‖J x‖ < R := by
    have huR : ‖J (u : X)‖ ≤ R := u.property
    have hcR : c * R < R := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hc1 hR
    rw [hxdef, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left huR hc).trans_lt hcR
  let V : Set X := Metric.ball (u : X) ε ∩ {z | ‖J z‖ < R}
  have hV : IsOpen V := Metric.isOpen_ball.inter
    (isOpen_lt J.continuous.norm continuous_const)
  have hxV : x ∈ V := ⟨hxu, hxlow⟩
  obtain ⟨d, hdV, hdD⟩ := hD.inter_open_nonempty V hV ⟨x, hxV⟩
  let dS : lowerBall J R := ⟨d, by
    change ‖J d‖ ≤ R
    exact le_of_lt hdV.2⟩
  refine ⟨dS, ?_, ?_⟩
  · apply hball
    change _root_.Dist.dist d (u : X) < ε
    exact hdV.1
  · change d ∈ D
    exact hdD

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.dense_lowerCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.dense_lowerCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.dense_lowerCore ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.dense_lowerCore

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

end
