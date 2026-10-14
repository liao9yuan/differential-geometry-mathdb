import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.MetricSpace.Lipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission










noncomputable section

open scoped _root_.InnerProductSpace _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {s : Set E} (hne : s.Nonempty) (hs : IsComplete s) (hc : Convex ℝ s)


def convexProjection (x : E) : s :=
  ⟨(exists_norm_eq_iInf_of_complete_convex hne hs hc x).choose,
    (exists_norm_eq_iInf_of_complete_convex hne hs hc x).choose_spec.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.convexProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.convexProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.convexProjection ``Submission.DifferentialGeometry.Geometry.convexProjection

theorem convexProjection_variational (x : E) (y : s) :
    ⟪x - convexProjection hne hs hc x, (y : E) - convexProjection hne hs hc x⟫_ℝ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hc (convexProjection hne hs hc x).property).mp
    (exists_norm_eq_iInf_of_complete_convex hne hs hc x).choose_spec.2 y y.property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.convexProjection_variational then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.convexProjection_variational"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.convexProjection_variational ``Submission.DifferentialGeometry.Geometry.convexProjection_variational

@[simp] theorem convexProjection_of_mem (x : s) : convexProjection hne hs hc x = x := by
  apply Subtype.ext
  exact (sub_eq_zero.mp (real_inner_self_nonpos.mp (convexProjection_variational hne hs hc x x))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.convexProjection_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.convexProjection_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.convexProjection_of_mem ``Submission.DifferentialGeometry.Geometry.convexProjection_of_mem


theorem convexProjection_lipschitz : LipschitzWith 1 (convexProjection hne hs hc) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let p : E := convexProjection hne hs hc x
  let q : E := convexProjection hne hs hc y
  let d : E := p - q
  have hx : 0 ≤ ⟪x - p, d⟫_ℝ := by
    have h := convexProjection_variational hne hs hc x (convexProjection hne hs hc y)
    change ⟪x - p, q - p⟫_ℝ ≤ 0 at h
    rw [show q - p = -d by dsimp [d]; abel, inner_neg_right] at h
    linarith
  have hy : ⟪y - q, d⟫_ℝ ≤ 0 :=
    convexProjection_variational hne hs hc y (convexProjection hne hs hc x)
  have hi : ⟪x - y, d⟫_ℝ = ‖d‖ ^ 2 + ⟪x - p, d⟫_ℝ - ⟪y - q, d⟫_ℝ := by
    rw [show x - y = d + (x - p) - (y - q) by dsimp [d]; abel,
      inner_sub_left, inner_add_left, real_inner_self_eq_norm_sq]
  have hC := real_inner_le_norm (x - y) d
  have hmul : ‖d‖ * ‖d‖ ≤ ‖x - y‖ * ‖d‖ := by nlinarith
  change _root_.Dist.dist p q ≤ (1 : ℝ≥0) * _root_.Dist.dist x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  change ‖d‖ ≤ ‖x - y‖
  rcases (norm_nonneg d).eq_or_lt with hd | hd
  · rw [← hd]
    exact norm_nonneg _
  · exact (mul_le_mul_iff_of_pos_right hd).mp hmul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.convexProjection_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.convexProjection_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.convexProjection_lipschitz ``Submission.DifferentialGeometry.Geometry.convexProjection_lipschitz

end DifferentialGeometry.Geometry
