import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Submission.DifferentialGeometry.Geometry.Metric.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry

open _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]

theorem ball_subset_of_le
    {X : Type*} [PseudoMetricSpace X] {x : X} {r R : Real}
    (hr : r ≤ R) :
    Metric.ball x r ⊆ Metric.ball x R := by
  intro y hy
  rw [Metric.mem_ball] at hy ⊢
  exact lt_of_lt_of_le hy hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.ball_subset_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.ball_subset_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.ball_subset_of_le ``Submission.DifferentialGeometry.ball_subset_of_le


theorem cball_subset_of_le
    {X : Type*} [PseudoMetricSpace X] {x : X} {r R : Real}
    (hr : r ≤ R) :
    Metric.closedBall x r ⊆ Metric.closedBall x R := by
  intro y hy
  rw [Metric.mem_closedBall] at hy ⊢
  exact le_trans hy hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.cball_subset_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.cball_subset_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.cball_subset_of_le ``Submission.DifferentialGeometry.cball_subset_of_le

theorem injOn_of_return
    {X Y ι : Type*} [PseudoMetricSpace X]
    {S : Set X} {F : X → Y} {H : Y → X}
    (K V : ι → Set X) {ρ : Real}
    (hρ : 0 < ρ)
    (hcover : S ⊆ ⋃ i, K i)
    (hbuffer : ∀ i x, x ∈ K i → Metric.ball x ρ ⊆ V i)
    (hlocal : ∀ i, Set.InjOn F (V i))
    (hreturn : ∀ x, x ∈ S → _root_.Dist.dist (H (F x)) x < ρ / 2) :
    Set.InjOn F S := by
  intro x hx y hy hF
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover hx)
  apply hlocal i
  · exact hbuffer i x hxi (Metric.mem_ball_self hρ)
  · apply hbuffer i x hxi
    rw [Metric.mem_ball]
    calc
      dist y x ≤ _root_.Dist.dist y (H (F y)) + _root_.Dist.dist (H (F y)) x := dist_triangle _ _ _
      _ = _root_.Dist.dist (H (F y)) y + _root_.Dist.dist (H (F x)) x := by
        rw [dist_comm y (H (F y)), ← hF]
      _ < ρ / 2 + ρ / 2 := add_lt_add (hreturn y hy) (hreturn x hx)
      _ = ρ := by ring
  · exact hF

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.injOn_of_return then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.injOn_of_return"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.injOn_of_return ``Submission.DifferentialGeometry.injOn_of_return

end DifferentialGeometry
