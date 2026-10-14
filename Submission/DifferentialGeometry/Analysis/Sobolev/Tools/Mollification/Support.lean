import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.Basic
import Mathlib.Topology.MetricSpace.Thickening

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.Analysis.Sobolev

open _root_.MeasureTheory _root_.Metric _root_.Set
open scoped _root_.Pointwise _root_.Convolution

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem mollifyEps_nonneg {ε : ℝ} (hε : 0 < ε)
    {u : E → ℝ} (hu : ∀ x, 0 ≤ u x) (x : E) :
    0 ≤ mollifyEps hε u x := by
  rw [mollifyEps_apply]
  exact _root_.MeasureTheory.integral_nonneg fun y => mul_nonneg (mollifierEps_nonneg hε y) (hu (x - y))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.mollifyEps_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.mollifyEps_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.mollifyEps_nonneg ``Submission.DifferentialGeometry.Analysis.Sobolev.mollifyEps_nonneg

theorem tsupport_mollifyEps_subset_cthickening {ε : ℝ} (hε : 0 < ε) (u : E → ℝ) :
    tsupport (mollifyEps hε u) ⊆ _root_.Metric.cthickening ε (tsupport u) := by
  apply closure_minimal _ _root_.Metric.isClosed_cthickening
  have hs : Function.support (mollifyEps hε u) ⊆
      Function.support (mollifierEps hε) + Function.support u :=
    _root_.MeasureTheory.support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ)
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hs hx
  apply _root_.Metric.mem_cthickening_of_dist_le (y + z) z ε (tsupport u) (subset_closure hz)
  have hyε := mollifierEps_support_subset_closedBall_eps hε hy
  simpa only [_root_.Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hyε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.tsupport_mollifyEps_subset_cthickening then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.tsupport_mollifyEps_subset_cthickening"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.tsupport_mollifyEps_subset_cthickening ``Submission.DifferentialGeometry.Analysis.Sobolev.tsupport_mollifyEps_subset_cthickening

theorem exists_isCompact_tsupport_mollifyEps_subset
    {u : E → ℝ} (hu : HasCompactSupport u)
    {Ω : Set E} (hΩ : IsOpen Ω) (huΩ : tsupport u ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : Set E, IsCompact K ∧ K ⊆ Ω ∧
      tsupport u ⊆ K ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ δ →
        tsupport (mollifyEps hε u) ⊆ K := by
  obtain ⟨δ, hδ, hδΩ⟩ := hu.exists_cthickening_subset_open hΩ huΩ
  refine ⟨δ, hδ, _root_.Metric.cthickening δ (tsupport u), hu.cthickening, hδΩ,
    _root_.Metric.self_subset_cthickening _, ?_⟩
  intro ε hε hεδ
  exact (tsupport_mollifyEps_subset_cthickening hε u).trans
    (_root_.Metric.cthickening_mono hεδ (tsupport u))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.exists_isCompact_tsupport_mollifyEps_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.exists_isCompact_tsupport_mollifyEps_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.exists_isCompact_tsupport_mollifyEps_subset ``Submission.DifferentialGeometry.Analysis.Sobolev.exists_isCompact_tsupport_mollifyEps_subset

end DifferentialGeometry.Analysis.Sobolev
