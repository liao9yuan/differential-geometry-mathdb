import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set
open scoped _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.Analysis

theorem continuousOn_of_norm_sub_le_rpow
    {X Y : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
    {v : X → Y} {S : Set X} {C α : ℝ} (hC : 0 ≤ C) (hα : 0 < α)
    (h : ∀ x ∈ S, ∀ y ∈ S, ‖v x - v y‖ ≤ C * ‖x - y‖ ^ α) :
    ContinuousOn v S := by
  have hh : HolderOnWith (NNReal.mk C hC) (NNReal.mk α hα.le) v S := by
    intro x hx y hy
    have hn := ENNReal.ofReal_le_ofReal (h x hx y hy)
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
    rw [← ENNReal.ofReal_eq_coe_nnreal hC]
    change ENNReal.ofReal ‖v x - v y‖ ≤
      ENNReal.ofReal C * ENNReal.ofReal ‖x - y‖ ^ α
    rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (x - y)) hα.le,
      ← ENNReal.ofReal_mul hC]
    exact hn
  exact hh.continuousOn hα

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.continuousOn_of_norm_sub_le_rpow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.continuousOn_of_norm_sub_le_rpow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.continuousOn_of_norm_sub_le_rpow ``Submission.DifferentialGeometry.Analysis.continuousOn_of_norm_sub_le_rpow

end DifferentialGeometry.Analysis
