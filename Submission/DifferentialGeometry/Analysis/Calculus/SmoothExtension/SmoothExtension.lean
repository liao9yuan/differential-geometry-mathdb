import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Separation.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter _root_.Topology
open scoped _root_.ContDiff

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_update_of_eventuallyEq [DecidableEq E] {n : ℕ∞ω} (B C : E → F) (p : E)
    (hB : ∀ x, x ≠ p → ContDiffAt ℝ n B x)
    (hC : ContDiffAt ℝ n C p)
    (hmatch : B =ᶠ[𝓝[≠] p] C) :
    ContDiff ℝ n (Function.update B p (C p)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = p
  · subst x
    apply hC.congr_of_eventuallyEq
    exact eventuallyEq_nhds_of_eventuallyEq_nhdsNE
      ((Function.update_eventuallyEq_nhdsNE B p p (C p)).trans hmatch)
      (Function.update_self _ _ _)
  · apply (hB x hx).congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact Function.update_of_ne hy _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiff_update_of_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiff_update_of_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiff_update_of_eventuallyEq ``Submission.DifferentialGeometry.Analysis.contDiff_update_of_eventuallyEq

end DifferentialGeometry.Analysis
