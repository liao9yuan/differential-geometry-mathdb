import Submission.DifferentialGeometry.Topology.Manifold.Path.Reparametrization
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.ContDiff

namespace Path
open _root_.Path

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Path in
theorem contDiffOn_extend_segment (a b : E) {n : ℕ∞ω} :
    ContDiffOn ℝ n (Path.segment a b).extend (_root_.Set.Icc 0 1) :=
  (AffineMap.contDiff_lineMap a b).contDiffOn.congr (Path.eqOn_extend_segment a b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Path.contDiffOn_extend_segment then
    throwError "Refusing to shadow existing declaration Path.contDiffOn_extend_segment"
  Lean.modifyEnv fun env => Lean.addAlias env `Path.contDiffOn_extend_segment ``Submission.Path.contDiffOn_extend_segment

open _root_.Path in
theorem extend_segment_withSittingInstants (a b : E) :
    (Path.segment a b).withSittingInstants.extend =
      fun t : ℝ => AffineMap.lineMap a b (Real.smoothTransition (3 * t - 1)) := by
  rw [extend_withSittingInstants]
  funext t
  exact Path.eqOn_extend_segment a b
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Path.extend_segment_withSittingInstants then
    throwError "Refusing to shadow existing declaration Path.extend_segment_withSittingInstants"
  Lean.modifyEnv fun env => Lean.addAlias env `Path.extend_segment_withSittingInstants ``Submission.Path.extend_segment_withSittingInstants

end Path
