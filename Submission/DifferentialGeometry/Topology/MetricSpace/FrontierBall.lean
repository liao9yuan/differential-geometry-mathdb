import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Normed.Module.Convex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Analysis

theorem ball_infDist_frontier_subset_of_isOpen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    (hfrontier : (frontier U).Nonempty) :
    ball x (_root_.Metric.infDist x (frontier U)) ⊆ U := by
  let V := _root_.Metric.ball x (_root_.Metric.infDist x (frontier U))
  have hxn : x ∉ frontier U := by
    rw [hU.frontier_eq]
    exact fun h => h.2 hx
  have hd : 0 < _root_.Metric.infDist x (frontier U) :=
    (isClosed_frontier.notMem_iff_infDist_pos hfrontier).mp hxn
  have hdis : Disjoint (frontier U) V := (_root_.Metric.disjoint_ball_infDist (x := x) (s := frontier U)).symm
  let _ : PreconnectedSpace V :=
    Subtype.preconnectedSpace (convex_ball x (_root_.Metric.infDist x (frontier U))).isPreconnected
  have hc : IsClopen (Subtype.val ⁻¹' U : Set V) := isClopen_preimage_val hU hdis
  have he : (Subtype.val ⁻¹' U : Set V) = univ := hc.eq_univ ⟨⟨x, _root_.Metric.mem_ball_self hd⟩, hx⟩
  intro y hy
  have hmem : (⟨y, hy⟩ : V) ∈ (Subtype.val ⁻¹' U : Set V) := he ▸ _root_.Set.mem_univ _
  exact hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ball_infDist_frontier_subset_of_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ball_infDist_frontier_subset_of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ball_infDist_frontier_subset_of_isOpen ``Submission.DifferentialGeometry.Analysis.ball_infDist_frontier_subset_of_isOpen

end DifferentialGeometry.Analysis

end
