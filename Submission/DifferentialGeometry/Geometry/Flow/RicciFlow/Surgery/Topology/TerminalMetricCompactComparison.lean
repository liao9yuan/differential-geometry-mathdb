import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage.IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.exists_compact_relative_quad_bound (L : G.TerminalLimitMetric)
    {K : Set G.terminalRegularOpen} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ d ∈ _root_.Set.Ico a s, ∀ t ∈ _root_.Set.Ioo d s, ∀ x ∈ K, ∀ v : TangentSpace ThreeModel x,
      |((G.flow.base.metric t).restrictOpen G.terminalRegularOpen).inner x v v -
        L.metric.inner x v v| ≤ ε *
        ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen).inner x v v := by
  let : SecondCountableTopology P.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier
  let : LocallyCompactSpace G.terminalRegularOpen :=
    ChartedSpace.locallyCompactSpace ThreeSpace G.terminalRegularOpen
  have he : 0 < 1 + ε := by linarith
  obtain ⟨d, hd, hbound⟩ := L.converges K hK 0 (ε / (1 + ε)) (div_pos hε he)
  refine ⟨d, hd, ?_⟩
  intro t ht x hx v
  let gt := (G.flow.base.metric t).restrictOpen G.terminalRegularOpen
  have herr := DifferentialGeometry.CheegerGromovCompactness.metricDifference_abs_le
    gt L.metric L.metric x v v
  rw [mul_assoc, Real.mul_self_sqrt (DifferentialGeometry.metric_inner_self_nonneg
    L.metric x v)] at herr
  have herr' := herr.trans (mul_le_mul_of_nonneg_right (hbound t ht x hx).le
    (DifferentialGeometry.metric_inner_self_nonneg L.metric x v))
  have heq : (1 + ε) * (ε / (1 + ε)) = ε := by
    field_simp
  have hnorm : |gt.inner x v v - L.metric.inner x v v| ≤ ε * gt.inner x v v := by
    have habs : 0 ≤ |gt.inner x v v - L.metric.inner x v v| := abs_nonneg _
    have hscaled := mul_le_mul_of_nonneg_left herr' he.le
    rw [← mul_assoc, heq] at hscaled
    have hless : L.metric.inner x v v - gt.inner x v v ≤
        |gt.inner x v v - L.metric.inner x v v| := by
      linarith [neg_abs_le (gt.inner x v v - L.metric.inner x v v)]
    nlinarith
  exact hnorm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_compact_relative_quad_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_compact_relative_quad_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_compact_relative_quad_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_compact_relative_quad_bound

theorem TerminalLimitMetric.exists_compact_quad_bound (L : G.TerminalLimitMetric)
    {K : Set G.terminalRegularOpen} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ d ∈ _root_.Set.Ico a s, ∀ t ∈ _root_.Set.Ioo d s, ∀ x ∈ K, ∀ v : TangentSpace ThreeModel x,
      L.metric.inner x v v ≤ (1 + ε) *
        ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen).inner x v v := by
  obtain ⟨d, hd, hbound⟩ := L.exists_compact_relative_quad_bound hK hε
  refine ⟨d, hd, ?_⟩
  intro t ht x hx v
  have h := (abs_le.mp (hbound t ht x hx v)).1
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_compact_quad_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_compact_quad_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_compact_quad_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_compact_quad_bound

end OrientedThreeStage.IncomingSlab

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
