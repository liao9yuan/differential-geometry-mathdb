import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalMetricCompactComparison
import Submission.DifferentialGeometry.Geometry.Curvature.MetricDifference
import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Convergence
import Submission.DifferentialGeometry.Geometry.Curvature.OperatorNaturality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.tendsto_inner (L : G.TerminalLimitMetric)
    (x : G.terminalRegularOpen) (v w : TangentSpace ThreeModel x) :
    _root_.Filter.Tendsto (fun t => ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen).inner x v w)
      (𝓝[<] s) (𝓝 (L.metric.inner x v w)) := by
  let A := Real.sqrt (L.metric.inner x v v) * Real.sqrt (L.metric.inner x w w)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨d, hd, hbound⟩ := L.converges {x} isCompact_singleton 0 (ε / (A + 1))
    (div_pos hε (by linarith))
  filter_upwards [Ioo_mem_nhdsLT hd.2] with t ht
  have hdiff := metricDifference_abs_le
    ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) L.metric L.metric x v w
  have hb := (hbound t ht x (_root_.Set.mem_singleton x)).le
  have hmul := mul_le_mul_of_nonneg_right hb hA
  have hh : ε / (A + 1) * A < ε := by
    have h := (div_mul_cancel₀ ε (by linarith : A + 1 ≠ 0))
    have hp : 0 < ε / (A + 1) := div_pos hε (by linarith)
    nlinarith
  rw [Real.dist_eq]
  exact hdiff.trans_lt (by simpa only [mul_assoc, A] using hmul.trans_lt hh)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.tendsto_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.tendsto_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.tendsto_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.tendsto_inner

theorem TerminalLimitMetric.tendsto_metricRm04StandardAt (L : G.TerminalLimitMetric)
    (x : G.terminalRegularOpen) (v w u z : TangentSpace ThreeModel x) :
    _root_.Filter.Tendsto (fun t => metricRm04StandardAt
      ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) x v w u z)
      (𝓝[<] s) (𝓝 (metricRm04StandardAt L.metric x v w u z)) := by
  let A := Real.sqrt (L.metric.inner x z z) *
      Real.sqrt (L.metric.inner x (riemannOp (cov := LeviCivita L.metric) x v w u)
        (riemannOp (cov := LeviCivita L.metric) x v w u)) +
      864 * Real.sqrt (L.metric.inner x v v) * Real.sqrt (L.metric.inner x w w) *
        Real.sqrt (L.metric.inner x u u) * Real.sqrt (L.metric.inner x z z)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := _root_.Min.min (1 / 6) (ε / (A + 1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by linarith))
  have hδ6 : δ ≤ 1 / 6 := min_le_left _ _
  have hδA : δ * A < ε := by
    have hb : δ ≤ ε / (A + 1) := min_le_right _ _
    have hm := (le_div_iff₀ (by linarith : 0 < A + 1)).mp hb
    nlinarith
  obtain ⟨d0, hd0, hb0⟩ := L.converges {x} isCompact_singleton 0 δ hδ
  obtain ⟨d1, hd1, hb1⟩ := L.converges {x} isCompact_singleton 1 δ hδ
  obtain ⟨d2, hd2, hb2⟩ := L.converges {x} isCompact_singleton 2 δ hδ
  filter_upwards [Ioo_mem_nhdsLT (max_lt hd0.2 (max_lt hd1.2 hd2.2))] with t ht
  have hjet : ∀ k ≤ 2, metricDerivNorm k
      ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) L.metric L.metric x ≤ δ := by
    intro k hk
    interval_cases k
    · exact (hb0 t ⟨(le_max_left _ _).trans_lt ht.1, ht.2⟩ x (_root_.Set.mem_singleton x)).le
    · exact (hb1 t ⟨((le_max_left _ _).trans (le_max_right _ _)).trans_lt ht.1, ht.2⟩ x (_root_.Set.mem_singleton x)).le
    · exact (hb2 t ⟨((le_max_right _ _).trans (le_max_right _ _)).trans_lt ht.1, ht.2⟩ x (_root_.Set.mem_singleton x)).le
  have hn : (Module.finrank ℝ ThreeSpace : ℝ) * δ ≤ 1 / 2 := by
    simp only [ThreeSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat]
    linarith
  have hb := metricRm04_difference_le_of_metricDerivNorm_le L.metric
    ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) x hδ.le
    (by linarith) hn hjet v w u z
  rw [Real.dist_eq]
  exact hb.trans_lt hδA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.tendsto_metricRm04StandardAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.tendsto_metricRm04StandardAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.tendsto_metricRm04StandardAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.tendsto_metricRm04StandardAt

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open _root_.Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.tendsto_leastCurvatureOperatorEigenvalueAt
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen) :
    _root_.Filter.Tendsto (fun t => leastCurvatureOperatorEigenvalueAt (G.flow.base.metric t) x.1
      (metricAlgebraicCurvatureTensorAt (G.flow.base.metric t) x.1)) (𝓝[<] s)
      (𝓝 (leastCurvatureOperatorEigenvalueAt L.metric x (metricAlgebraicCurvatureTensorAt L.metric x))) := by
  let : SecondCountableTopology P.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier
  let : LocallyCompactSpace G.terminalRegularOpen :=
    ChartedSpace.locallyCompactSpace ThreeSpace G.terminalRegularOpen
  let : SigmaCompactSpace G.terminalRegularOpen := inferInstance
  let g (t : ℝ) := (G.flow.base.metric t).restrictOpen G.terminalRegularOpen
  have hg : ∀ v w : TangentSpace ThreeModel x,
      Tendsto (fun t => (g t).inner x v w) (𝓝[<] s) (𝓝 (L.metric.inner x v w)) :=
    L.tendsto_inner x
  have hA : ∀ v w u z : TangentSpace ThreeModel x,
      _root_.Filter.Tendsto (fun t => tensor04StandardAt (metricAlgebraicCurvatureTensorAt (g t) x).1 v w u z)
        (𝓝[<] s) (𝓝 (tensor04StandardAt (metricAlgebraicCurvatureTensorAt L.metric x).1 v w u z)) :=
    L.tendsto_metricRm04StandardAt x
  have h := leastCurvatureOperatorEigenvalueAt_tendsto_of_components
    (I := ThreeModel) (g := g) (A := fun t => metricAlgebraicCurvatureTensorAt (g t) x)
    (by simp [ThreeSpace]) L.metric x (metricAlgebraicCurvatureTensorAt L.metric x) hg hA
  simpa only [g, leastCurvatureOperatorEigenvalueAt_restrictOpen] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.tendsto_leastCurvatureOperatorEigenvalueAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.tendsto_leastCurvatureOperatorEigenvalueAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.tendsto_leastCurvatureOperatorEigenvalueAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.tendsto_leastCurvatureOperatorEigenvalueAt

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
