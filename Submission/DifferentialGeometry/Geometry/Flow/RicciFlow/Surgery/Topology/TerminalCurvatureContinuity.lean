import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CurvatureContinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalClosedSolution
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierMemOpensTerminalRegularOpen : IsManifold ThreeModel 1 G.terminalRegularOpen :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierMemOpensTerminalRegularOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierMemOpensTerminalRegularOpen target :: scope.openDecls } }

private theorem TerminalLimitMetric.closedSolution_riemannNorm
    (L : G.TerminalLimitMetric) {c : ℝ} (hcs : c ≤ s) (t : ℝ)
    (x : G.terminalRegularOpen) :
    Real.sqrt (normSq0S ((L.closedSolution ⊤ hcs).base.metric t)
      (⟨x, _root_.Set.mem_univ x⟩ : (⊤ : TopologicalSpace.Opens G.terminalRegularOpen)) 4
      ((L.closedSolution ⊤ hcs).base.rm04 t ⟨x, _root_.Set.mem_univ x⟩)) =
      Real.sqrt (normSq0S (L.extendedMetric t) x 4 (metricRm04At (L.extendedMetric t) x)) := by
  simp only [SolutionFamily.rm04, metricRm04_apply, L.closedSolution_metric]
  rw [rmNormSq_restrictOpen]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_riemannNorm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_riemannNorm target :: scope.openDecls } }

private theorem TerminalLimitMetric.extendedMetric_riemannNorm_before
    (L : G.TerminalLimitMetric) {t : ℝ} (ht : t < s) (x : G.terminalRegularOpen) :
    Real.sqrt (normSq0S (L.extendedMetric t) x 4 (metricRm04At (L.extendedMetric t) x)) =
      G.riemannNorm t x.val := by
  rw [L.extendedMetric_before ht, rmNormSq_restrictOpen]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_riemannNorm_before
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_riemannNorm_before target :: scope.openDecls } }

theorem TerminalLimitMetric.tendsto_riemannNorm
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen) :
    _root_.Filter.Tendsto (fun t => G.riemannNorm t x.val) (𝓝[<] s)
      (𝓝 (Real.sqrt (normSq0S L.metric x 4 (metricRm04At L.metric x)))) := by
  let W : TopologicalSpace.Opens G.terminalRegularOpen := ⊤
  let xW : W := ⟨x, _root_.Set.mem_univ x⟩
  have hc := (L.closedSolution_isSolutionOn W le_rfl G.lt).continuousOn_riemannNorm_time xW
  have hci := hc s (show s ∈ (RealTimeInterval.closed a s G.lt.le).carrier from ⟨G.lt.le, le_rfl⟩)
  have hlim := hci.mono_left (nhdsWithin_mono s _root_.Set.Ioo_subset_Icc_self)
  rw [nhdsWithin_Ioo_eq_nhdsLT G.lt] at hlim
  change _root_.Filter.Tendsto (fun t => Real.sqrt (normSq0S ((L.closedSolution ⊤ G.lt.le).base.metric t)
      xW 4 ((L.closedSolution ⊤ G.lt.le).base.rm04 t xW))) (𝓝[<] s)
      (𝓝 (Real.sqrt (normSq0S ((L.closedSolution ⊤ G.lt.le).base.metric s)
        xW 4 ((L.closedSolution ⊤ G.lt.le).base.rm04 s xW)))) at hlim
  simp only [xW, W, L.closedSolution_riemannNorm, L.extendedMetric_terminal] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact L.extendedMetric_riemannNorm_before ht x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.tendsto_riemannNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.tendsto_riemannNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.tendsto_riemannNorm ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.tendsto_riemannNorm

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
