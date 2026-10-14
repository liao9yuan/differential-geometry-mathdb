import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalTimeExtension
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.JointRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedIntervalDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen_1 (W : TopologicalSpace.Opens G.terminalRegularOpen) : SigmaCompactSpace W :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen_1 target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierMemOpensTerminalRegularOpen : IsManifold ThreeModel 1 G.terminalRegularOpen :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierMemOpensTerminalRegularOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierMemOpensTerminalRegularOpen target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierMemOpensTerminalRegularOpen_1 (W : TopologicalSpace.Opens G.terminalRegularOpen) : IsManifold ThreeModel 1 W :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierMemOpensTerminalRegularOpen_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierMemOpensTerminalRegularOpen_1 target :: scope.openDecls } }


theorem TerminalLimitMetric.extendedMetric_restrictOpen_jointContMDiffOn
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c : ℝ} (hac : a ≤ c) (hcs : c < s) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × W => (⟨q.2, ((L.extendedMetric q.1).restrictOpen W).inner q.2⟩ :
        _root_.Bundle.TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (_root_.Set.Icc c s ×ˢ _root_.Set.univ) := by
  apply metricCLMSection_jointContMDiffOn_of_chartGram_on
    (fun t => (L.extendedMetric t).restrictOpen W) (_root_.Set.Icc c s)
  intro p i j
  refine chartGramMatrix_joint_contMDiffOn_of_pullback L.extendedMetric (_root_.Set.Icc c s)
    (L.extendedMetric_jointContMDiffOn hac hcs) (fun t => (L.extendedMetric t).restrictOpen W)
    Subtype.val contMDiff_subtype_val ?_ p i j
  intro t _ x v w
  simp only [SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_restrictOpen_jointContMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_restrictOpen_jointContMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_restrictOpen_jointContMDiffOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_restrictOpen_jointContMDiffOn

theorem TerminalLimitMetric.extendedMetric_restrictOpen_hasDerivAt
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {t : ℝ} (ht : t ∈ _root_.Set.Ioo a s) (x : W) (v w : TangentSpace ThreeModel x) :
    HasDerivAt (fun u => ((L.extendedMetric u).restrictOpen W).inner x v w)
      (-2 * ricciTensor ((L.extendedMetric t).restrictOpen W) x v w) t := by
  have hd := L.extendedMetric_hasDerivAt ht x.val v w
  rw [Geometry.Curvature.ricciTensor_restrictOpen]
  simpa only [SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply] using hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_restrictOpen_hasDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_restrictOpen_hasDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_restrictOpen_hasDerivAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_restrictOpen_hasDerivAt

def TerminalLimitMetric.closedSolution
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c : ℝ} (hcs : c ≤ s) : SolutionOn (I := ThreeModel) (M := W)
      (RealTimeInterval.closed c s hcs) where
  base := { metric := fun t => (L.extendedMetric t).restrictOpen W }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution

@[simp] theorem TerminalLimitMetric.closedSolution_metric
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c : ℝ} (hcs : c ≤ s) (t : ℝ) :
    (L.closedSolution W hcs).base.metric t = (L.extendedMetric t).restrictOpen W := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_metric

theorem TerminalLimitMetric.closedSolution_before
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c : ℝ} (hcs : c ≤ s) {t : ℝ} (ht : t < s) :
    (L.closedSolution W hcs).base.metric t =
      ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen).restrictOpen W := by
  rw [L.closedSolution_metric, L.extendedMetric_before ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_before then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_before"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_before ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_before

theorem TerminalLimitMetric.closedSolution_terminal
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c : ℝ} (hcs : c ≤ s) :
    (L.closedSolution W hcs).base.metric s = L.metric.restrictOpen W := by
  rw [L.closedSolution_metric, L.extendedMetric_terminal]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_terminal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_terminal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_terminal ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_terminal

theorem TerminalLimitMetric.closedSolution_isSolutionOn
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c : ℝ} (hac : a ≤ c) (hcs : c < s) : IsSolutionOn (L.closedSolution W hcs.le) := by
  apply isSolutionOn_of_joint_metric (RealTimeInterval.closed c s hcs.le)
    (uniqueDiffOn_Icc hcs) (fun t => (L.extendedMetric t).restrictOpen W)
    (L.extendedMetric_restrictOpen_jointContMDiffOn W hac hcs)
  intro t ht x v w
  exact (L.extendedMetric_restrictOpen_hasDerivAt W
    ⟨hac.trans_lt ht.1, ht.2⟩ x v w).hasDerivWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_isSolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_isSolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_isSolutionOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_isSolutionOn

theorem TerminalLimitMetric.extendedMetric_restrictOpen_hasDerivWithinAt
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c t : ℝ} (hac : a ≤ c) (hcs : c < s) (ht : t ∈ _root_.Set.Icc c s)
    (x : W) (v w : TangentSpace ThreeModel x) :
    HasDerivWithinAt (fun u => ((L.extendedMetric u).restrictOpen W).inner x v w)
      (-2 * ricciTensor ((L.extendedMetric t).restrictOpen W) x v w) (_root_.Set.Icc c s) t := by
  have hd := metric_inner_hasDerivWithinAt_on_closed_interval (L.closedSolution W hcs.le)
    (L.closedSolution_isSolutionOn W hac hcs) hcs Subset.rfl Subset.rfl ht x v w
  have hr := metricRicciAt_apply_eq_ricciTensor ((L.extendedMetric t).restrictOpen W) x v w
  dsimp only [SolutionOn.ricciAt, SolutionFamily.ricciAt, closedSolution] at hd
  erw [hr] at hd
  exact hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_restrictOpen_hasDerivWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_restrictOpen_hasDerivWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_restrictOpen_hasDerivWithinAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_restrictOpen_hasDerivWithinAt


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end

noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.closedSolution_chartGram_spatial_fderiv_continuousOn
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c : ℝ} (hac : a ≤ c) (hcs : c < s) (p : W) :
    ContinuousOn (fun z : ℝ × ThreeSpace => fderiv ℝ
      (fun y : ThreeSpace => chartGramOp (I := ThreeModel) (L.closedSolution W hcs.le).family p (z.1, y)) z.2)
      (_root_.Set.Icc c s ×ˢ interior (extChartAt ThreeModel p).target) := by
  exact (L.closedSolution W hcs.le).chartGram_spatial_fderiv_continuousOn_of_joint_metric
    (_root_.Set.Icc c s) (L.extendedMetric_restrictOpen_jointContMDiffOn W hac hcs) p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_chartGram_spatial_fderiv_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_chartGram_spatial_fderiv_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_chartGram_spatial_fderiv_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_chartGram_spatial_fderiv_continuousOn

theorem TerminalLimitMetric.closedSolution_scalarOnE_spatial_fderiv_continuousOn
    (L : G.TerminalLimitMetric) (W : TopologicalSpace.Opens G.terminalRegularOpen)
    {c : ℝ} (hac : a ≤ c) (hcs : c < s) (p : W) :
    ContinuousOn (fun z : ℝ × ThreeSpace => fderiv ℝ
      (DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := ThreeModel) p
        ((L.closedSolution W hcs.le).scalar z.1)) z.2)
      (_root_.Set.Icc c s ×ˢ interior (extChartAt ThreeModel p).target) := by
  exact (L.closedSolution W hcs.le).scalarOnE_spatial_fderiv_continuousOn_of_joint_metric
    (_root_.Set.Icc c s) (L.extendedMetric_restrictOpen_jointContMDiffOn W hac hcs) p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_scalarOnE_spatial_fderiv_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_scalarOnE_spatial_fderiv_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_scalarOnE_spatial_fderiv_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_scalarOnE_spatial_fderiv_continuousOn

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

end
