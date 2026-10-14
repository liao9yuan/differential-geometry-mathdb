import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorLocalFlow
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Seam
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalClosedSolution
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpenIncoming : SigmaCompactSpace E.incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      E.incoming.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpenIncoming
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpenIncoming target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierMemOpensTerminalRegularOpenIncoming : IsManifold ThreeModel 1 E.incoming.terminalRegularOpen :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierMemOpensTerminalRegularOpenIncoming
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierMemOpensTerminalRegularOpenIncoming target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierMemOpensTerminalRegularOpenIncoming_1 (W : TopologicalSpace.Opens E.incoming.terminalRegularOpen) :
    IsManifold ThreeModel 1 W := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierMemOpensTerminalRegularOpenIncoming_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatSubtypeCarrierMemOpensTerminalRegularOpenIncoming_1 target :: scope.openDecls } }


theorem exists_survivor_solution_across_event
    (G : Q.IncomingSlab s b) (hmetric : G.flow.base.metric s = E.outputMetric)
    (W : TopologicalSpace.Opens E.incoming.terminalRegularOpen) (x₀ : W)
    (hW : ∀ x ∈ W, x.val ∈ interior (Subtype.val '' E.old))
    {c d : ℝ} (hac : a ≤ c) (hcs : c < s) (hsd : s < d) (hdb : d < b) :
    letI : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)
    ∃ (F : PartialDiffeomorph ThreeModel ThreeModel
          E.incoming.terminalRegularOpen Q.Carrier ∞)
      (S : SolutionOn (I := ThreeModel) (M := W) (RealTimeInterval.closedOpen s b G.lt)),
      F.source = W ∧ IsSolutionOn S ∧
      (∀ x ∈ W, E.RegularCrossing x.val (F x)) ∧
      S.base.metric s = E.terminal.metric.restrictOpen W ∧
      (∀ t (x : W) (v w : TangentSpace ThreeModel x),
        (S.base.metric t).inner x v w =
          (G.flow.base.metric t).inner (F x)
            (mfderiv ThreeModel ThreeModel F x v) (mfderiv ThreeModel ThreeModel F x w)) ∧
      IsSolutionOn (E.terminal.closedSolution W hcs.le) ∧
      IsSolutionOn ({ base := { metric := fun t =>
          if t ≤ s then (E.terminal.extendedMetric t).restrictOpen W else S.base.metric t } } :
        SolutionOn (I := ThreeModel) (M := W)
          (RealTimeInterval.closed c d (hcs.trans hsd).le)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
        (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
        (fun q : ℝ × W =>
          (⟨q.2, ((if q.1 ≤ s then (E.terminal.extendedMetric q.1).restrictOpen W
            else S.base.metric q.1)).inner q.2⟩ :
            _root_.Bundle.TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
              (fun x => TangentSpace ThreeModel x →L[ℝ]
                TangentSpace ThreeModel x →L[ℝ] ℝ)))
        (_root_.Set.Icc c d ×ˢ (_root_.Set.univ : Set W)) ∧
      ∀ m : ℕ, ∀ x : W,
        iteratedDerivWithin m
          (fun t => Tensor0SBundle.metricTensorField
            ((E.terminal.extendedMetric t).restrictOpen W) x) (_root_.Set.Icc c s) s =
        iteratedDerivWithin m
          (fun t => Tensor0SBundle.metricTensorField (S.base.metric t) x) (_root_.Set.Icc s d) s := by
  let : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)
  obtain ⟨F, S, hsource, hS, hcross, hstart, hpull⟩ :=
    E.exists_survivor_local_flow G hmetric W x₀ hW
  let gL := fun t => (E.terminal.extendedMetric t).restrictOpen W
  have hleft : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × W => (⟨q.2, (gL q.1).inner q.2⟩ :
        _root_.Bundle.TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ]
            TangentSpace ThreeModel x →L[ℝ] ℝ))) (_root_.Set.Icc c s ×ˢ _root_.Set.univ) :=
    E.terminal.extendedMetric_restrictOpen_jointContMDiffOn W hac hcs
  have hright : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun q : ℝ × W => (⟨q.2, (S.base.metric q.1).inner q.2⟩ :
        _root_.Bundle.TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ]
            TangentSpace ThreeModel x →L[ℝ] ℝ))) (_root_.Set.Icc s d ×ˢ _root_.Set.univ) := by
    have hFsmooth : ContMDiff ThreeModel ThreeModel ∞ (fun x : W => F x.val) :=
      F.contMDiffOn.comp_contMDiff contMDiff_subtype_val (by
        intro x
        rw [hsource]
        exact x.property)
    apply metricCLMSection_jointContMDiffOn_of_chartGram_on S.base.metric (_root_.Set.Icc s d)
    intro p i j
    apply chartGramMatrix_joint_contMDiffOn_of_pullback G.flow.base.metric (_root_.Set.Icc s d)
      (G.smoothUpTo.jointContMDiffOn.mono (fun q hq =>
        ⟨⟨hq.1.1, hq.1.2.trans_lt hdb⟩, hq.2⟩)) S.base.metric
      (fun x : W => F x.val) hFsmooth
    intro t ht x v w
    have hd := mfderiv_restrict_open (I := ThreeModel) (J := ThreeModel)
      (F : E.incoming.terminalRegularOpen → Q.Carrier) W x
    have hv := DFunLike.congr_fun hd v
    have hw := DFunLike.congr_fun hd w
    exact (hpull t x v w).trans
      (congrArg₂ (fun v w : ThreeSpace => (G.flow.base.metric t).inner (F x) v w)
        hv.symm hw.symm)
  have hpdeL : ∀ t ∈ _root_.Set.Ioo c s, ∀ x : W, ∀ v w : TangentSpace ThreeModel x,
      HasDerivAt (fun u => (gL u).inner x v w) (-2 * ricciTensor (gL t) x v w) t := by
    intro t ht x v w
    exact E.terminal.extendedMetric_restrictOpen_hasDerivAt W
      ⟨hac.trans_lt ht.1, ht.2⟩ x v w
  have hpdeR : ∀ t ∈ _root_.Set.Ioo s d, ∀ x : W, ∀ v w : TangentSpace ThreeModel x,
      HasDerivAt (fun u => (S.base.metric u).inner x v w)
        (-2 * ricciTensor (S.base.metric t) x v w) t := by
    intro t ht x v w
    have hd := metricDerivAt S hS ⟨t, ⟨ht.1, ht.2.trans hdb⟩⟩ x v w
    have hr := metricRicciAt_apply_eq_ricciTensor (S.base.metric t) x v w
    dsimp only [SolutionOn.ricciAt, SolutionFamily.ricciAt] at hd
    erw [hr] at hd
    exact hd
  have hmatch : gL s = S.base.metric s := by
    simpa only [gL, OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal]
      using hstart.symm
  exact ⟨F, S, hsource, hS, hcross, hstart, hpull,
    E.terminal.closedSolution_isSolutionOn W hac hcs,
    isSolutionOn_ite_of_ricciFlow gL S.base.metric hcs hsd hleft hright hpdeL hpdeR hmatch,
    metricCLMSection_jointContMDiffOn_ite_of_ricciFlow gL S.base.metric
      hcs hsd hleft hright hpdeL hpdeR hmatch,
    fun m x => metricTensorField_iteratedDerivWithin_eq_of_ricciFlow gL S.base.metric
      hcs hsd hleft hright hpdeL hpdeR hmatch m x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_survivor_solution_across_event then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_survivor_solution_across_event"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_survivor_solution_across_event ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_survivor_solution_across_event

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
