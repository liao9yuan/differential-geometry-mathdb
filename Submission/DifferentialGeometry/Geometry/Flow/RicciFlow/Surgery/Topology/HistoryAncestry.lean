import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Ancestry
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPresentation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory


theorem ancestorRestriction (H : ObservedHistory.{u}) (t : _root_.Set.Icc (0 : ℝ) H.horizon) :
    AncestorRestrictionData (H.restrict t) H where
  count_le := Nat.le_of_lt_succ (H.activeStage t).isLt
  stage_eq _ := rfl
  discarded_eq _ := rfl
  capped_eq _ := rfl
  transition_eq _ := HEq.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.ancestorRestriction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.ancestorRestriction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.ancestorRestriction ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.ancestorRestriction

theorem finite_ancestry_restrict (H : ObservedHistory.{u})
    (t : _root_.Set.Icc (0 : ℝ) H.horizon)
    (terminal : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier) :
    ∀ j : Fin ((H.restrict t).eventCount + 1),
      (rfs_finite_ancestor_chain (H.restrict t)
        ((rfs_finite_ancestor_chain H terminal).component (H.activeStage t))).component j =
      (rfs_finite_ancestor_chain H terminal).component
        (Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (H.activeStage t).isLt) 1) j) := by
  intro j
  induction j using Fin.reverseInduction with
  | last =>
    exact (rfs_finite_ancestor_chain (H.restrict t)
      ((rfs_finite_ancestor_chain H terminal).component (H.activeStage t))).terminal_eq
  | cast j ih =>
    rw [(rfs_finite_ancestor_chain (H.restrict t)
      ((rfs_finite_ancestor_chain H terminal).component (H.activeStage t))).parent_eq, ih]
    exact ((rfs_finite_ancestor_chain H terminal).parent_eq
      (Fin.castLE (Nat.le_of_lt_succ (H.activeStage t).isLt) j)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.finite_ancestry_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.finite_ancestry_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.finite_ancestry_restrict ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.finite_ancestry_restrict

namespace SamePresentation
variable {H K : ObservedHistory.{u}} (R : H.SamePresentation K)


def componentToOther (j : Fin (H.eventCount + 1)) :
    ConnectedComponents (H.stage j).Carrier →
      ConnectedComponents (K.stage (Fin.cast (congrArg (· + 1) R.count_eq) j)).Carrier :=
  fun c => (R.stage_eq j) ▸ c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.componentToOther then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.componentToOther"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.componentToOther ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.componentToOther

private theorem componentToOther_parent (j : Fin H.eventCount)
    (c : ConnectedComponents (H.stage j.succ).Carrier) :
    R.componentToOther j.castSucc ((H.event j).transition.childParent c) =
      (K.event (Fin.cast R.count_eq j)).transition.childParent
        (R.componentToOther j.succ c) :=
  SmoothCutCapTransition.childParent_congr (H.event j).transition
    (K.event (Fin.cast R.count_eq j)).transition
    (R.stage_eq j.castSucc) (R.stage_eq j.succ)
    (R.event_eq j).discarded_eq (R.event_eq j).capped_eq (R.event_eq j).transition_heq c

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.componentToOther_parent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.componentToOther_parent target :: scope.openDecls } }

theorem finite_ancestry
    (terminalH : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier)
    (terminalK : ConnectedComponents (K.stage (Fin.last K.eventCount)).Carrier)
    (hterminal : R.componentToOther (Fin.last H.eventCount) terminalH =
      (rfs_finite_ancestor_chain K terminalK).component
        (Fin.cast (congrArg (· + 1) R.count_eq) (Fin.last H.eventCount))) :
    ∀ j : Fin (H.eventCount + 1), R.componentToOther j
      ((rfs_finite_ancestor_chain H terminalH).component j) =
      (rfs_finite_ancestor_chain K terminalK).component
        (Fin.cast (congrArg (· + 1) R.count_eq) j) := by
  intro j
  induction j using Fin.reverseInduction with
  | last =>
    rw [(rfs_finite_ancestor_chain H terminalH).terminal_eq]
    exact hterminal
  | cast j ih =>
    rw [(rfs_finite_ancestor_chain H terminalH).parent_eq, R.componentToOther_parent, ih]
    exact ((rfs_finite_ancestor_chain K terminalK).parent_eq (Fin.cast R.count_eq j)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.finite_ancestry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.finite_ancestry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.finite_ancestry ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.finite_ancestry

end SamePresentation
end ObservedHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
