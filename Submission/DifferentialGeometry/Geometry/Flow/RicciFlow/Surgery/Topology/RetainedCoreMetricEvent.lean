import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreTower
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventRetainedMaps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

private def retainedToOld (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) :
    C((E.transition.retainedCoreOpens : Type u), E.old) where
  toFun x := ⟨x.1, hOld ▸ x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.retainedToOld
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.retainedToOld target :: scope.openDecls } }

private theorem contMDiff_retainedToOld (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) :
    letI := E.transition.coreOpensCharts E.transition.retainedCoreOpens
    letI := E.oldCharts
    ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ (E.retainedToOld hOld) := by
  let := E.transition.coreOpensCharts E.transition.retainedCoreOpens
  let := E.oldCharts
  let := E.transition.coreCharts
  let := E.transition.coreSmooth
  have hinc := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_restrictOpen
    (𝓡∂ 3) ThreeModel _ E.transition.core_induced E.transition.retainedCoreOpens
  change ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ (E.retainedToOld hOld)
  intro x
  rw [ContMDiffAt.iff_comp_isImmersionAt
    (E.old_induced.isImmersion.isImmersionAt (E.retainedToOld hOld x))]
  exact ⟨(E.retainedToOld hOld).continuous.continuousAt, hinc.contMDiff.contMDiffAt⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.contMDiff_retainedToOld
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.contMDiff_retainedToOld target :: scope.openDecls } }

def retainedOldDiffeomorph (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) :
    letI := E.transition.coreOpensCharts E.transition.retainedCoreOpens
    letI := E.oldCharts
    Diffeomorph (𝓡∂ 3) (𝓡∂ 3) E.transition.retainedCoreOpens E.old ∞ := by
  letI := E.transition.coreOpensCharts E.transition.retainedCoreOpens
  letI := E.oldCharts
  let back : C(E.old, (E.transition.retainedCoreOpens : Type u)) :=
    ⟨fun x => ⟨x.1, by change x.1 ∈ E.transition.trace.retainedCore; rw [← hOld]; exact x.2⟩,
      continuous_subtype_val.subtype_mk (fun x => by
        change x.1 ∈ E.transition.trace.retainedCore
        rw [← hOld]
        exact x.2)⟩
  refine ⟨⟨E.retainedToOld hOld, back, fun _ => rfl, fun _ => rfl⟩,
    E.contMDiff_retainedToOld hOld, ?_⟩
  let := E.transition.coreCharts
  let := E.transition.coreSmooth
  have hinc := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_restrictOpen
    (𝓡∂ 3) ThreeModel _ E.transition.core_induced E.transition.retainedCoreOpens
  change ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ back
  intro x
  rw [ContMDiffAt.iff_comp_isImmersionAt (hinc.isImmersion.isImmersionAt (back x))]
  exact ⟨back.continuous.continuousAt, E.old_induced.contMDiff.contMDiffAt⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.retainedOldDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.retainedOldDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.retainedOldDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.retainedOldDiffeomorph

def toRetainedCoreEvent (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) : RetainedCoreEvent P Q a s where
  discarded := E.discarded
  capped := E.capped
  transition := E.transition
  incoming := E.incoming
  terminal := E.terminal
  outputMetric := E.outputMetric
  oldTerminal := E.oldTerminal.comp (E.retainedToOld hOld)
  oldTerminal_eq := fun x => E.oldTerminal_eq (E.retainedToOld hOld x)
  oldOutput := E.oldOutput.comp (E.retainedToOld hOld)
  oldOutput_eq := fun x => E.oldOutput_eq (E.retainedToOld hOld x)
  old_metric_eq := by
    let := E.transition.coreOpensCharts E.transition.retainedCoreOpens
    let := E.oldCharts
    intro x v w
    have hterminal := E.oldTerminal_isSmoothEmbedding.contMDiff.mdifferentiable (by simp)
    have houtput := E.contMDiff_oldOutput.mdifferentiable (by simp)
    have hmap := (E.contMDiff_retainedToOld hOld).mdifferentiable (by simp)
    change E.terminal.metric.inner _
        (mfderiv (𝓡∂ 3) ThreeModel (E.oldTerminal ∘ E.retainedToOld hOld) x v)
        (mfderiv (𝓡∂ 3) ThreeModel (E.oldTerminal ∘ E.retainedToOld hOld) x w) =
      E.outputMetric.inner _
        (mfderiv (𝓡∂ 3) ThreeModel (E.oldOutput ∘ E.retainedToOld hOld) x v)
        (mfderiv (𝓡∂ 3) ThreeModel (E.oldOutput ∘ E.retainedToOld hOld) x w)
    rw [mfderiv_comp x (hterminal _) (hmap _), mfderiv_comp x (houtput _) (hmap _)]
    exact E.old_metric_eq (E.retainedToOld hOld x) _ _
  old_contains_outside := fun _ hx _ => hx
  every_child_meets_old := by
    intro c
    obtain ⟨x, hx⟩ := E.every_child_meets_old c
    exact ⟨⟨x.1, by change x.1 ∈ E.transition.trace.retainedCore; rw [← hOld]; exact x.2⟩, hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent

@[simp] theorem toRetainedCoreEvent_transition (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) :
    (E.toRetainedCoreEvent hOld).transition = E.transition := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent_transition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent_transition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent_transition ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent_transition

@[simp] theorem toRetainedCoreEvent_incoming (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) :
    (E.toRetainedCoreEvent hOld).incoming = E.incoming := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent_incoming then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent_incoming"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent_incoming ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent_incoming

@[simp] theorem toRetainedCoreEvent_terminal (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) :
    (E.toRetainedCoreEvent hOld).terminal = E.terminal := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent_terminal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent_terminal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent_terminal ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent_terminal

@[simp] theorem toRetainedCoreEvent_outputMetric (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) :
    (E.toRetainedCoreEvent hOld).outputMetric = E.outputMetric := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent_outputMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent_outputMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent_outputMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.toRetainedCoreEvent_outputMetric

theorem regularCrossing_toRetainedCoreEvent_iff (E : MetricCutCapEvent P Q a s)
    (hOld : E.old = E.transition.trace.retainedCore) (p : P.Carrier) (q : Q.Carrier) :
    (E.toRetainedCoreEvent hOld).toMetricCutCapEvent.RegularCrossing p q ↔
      E.RegularCrossing p q := by
  let := E.transition.coreOpensCharts E.transition.retainedCoreOpens
  let := E.oldCharts
  let d := E.retainedOldDiffeomorph hOld
  constructor
  · rintro ⟨x, hx, hp, hq⟩
    refine ⟨d x, ((d.isLocalDiffeomorph x).isInteriorPoint_iff (by simp)).mp hx, ?_, ?_⟩
    · change x.1.1 = p
      exact hp
    · convert hq using 1
      rfl
  · rintro ⟨x, hx, hp, hq⟩
    refine ⟨d.symm x, ((d.symm.isLocalDiffeomorph x).isInteriorPoint_iff (by simp)).mp hx,
      ?_, ?_⟩
    · change x.1.1 = p
      exact hp
    · change E.oldOutput _ = q
      convert hq using 1
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.regularCrossing_toRetainedCoreEvent_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.regularCrossing_toRetainedCoreEvent_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.regularCrossing_toRetainedCoreEvent_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.regularCrossing_toRetainedCoreEvent_iff

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
