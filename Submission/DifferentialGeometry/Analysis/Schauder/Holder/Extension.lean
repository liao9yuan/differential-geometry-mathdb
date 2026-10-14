import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.ExtendFrom
import Mathlib.Topology.UniformSpace.Cauchy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Filter
open scoped _root_.Topology _root_.NNReal

open _root_.HolderOnWith in
theorem HolderOnWith.closure
    {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {s : Set X} {f : X → Y} {K α : ℝ≥0}
    (hf : HolderOnWith K α f s) (hc : ContinuousOn f (_root_.closure s)) :
    HolderOnWith K α f (_root_.closure s) := by
  have := ENNReal.continuous_const_mul (ENNReal.coe_ne_top (r := K))
  have := @ENNReal.continuous_rpow_const (α : ℝ)
  refine fun x hx y hy => le_on_closure
    (fun y hy => le_on_closure (fun x hx => hf x hx y hy) ?_ ?_ hx) ?_ ?_ hy
  all_goals fun_prop

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.HolderOnWith
  let env ← Lean.getEnv
  if env.contains `HolderOnWith.closure then
    throwError "Refusing to shadow existing declaration HolderOnWith.closure"
  Lean.modifyEnv fun env => Lean.addAlias env `HolderOnWith.closure ``Submission.HolderOnWith.closure

private theorem continuousOn_extendFrom_of_uniformContinuousOn
    {X Y : Type*} [UniformSpace X] [UniformSpace Y] [CompleteSpace Y]
    {s : Set X} {f : X → Y} (hf : UniformContinuousOn f s) :
    ContinuousOn (_root_.extendFrom s f) (_root_.closure s) := by
  apply continuousOn_extendFrom Subset.rfl
  intro x hx
  have hn : _root_.Filter.NeBot (𝓝[s] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  exact CompleteSpace.complete ((cauchy_nhds.mono' hn nhdsWithin_le_nhds).map_of_le hf
    inf_le_right)

run_cmd do
  let target := ``Submission.continuousOn_extendFrom_of_uniformContinuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `continuousOn_extendFrom_of_uniformContinuousOn target :: scope.openDecls } }

open _root_.HolderOnWith in
theorem HolderOnWith.extendFrom
    {X Y : Type*} [PseudoEMetricSpace X] [EMetricSpace Y] [CompleteSpace Y]
    {s : Set X} {f : X → Y} {K α : ℝ≥0}
    (hf : HolderOnWith K α f s) (hα : 0 < α) :
    HolderOnWith K α (_root_.extendFrom s f) (_root_.closure s) ∧ _root_.Set.EqOn (_root_.extendFrom s f) f s := by
  have he := extendFrom_extends (hf.continuousOn hα)
  refine ⟨?_, he⟩
  apply HolderOnWith.closure (hc :=
    continuousOn_extendFrom_of_uniformContinuousOn (hf.uniformContinuousOn hα))
  intro x hx y hy
  simpa only [he x hx, he y hy] using hf x hx y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `HolderOnWith.extendFrom then
    throwError "Refusing to shadow existing declaration HolderOnWith.extendFrom"
  Lean.modifyEnv fun env => Lean.addAlias env `HolderOnWith.extendFrom ``Submission.HolderOnWith.extendFrom
