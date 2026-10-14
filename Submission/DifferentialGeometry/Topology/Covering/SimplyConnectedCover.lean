import Mathlib.Topology.Homotopy.Lifting

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace IsCoveringMap
open _root_.IsCoveringMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y]
  {f : X → Y}

open _root_.IsCoveringMap in
theorem exists_continuousMap_inverse_of_simplyConnected
    [PreconnectedSpace X] (hf : IsCoveringMap f) (x₀ : X) :
    ∃ g : C(Y, X), Function.LeftInverse g f ∧ Function.RightInverse g f := by
  obtain ⟨g, ⟨hg₀, hfg⟩, _⟩ :=
    hf.existsUnique_continuousMap_lifts (ContinuousMap.id Y) (f x₀) x₀ rfl
  have hright : Function.RightInverse g f := by
    intro y
    exact congrFun hfg y
  have hgf : (g : Y → X) ∘ f = id :=
    hf.eq_of_comp_eq (g.continuous.comp hf.continuous) continuous_id
      (by
        funext x
        exact hright (f x)) x₀ hg₀
  exact ⟨g, (fun x => congrFun hgf x), hright⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoveringMap.exists_continuousMap_inverse_of_simplyConnected then
    throwError "Refusing to shadow existing declaration IsCoveringMap.exists_continuousMap_inverse_of_simplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoveringMap.exists_continuousMap_inverse_of_simplyConnected ``Submission.IsCoveringMap.exists_continuousMap_inverse_of_simplyConnected

open _root_.IsCoveringMap in
theorem bijective_of_simplyConnected [ConnectedSpace X]
    (hf : IsCoveringMap f) : Function.Bijective f := by
  obtain ⟨g, hleft, hright⟩ := hf.exists_continuousMap_inverse_of_simplyConnected
    (Classical.choice (inferInstance : Nonempty X))
  exact ⟨hleft.injective, fun y => ⟨g y, hright y⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoveringMap.bijective_of_simplyConnected then
    throwError "Refusing to shadow existing declaration IsCoveringMap.bijective_of_simplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoveringMap.bijective_of_simplyConnected ``Submission.IsCoveringMap.bijective_of_simplyConnected

open _root_.IsCoveringMap in
theorem injective_of_simplyConnected [ConnectedSpace X]
    (hf : IsCoveringMap f) : Function.Injective f :=
  hf.bijective_of_simplyConnected.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoveringMap.injective_of_simplyConnected then
    throwError "Refusing to shadow existing declaration IsCoveringMap.injective_of_simplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoveringMap.injective_of_simplyConnected ``Submission.IsCoveringMap.injective_of_simplyConnected

open _root_.IsCoveringMap in
noncomputable def homeomorphOfSimplyConnected [ConnectedSpace X]
    (hf : IsCoveringMap f) : X ≃ₜ Y := by
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  let g := Classical.choose (hf.exists_continuousMap_inverse_of_simplyConnected x₀)
  have hg := Classical.choose_spec (hf.exists_continuousMap_inverse_of_simplyConnected x₀)
  exact
    { toFun := f
      invFun := g
      left_inv := hg.1
      right_inv := hg.2
      continuous_toFun := hf.continuous
      continuous_invFun := g.continuous }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoveringMap.homeomorphOfSimplyConnected then
    throwError "Refusing to shadow existing declaration IsCoveringMap.homeomorphOfSimplyConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoveringMap.homeomorphOfSimplyConnected ``Submission.IsCoveringMap.homeomorphOfSimplyConnected


open _root_.IsCoveringMap in
@[simp] theorem homeomorphOfSimplyConnected_apply [ConnectedSpace X]
    (hf : IsCoveringMap f) (x : X) :
    hf.homeomorphOfSimplyConnected x = f x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCoveringMap.homeomorphOfSimplyConnected_apply then
    throwError "Refusing to shadow existing declaration IsCoveringMap.homeomorphOfSimplyConnected_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCoveringMap.homeomorphOfSimplyConnected_apply ``Submission.IsCoveringMap.homeomorphOfSimplyConnected_apply

end IsCoveringMap
