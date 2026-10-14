import Mathlib.Topology.SeparatedMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter
open scoped _root_.Topology

open _root_.IsLocallyInjective in
theorem IsLocallyInjective.eventuallyEq_of_comp_eventuallyEq
    {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {π : β → γ} (hπ : IsLocallyInjective π)
    {f g : α → β} {x : α} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hx : f x = g x) (heq : (π ∘ f) =ᶠ[𝓝 x] (π ∘ g)) : f =ᶠ[𝓝 x] g := by
  obtain ⟨U, hU, hxU, hUinj⟩ := hπ (f x)
  have hfU : ∀ᶠ y in 𝓝 x, f y ∈ U := hf (hU.mem_nhds hxU)
  have hgU : ∀ᶠ y in 𝓝 x, g y ∈ U := hg (hU.mem_nhds (hx ▸ hxU))
  filter_upwards [hfU, hgU, heq] with y hyf hyg hyeq
  exact hUinj hyf hyg hyeq

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.IsLocallyInjective
  let env ← Lean.getEnv
  if env.contains `IsLocallyInjective.eventuallyEq_of_comp_eventuallyEq then
    throwError "Refusing to shadow existing declaration IsLocallyInjective.eventuallyEq_of_comp_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `IsLocallyInjective.eventuallyEq_of_comp_eventuallyEq ``Submission.IsLocallyInjective.eventuallyEq_of_comp_eventuallyEq
