import Mathlib.Topology.Maps.Proper.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter
open scoped _root_.Topology

open _root_.IsProperMap in
theorem IsProperMap.of_eventuallyEq_cocompact {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f g : X → Y} (hf : IsProperMap f) (hg : Continuous g)
    (heq : g =ᶠ[_root_.Filter.cocompact X] f) : IsProperMap g := by
  obtain ⟨K, hK, hKeq⟩ := mem_cocompact.mp heq
  rw [isProperMap_iff_ultrafilter_of_t2]
  refine ⟨hg, ?_⟩
  intro U y hy
  by_cases hUK : K ∈ U
  · obtain ⟨x, _, hx⟩ := hK.ultrafilter_le_nhds' U hUK
    exact ⟨x, hx⟩
  · have hUKc : Kᶜ ∈ U := Ultrafilter.compl_mem_iff_notMem.mpr hUK
    have heqU : g =ᶠ[U] f := by
      filter_upwards [hUKc] with x hx
      exact hKeq hx
    obtain ⟨x, _, hx⟩ := hf.ultrafilter_le_nhds_of_tendsto (hy.congr' heqU)
    exact ⟨x, hx⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.IsProperMap
  let env ← Lean.getEnv
  if env.contains `IsProperMap.of_eventuallyEq_cocompact then
    throwError "Refusing to shadow existing declaration IsProperMap.of_eventuallyEq_cocompact"
  Lean.modifyEnv fun env => Lean.addAlias env `IsProperMap.of_eventuallyEq_cocompact ``Submission.IsProperMap.of_eventuallyEq_cocompact
