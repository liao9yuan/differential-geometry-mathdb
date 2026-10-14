import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Logic.Small.Set
import Mathlib.Data.Countable.Small

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

universe u v w

open _root_.ChartedSpace in
theorem ChartedSpace.small_of_lindelofSpace (H : Type u) [TopologicalSpace H] [Small.{w} H]
    (M : Type v) [TopologicalSpace M] [ChartedSpace H M] [LindelofSpace M] : Small.{w} M := by
  have hsmall (x : M) : Small.{w} (chartAt H x).source := by
    apply small_of_injective (f := fun y : (chartAt H x).source => chartAt H x y)
    intro a b hab
    exact Subtype.ext ((chartAt H x).injOn a.property b.property hab)
  let _ := hsmall
  obtain ⟨t, htc, ht⟩ := LindelofSpace.elim_nhds_subcover
    (fun x : M => (chartAt H x).source) (chart_source_mem_nhds H)
  let _ : Countable t := htc.to_subtype
  have hs : Small.{w} (⋃ x ∈ t, (chartAt H x).source) := by
    exact small_biUnion.{w} t (fun x _ => (chartAt H x).source)
  rw [ht] at hs
  exact small_univ_iff.mp hs

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ChartedSpace
  let env ← Lean.getEnv
  if env.contains `ChartedSpace.small_of_lindelofSpace then
    throwError "Refusing to shadow existing declaration ChartedSpace.small_of_lindelofSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `ChartedSpace.small_of_lindelofSpace ``Submission.ChartedSpace.small_of_lindelofSpace

open _root_.ChartedSpace in
theorem ChartedSpace.small_of_compactSpace (H : Type u) [TopologicalSpace H] [Small.{w} H]
    (M : Type v) [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] : Small.{w} M :=
  ChartedSpace.small_of_lindelofSpace H M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ChartedSpace.small_of_compactSpace then
    throwError "Refusing to shadow existing declaration ChartedSpace.small_of_compactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `ChartedSpace.small_of_compactSpace ``Submission.ChartedSpace.small_of_compactSpace
