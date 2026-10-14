import Mathlib.Topology.Order.IntermediateValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology

variable {X α : Type*} [TopologicalSpace X] [LinearOrder α] [TopologicalSpace α]
  [OrderClosedTopology α] {S : Set X} {f : X → α} {r : α} {p : X}

theorem connectedComponentIn_sdiff_fiber_eq_inter_lt
    (hf : ContinuousOn f S) (hconn : IsPreconnected (S ∩ {x | f x < r}))
    (hp : p ∈ S ∩ {x | f x < r}) :
    connectedComponentIn (S \ {x | f x = r}) p = S ∩ {x | f x < r} := by
  have hsub : S ∩ {x | f x < r} ⊆ S \ {x | f x = r} :=
    fun _ hx => ⟨hx.1, (show f _ < r from hx.2).ne⟩
  apply Subset.antisymm _ (hconn.subset_connectedComponentIn hp hsub)
  intro x hx
  have hxS := connectedComponentIn_subset (S \ {x | f x = r}) p hx
  refine ⟨hxS.1, ?_⟩
  change f x < r
  by_contra h
  have hpx := mem_connectedComponentIn (hsub hp)
  obtain ⟨y, hy, hyr⟩ := isPreconnected_connectedComponentIn.intermediate_value hpx hx
    (hf.mono ((connectedComponentIn_subset _ _).trans _root_.Set.sdiff_subset))
    ⟨(show f p < r from hp.2).le, le_of_not_gt h⟩
  exact (connectedComponentIn_subset _ _ hy).2 hyr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedComponentIn_sdiff_fiber_eq_inter_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedComponentIn_sdiff_fiber_eq_inter_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedComponentIn_sdiff_fiber_eq_inter_lt ``Submission.DifferentialGeometry.Topology.connectedComponentIn_sdiff_fiber_eq_inter_lt

theorem connectedComponentIn_sdiff_fiber_eq_inter_gt
    (hf : ContinuousOn f S) (hconn : IsPreconnected (S ∩ {x | r < f x}))
    (hp : p ∈ S ∩ {x | r < f x}) :
    connectedComponentIn (S \ {x | f x = r}) p = S ∩ {x | r < f x} := by
  exact connectedComponentIn_sdiff_fiber_eq_inter_lt (α := αᵒᵈ) hf hconn hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedComponentIn_sdiff_fiber_eq_inter_gt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedComponentIn_sdiff_fiber_eq_inter_gt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedComponentIn_sdiff_fiber_eq_inter_gt ``Submission.DifferentialGeometry.Topology.connectedComponentIn_sdiff_fiber_eq_inter_gt

end DifferentialGeometry.Topology
