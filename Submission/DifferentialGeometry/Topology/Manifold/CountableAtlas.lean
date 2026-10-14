import Mathlib.Geometry.Manifold.ChartedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.Manifold


theorem secondCountableTopology_of_compact {E M : Type*} [TopologicalSpace E]
    [TopologicalSpace M] [ChartedSpace E M] [SecondCountableTopology E] [CompactSpace M] :
    SecondCountableTopology M := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => (chartAt E x).source) (fun x => (chartAt E x).open_source)
    (show (Set.univ : Set M) ⊆ ⋃ x, (chartAt E x).source from
      fun x _ => Set.mem_iUnion.mpr ⟨x, mem_chart_source E x⟩)
  exact ChartedSpace.secondCountable_of_countable_cover E
    (Set.eq_univ_of_subset hs rfl) s.countable_toSet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.secondCountableTopology_of_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.secondCountableTopology_of_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.secondCountableTopology_of_compact ``Submission.DifferentialGeometry.Topology.Manifold.secondCountableTopology_of_compact

end DifferentialGeometry.Topology.Manifold
