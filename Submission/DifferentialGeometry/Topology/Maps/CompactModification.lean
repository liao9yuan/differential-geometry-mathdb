import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Topology
set_option autoImplicit false
namespace DifferentialGeometry.Topology

theorem isClosedMap_of_compact_modification
    {X : Type*} [TopologicalSpace X] [T2Space X] {f : X → X}
    (hf : Continuous f) {K : Set X} (hK : IsCompact K) (hfix : _root_.Set.EqOn f id Kᶜ) :
    IsClosedMap f := by
  have hfixed : IsClosed {x | f x = x} := isClosed_eq hf continuous_id
  have hfix' : _root_.Set.EqOn f id (closure Kᶜ) := closure_minimal hfix hfixed
  intro S hS
  have heq : f '' S = f '' (S ∩ K) ∪ (S ∩ closure Kᶜ) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases hxK : x ∈ K
      · exact Or.inl ⟨x, ⟨hx, hxK⟩, rfl⟩
      · have hh := hfix hxK
        change f x = x at hh
        rw [hh]
        exact Or.inr ⟨hx, subset_closure hxK⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨hy, hyK⟩)
      · exact ⟨x, hx.1, rfl⟩
      · exact ⟨y, hy, hfix' hyK⟩
  rw [heq]
  exact ((hK.inter_left hS).image hf).isClosed.union (hS.inter isClosed_closure)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isClosedMap_of_compact_modification then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isClosedMap_of_compact_modification"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isClosedMap_of_compact_modification ``Submission.DifferentialGeometry.Topology.isClosedMap_of_compact_modification

end DifferentialGeometry.Topology
