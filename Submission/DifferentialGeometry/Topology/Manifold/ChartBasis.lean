import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Bases

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.TopologicalSpace

namespace ChartedSpace
open _root_.ChartedSpace

open _root_.ChartedSpace in
theorem exists_isTopologicalBasis_homeomorph_open
    (H M : Type*) [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] :
    ∃ B : Set (Set M), _root_.TopologicalSpace.IsTopologicalBasis B ∧
      (∀ U ∈ B, ∀ V ∈ B, U ∩ V ∈ B) ∧
      ∀ U ∈ B, ∃ S : Set H, IsOpen S ∧ Nonempty (U ≃ₜ S) := by
  let B : Set (Set M) := {U | IsOpen U ∧ ∃ p : M, U ⊆ (chartAt H p).source}
  refine ⟨B, ?_, ?_, ?_⟩
  · apply _root_.TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun _ h => h.1)
    intro x U hx hU
    exact ⟨U ∩ (chartAt H x).source,
      ⟨hU.inter (chartAt H x).open_source, x, inter_subset_right⟩,
      ⟨hx, mem_chart_source H x⟩, inter_subset_left⟩
  · rintro U ⟨hU, p, hp⟩ V ⟨hV, _⟩
    exact ⟨hU.inter hV, p, inter_subset_left.trans hp⟩
  · rintro U ⟨hU, p, hp⟩
    exact ⟨(chartAt H p) '' U, (chartAt H p).isOpen_image_of_subset_source hU hp,
      ⟨(chartAt H p).homeomorphOfImageSubsetSource hp rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ChartedSpace.exists_isTopologicalBasis_homeomorph_open then
    throwError "Refusing to shadow existing declaration ChartedSpace.exists_isTopologicalBasis_homeomorph_open"
  Lean.modifyEnv fun env => Lean.addAlias env `ChartedSpace.exists_isTopologicalBasis_homeomorph_open ``Submission.ChartedSpace.exists_isTopologicalBasis_homeomorph_open

end ChartedSpace

namespace ModelWithCorners
open _root_.ModelWithCorners

open _root_.ModelWithCorners in
theorem exists_isTopologicalBasis_homeomorph_open
    {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :
    ∃ B : Set (Set M), _root_.TopologicalSpace.IsTopologicalBasis B ∧
      (∀ U ∈ B, ∀ V ∈ B, U ∩ V ∈ B) ∧
      ∀ U ∈ B, ∃ S : Set E, IsOpen S ∧ Nonempty (U ≃ₜ S) := by
  obtain ⟨B, hB, hinter, hchart⟩ := ChartedSpace.exists_isTopologicalBasis_homeomorph_open H M
  refine ⟨B, hB, hinter, ?_⟩
  intro U hU
  obtain ⟨S, hS, ⟨e⟩⟩ := hchart U hU
  exact ⟨I.toHomeomorph '' S, I.toHomeomorph.isOpenMap _ hS,
    ⟨e.trans (I.toHomeomorph.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource
      (_root_.Set.subset_univ S) rfl)⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ModelWithCorners.exists_isTopologicalBasis_homeomorph_open then
    throwError "Refusing to shadow existing declaration ModelWithCorners.exists_isTopologicalBasis_homeomorph_open"
  Lean.modifyEnv fun env => Lean.addAlias env `ModelWithCorners.exists_isTopologicalBasis_homeomorph_open ``Submission.ModelWithCorners.exists_isTopologicalBasis_homeomorph_open

end ModelWithCorners
