import Mathlib.Topology.OpenPartialHomeomorph.IsImage

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace OpenPartialHomeomorph
open _root_.OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open _root_.OpenPartialHomeomorph in
theorem isImage_image_of_subset_source (e : OpenPartialHomeomorph X Y)
    {s : Set X} (hs : s ⊆ e.source) : e.IsImage s (e '' s) := by
  apply IsImage.of_image_eq
  have ht : e '' s ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hs hx)
  rw [inter_eq_right.mpr hs, inter_eq_right.mpr ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.isImage_image_of_subset_source then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.isImage_image_of_subset_source"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.isImage_image_of_subset_source ``Submission.OpenPartialHomeomorph.isImage_image_of_subset_source

open _root_.OpenPartialHomeomorph in
theorem image_interior_of_subset_source (e : OpenPartialHomeomorph X Y)
    {s : Set X} (hs : s ⊆ e.source) : e '' interior s = interior (e '' s) := by
  have h := (e.isImage_image_of_subset_source hs).interior.image_eq
  have ht : e '' s ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hs hx)
  rw [inter_eq_right.mpr (interior_subset.trans hs),
    inter_eq_right.mpr (interior_subset.trans ht)] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.image_interior_of_subset_source then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.image_interior_of_subset_source"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.image_interior_of_subset_source ``Submission.OpenPartialHomeomorph.image_interior_of_subset_source

open _root_.OpenPartialHomeomorph in
theorem image_frontier_of_subset_source (e : OpenPartialHomeomorph X Y)
    {s : Set X} (hs : s ⊆ e.source) (hsc : IsClosed s) (htc : IsClosed (e '' s)) :
    e '' frontier s = frontier (e '' s) := by
  have h := (e.isImage_image_of_subset_source hs).frontier.image_eq
  have ht : e '' s ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hs hx)
  rw [inter_eq_right.mpr (hsc.frontier_subset.trans hs),
    inter_eq_right.mpr (htc.frontier_subset.trans ht)] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.image_frontier_of_subset_source then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.image_frontier_of_subset_source"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.image_frontier_of_subset_source ``Submission.OpenPartialHomeomorph.image_frontier_of_subset_source

open _root_.OpenPartialHomeomorph in
theorem closure_interior_image_of_subset_source (e : OpenPartialHomeomorph X Y)
    {s : Set X} (hs : s ⊆ e.source) (hreg : closure (interior s) = s)
    (hclosed : IsClosed (e '' s)) : closure (interior (e '' s)) = e '' s := by
  apply Subset.antisymm (closure_minimal interior_subset hclosed)
  rw [← e.image_interior_of_subset_source hs]
  have hc : ContinuousOn e (closure (interior s)) := by
    rw [hreg]
    exact e.continuousOn.mono hs
  simpa only [hreg] using hc.image_closure

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.closure_interior_image_of_subset_source then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.closure_interior_image_of_subset_source"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.closure_interior_image_of_subset_source ``Submission.OpenPartialHomeomorph.closure_interior_image_of_subset_source

end OpenPartialHomeomorph
