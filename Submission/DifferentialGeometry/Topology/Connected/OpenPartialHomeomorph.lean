import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Hausdorff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Set

namespace OpenPartialHomeomorph
open _root_.OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open _root_.OpenPartialHomeomorph in
theorem image_eq_connectedComponent
    (e : OpenPartialHomeomorph X Y) {s : Set X}
    (hconnected : IsPreconnected s) (hopen : IsOpen s)
    (hclosed : IsClosed (e '' s)) (hsource : s ⊆ e.source)
    {x : X} (hx : x ∈ s) : e '' s = connectedComponent (e x) := by
  have hcont := e.continuousOn.mono hsource
  have hconn := hconnected.image e hcont
  have hopen' := e.isOpen_image_of_subset_source hopen hsource
  have hmem : e x ∈ e '' s := _root_.Set.mem_image_of_mem e hx
  exact subset_antisymm (hconn.subset_connectedComponent hmem)
    ((show IsClopen (e '' s) from ⟨hclosed, hopen'⟩).connectedComponent_subset hmem)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.image_eq_connectedComponent then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.image_eq_connectedComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.image_eq_connectedComponent ``Submission.OpenPartialHomeomorph.image_eq_connectedComponent

open _root_.OpenPartialHomeomorph in
theorem image_eq_connectedComponent_of_isCompact [T2Space Y]
    (e : OpenPartialHomeomorph X Y) {s : Set X}
    (hcompact : IsCompact s) (hconnected : IsPreconnected s) (hopen : IsOpen s)
    (hsource : s ⊆ e.source) {x : X} (hx : x ∈ s) :
    e '' s = connectedComponent (e x) :=
  e.image_eq_connectedComponent hconnected hopen
    (hcompact.image_of_continuousOn (e.continuousOn.mono hsource)).isClosed hsource hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.image_eq_connectedComponent_of_isCompact then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.image_eq_connectedComponent_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.image_eq_connectedComponent_of_isCompact ``Submission.OpenPartialHomeomorph.image_eq_connectedComponent_of_isCompact

end OpenPartialHomeomorph
