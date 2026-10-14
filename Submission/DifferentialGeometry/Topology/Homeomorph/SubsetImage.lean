/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.OpenPartialHomeomorph.Images
import Mathlib.Topology.Separation.Hausdorff

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
theorem image_frontier_of_isCompact [T2Space X] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) {s : Set X} (hc : IsCompact s)
    (hs : s ⊆ e.source) : e '' frontier s = frontier (e '' s) :=
  e.image_frontier_of_subset_source hs hc.isClosed
    (hc.image_of_continuousOn (e.continuousOn.mono hs)).isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.image_frontier_of_isCompact then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.image_frontier_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.image_frontier_of_isCompact ``Submission.OpenPartialHomeomorph.image_frontier_of_isCompact

end OpenPartialHomeomorph
