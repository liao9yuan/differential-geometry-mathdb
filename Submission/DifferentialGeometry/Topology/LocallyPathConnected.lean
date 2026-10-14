/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Topology.Connected.LocallyPathConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Filter _root_.Set _root_.Topology

universe u v

namespace DifferentialGeometry.Topology


theorem locallyPathConnectedSpace_of_openCover
    {X : Type u} [TopologicalSpace X] {ι : Type v} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hlocal : ∀ i, LocallyPathConnectedSpace (U i)) :
    LocallyPathConnectedSpace X := by
  refine ⟨fun x => ?_⟩
  rw [Filter.hasBasis_self]
  intro s hs
  obtain ⟨i, hxi⟩ := hcover x
  let xi : U i := ⟨x, hxi⟩
  let _ : LocallyPathConnectedSpace (U i) := hlocal i
  have hs' : Subtype.val ⁻¹' s ∈ 𝓝 xi := continuousAt_subtype_val hs
  obtain ⟨t, ht, hts⟩ := (_root_.LocallyPathConnectedSpace.path_connected_basis xi).mem_iff.mp hs'
  refine ⟨Subtype.val '' t, ?_, ?_, ?_⟩
  · exact (hU i).isOpenEmbedding_subtypeVal.image_mem_nhds.mpr ht.1
  · exact ht.2.image continuous_subtype_val
  · rintro _ ⟨y, hy, rfl⟩
    exact hts hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.locallyPathConnectedSpace_of_openCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.locallyPathConnectedSpace_of_openCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.locallyPathConnectedSpace_of_openCover ``Submission.DifferentialGeometry.Topology.locallyPathConnectedSpace_of_openCover

end DifferentialGeometry.Topology
