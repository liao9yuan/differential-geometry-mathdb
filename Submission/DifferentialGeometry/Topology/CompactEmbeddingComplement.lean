/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.OpenEmbeddingFrontier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem nonempty_homeomorph_interior_sdiff_image_of_isCompact {A K : Set E} {f : E → E}
    (hA : IsCompact A) (hKA : K ⊆ A) (hf : ContinuousOn f A) (hinj : _root_.Set.InjOn f A) :
    Nonempty (↥(interior A \ K) ≃ₜ ↥(interior (f '' A) \ f '' K)) := by
  have hI : interior (f '' A) = f '' interior A := by
    rw [← _root_.Set.range_domRestrict f A,
      interior_range_eq_image_preimage_interior hA _ hf.domRestrict hinj.injective]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, interior_subset hx⟩, hx, rfl⟩
  have hD : (interior A \ K).domRestrict f '' _root_.Set.univ =
      interior (f '' A) \ f '' K := by
    rw [hI]
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      refine ⟨⟨x, x.2.1, rfl⟩, ?_⟩
      rintro ⟨z, hz, hzx⟩
      exact x.2.2 ((hinj (hKA hz) (interior_subset x.2.1) hzx) ▸ hz)
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      exact ⟨⟨x, hx, fun hxK => hy ⟨x, hxK, rfl⟩⟩, _root_.Set.mem_univ _, rfl⟩
  have hcompact : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hemb : _root_.Topology.IsEmbedding (A.domRestrict f) :=
    (hf.domRestrict.isClosedEmbedding hinj.injective).isEmbedding
  have hembD : _root_.Topology.IsEmbedding ((interior A \ K).domRestrict f) :=
    hemb.comp (.inclusion (sdiff_subset.trans interior_subset))
  refine ⟨hembD.toHomeomorph.trans (Homeomorph.setCongr ?_)⟩
  simpa only [_root_.Set.image_univ] using hD

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_homeomorph_interior_sdiff_image_of_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_homeomorph_interior_sdiff_image_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_homeomorph_interior_sdiff_image_of_isCompact ``Submission.DifferentialGeometry.Topology.nonempty_homeomorph_interior_sdiff_image_of_isCompact

end DifferentialGeometry.Topology
