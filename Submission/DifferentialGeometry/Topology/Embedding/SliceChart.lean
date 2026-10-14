/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Submission.DifferentialGeometry.External.TauCeti.Geometry.Manifold.LocallyFlat.Smooth

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace Manifold
open _root_.Manifold

open _root_.Set _root_.Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N}

open _root_.Manifold _root_.Manifold.IsSmoothEmbedding in
theorem IsSmoothEmbedding.exists_contMDiffOn_slice_chart [J.Boundaryless]
    (h : _root_.Manifold.IsSmoothEmbedding I J n f) (x : M) :
    ∃ Φ : OpenPartialHomeomorph N (E × h.isImmersion.complement), f x ∈ Φ.source ∧
      ContMDiffOn J 𝓘(𝕜, E × h.isImmersion.complement) n Φ Φ.source ∧
      ContMDiffOn 𝓘(𝕜, E × h.isImmersion.complement) J n Φ.symm Φ.target ∧
      Φ '' (Φ.source ∩ _root_.Set.range f) =
        Φ.target ∩ (_root_.Set.range I ×ˢ ({0} : Set h.isImmersion.complement)) :=
  (h.isImmersion.isImmersionOfComplement_complement x).exists_contMDiffOn_slice_chart
    h.isEmbedding.isInducing

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Manifold.IsSmoothEmbedding
  let env ← Lean.getEnv
  if env.contains `Manifold.IsSmoothEmbedding.exists_contMDiffOn_slice_chart then
    throwError "Refusing to shadow existing declaration Manifold.IsSmoothEmbedding.exists_contMDiffOn_slice_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.IsSmoothEmbedding.exists_contMDiffOn_slice_chart ``Submission.Manifold.IsSmoothEmbedding.exists_contMDiffOn_slice_chart

end Manifold
