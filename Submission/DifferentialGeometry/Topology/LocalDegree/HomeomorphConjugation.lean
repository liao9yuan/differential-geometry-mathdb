/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.LocalDegree.ChartParityTransport
import Submission.DifferentialGeometry.Topology.Manifold.EmbeddingLocalHomeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter
open scoped _root_.Topology _root_.Manifold

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))

theorem embeddingOrientationParity_conj_homeomorph
    (c : E ≃ₜ E) {U : Set E} (hU : IsOpen U) {f : E → E}
    (hf : ContinuousOn f U) (hfi : _root_.Set.InjOn f U) (x : U) :
    embeddingOrientationParity (hU.preimage c.symm.continuous)
      (c.continuous.comp_continuousOn
        (hf.comp c.symm.continuous.continuousOn (fun _ hx => hx)))
      (fun y hy z hz hyz => c.symm.injective (hfi hy hz (c.injective hyz)))
      ⟨c x, by simpa only [_root_.Set.mem_preimage, c.symm_apply_apply] using x.2⟩ =
      embeddingOrientationParity hU hf hfi x := by
  obtain ⟨F, hFs, -, hF⟩ :=
    DifferentialGeometry.Topology.exists_openPartialHomeomorph_of_continuousOn_injOn
      («E» := E) hU hf hfi
  let a := OpenPartialHomeomorph.refl E
  let b := c.toOpenPartialHomeomorph
  have hxF : (x : E) ∈ F.source := hFs ▸ x.2
  have hrel := chartOrientationParity_relative_eq_of_isPreconnected F a b
    _root_.PreconnectedSpace.isPreconnected_univ (fun _ _ => _root_.Set.mem_univ _) (fun _ _ => _root_.Set.mem_univ _)
    x hxF (_root_.Set.mem_univ _) (_root_.Set.mem_univ _)
  have hleft : chartOrientationParity a (F ≫ₕ a) x (_root_.Set.mem_univ _)
      ⟨hxF, _root_.Set.mem_univ _⟩ = embeddingOrientationParity hU hf hfi x := by
    unfold chartOrientationParity
    exact embeddingOrientationParity_congr (a.symm ≫ₕ (F ≫ₕ a)).open_source hU
      (a.symm ≫ₕ (F ≫ₕ a)).continuousOn (a.symm ≫ₕ (F ≫ₕ a)).injOn hf hfi _ x.2
      (Filter.Eventually.of_forall hF)
  have hright : chartOrientationParity b (F ≫ₕ b) x (_root_.Set.mem_univ _)
      ⟨hxF, _root_.Set.mem_univ _⟩ =
      embeddingOrientationParity (hU.preimage c.symm.continuous)
        (c.continuous.comp_continuousOn
          (hf.comp c.symm.continuous.continuousOn (fun _ hx => hx)))
        (fun y hy z hz hyz => c.symm.injective (hfi hy hz (c.injective hyz)))
        ⟨c x, by simpa only [_root_.Set.mem_preimage, c.symm_apply_apply] using x.2⟩ := by
    unfold chartOrientationParity
    apply embeddingOrientationParity_congr
    exact Filter.Eventually.of_forall fun y => congrArg c (hF (c.symm y))
  exact hright.symm.trans (hrel.symm.trans hleft)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.embeddingOrientationParity_conj_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.embeddingOrientationParity_conj_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.embeddingOrientationParity_conj_homeomorph ``Submission.DifferentialGeometry.LocalDegree.embeddingOrientationParity_conj_homeomorph

end DifferentialGeometry.LocalDegree
