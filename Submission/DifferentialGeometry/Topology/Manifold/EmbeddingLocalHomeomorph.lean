/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.InvarianceOfDomainManifold
import Mathlib.Topology.OpenPartialHomeomorph.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology

variable {E M N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace E N]

include E in
theorem exists_openPartialHomeomorph_of_continuousOn_injOn [Nonempty M]
    {U : Set M} (hU : IsOpen U) {f : M → N} (hf : ContinuousOn f U) (hinj : _root_.Set.InjOn f U) :
    ∃ F : OpenPartialHomeomorph M N, F.source = U ∧ F.target = f '' U ∧
      ∀ x, F x = f x := by
  classical
  have hopen : IsOpenMap (U.domRestrict f) := by
    intro W hW
    have hW' : IsOpen (Subtype.val '' W) := hU.isOpenMap_subtype_val W hW
    have hWU : Subtype.val '' W ⊆ U := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have himage : U.domRestrict f '' W = f '' (Subtype.val '' W) := by
      rw [← _root_.Set.image_comp]
      rfl
    rw [himage]
    exact isOpen_image_of_continuousOn_injOn (E := E) hW' (hf.mono hWU) (hinj.mono hWU)
  exact ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict (hinj.toPartialEquiv f U)
    hf hopen hU, rfl, rfl, fun _ => rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_openPartialHomeomorph_of_continuousOn_injOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_openPartialHomeomorph_of_continuousOn_injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_openPartialHomeomorph_of_continuousOn_injOn ``Submission.DifferentialGeometry.Topology.exists_openPartialHomeomorph_of_continuousOn_injOn

end DifferentialGeometry.Topology
