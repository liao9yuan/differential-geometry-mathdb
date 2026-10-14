/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.Homeomorph.ClosedExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace Homeomorph
open _root_.Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open _root_.Homeomorph in
theorem exists_pasting_of_image_eq (f g : X ≃ₜ Y) {K : Set X} (hK : IsClosed K)
    (himage : f '' K = g '' K) (hfront : _root_.Set.EqOn f g (frontier K)) :
    ∃ h : X ≃ₜ Y, _root_.Set.EqOn h f K ∧ _root_.Set.EqOn h g (interior K)ᶜ := by
  let F : K ≃ₜ f '' K := f.image K
  let G : K ≃ₜ f '' K := (g.image K).trans (Homeomorph.setCongr himage.symm)
  let q : K ≃ₜ K := F.trans G.symm
  have hfix : ∀ x : K, (x : X) ∈ frontier K → q x = x := by
    intro x hx
    apply G.injective
    change G (G.symm (F x)) = G x
    rw [G.apply_symm_apply]
    exact Subtype.ext (hfront hx)
  refine ⟨(q.extendById hK hfix).trans g, ?_, ?_⟩
  · intro x hx
    change g (q.extendById hK hfix x) = f x
    rw [q.extendById_apply_of_mem hK hfix hx]
    exact congrArg Subtype.val (G.apply_symm_apply (F ⟨x, hx⟩))
  · intro x hx
    change g (q.extendById hK hfix x) = g x
    rw [q.extendById_eqOn_compl_interior hK hfix hx, id_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.exists_pasting_of_image_eq then
    throwError "Refusing to shadow existing declaration Homeomorph.exists_pasting_of_image_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.exists_pasting_of_image_eq ``Submission.Homeomorph.exists_pasting_of_image_eq

end Homeomorph
