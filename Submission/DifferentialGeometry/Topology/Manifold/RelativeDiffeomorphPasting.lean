/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homeomorph.ClosedExtension
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.ContDiff

namespace Homeomorph
open _root_.Homeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H G M N : Type*} [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace H M] [ChartedSpace G N]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G} {n : ℕ∞ω}

open _root_.Homeomorph in
private theorem isLocalDiffeomorphAt_of_eqOn_open {f g : M → N} {x : M} {U : Set M}
    (hg : IsLocalDiffeomorphAt I J n g x) (hU : IsOpen U) (hx : x ∈ U)
    (heq : _root_.Set.EqOn f g U) : IsLocalDiffeomorphAt I J n f x := by
  obtain ⟨φ, hxφ, hφ⟩ := hg
  let ψ : PartialDiffeomorph I J M N n := {
    __ := φ.toOpenPartialHomeomorph.restrOpen U hU
    contMDiffOn_toFun := φ.contMDiffOn_toFun.mono _root_.Set.inter_subset_left
    contMDiffOn_invFun := φ.contMDiffOn_invFun.mono _root_.Set.inter_subset_left }
  exact ⟨ψ, ⟨hxφ, hx⟩, fun y hy => (heq hy.2).trans (hφ hy.1)⟩

run_cmd do
  let target := ``Submission.Homeomorph.isLocalDiffeomorphAt_of_eqOn_open
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Homeomorph.isLocalDiffeomorphAt_of_eqOn_open target :: scope.openDecls } }

open _root_.Homeomorph in
theorem exists_pasting_of_partialDiffeomorph (h : M ≃ₜ N)
    (φ : PartialDiffeomorph I J M N n) {K U : Set M} (hK : IsClosed K)
    (hsource : K ⊆ φ.source) (himage : φ '' K = h '' K)
    (hU : IsOpen U) (hfrontier : frontier K ⊆ U) (heq : _root_.Set.EqOn φ h U) :
    ∃ g : M ≃ₜ N, _root_.Set.EqOn g φ K ∧ _root_.Set.EqOn g h (interior K)ᶜ ∧ _root_.Set.EqOn g h U ∧
      g '' K = h '' K ∧
      (∀ x, IsLocalDiffeomorphAt I J n h x → IsLocalDiffeomorphAt I J n g x) ∧
      ∃ W : Set M, IsOpen W ∧ K ⊆ W ∧ W ⊆ φ.source ∧ _root_.Set.EqOn g φ W ∧
        IsLocalDiffeomorphOn I J n g W := by
  let A : K ≃ₜ h '' K :=
    φ.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource hsource himage
  let B : K ≃ₜ h '' K := h.image K
  let q : K ≃ₜ K := A.trans B.symm
  have hfix : ∀ x : K, (x : M) ∈ frontier K → q x = x := by
    intro x hx
    apply B.injective
    change B (B.symm (A x)) = B x
    rw [B.apply_symm_apply]
    exact Subtype.ext (heq (hfrontier hx))
  let g := (q.extendById hK hfix).trans h
  have hgK : _root_.Set.EqOn g φ K := by
    intro x hx
    change h (q.extendById hK hfix x) = φ x
    rw [q.extendById_apply_of_mem hK hfix hx]
    exact congrArg Subtype.val (B.apply_symm_apply (A ⟨x, hx⟩))
  have hgout : _root_.Set.EqOn g h (interior K)ᶜ := by
    intro x hx
    change h (q.extendById hK hfix x) = h x
    rw [q.extendById_eqOn_compl_interior hK hfix hx, id_eq]
  have hgU : _root_.Set.EqOn g h U := by
    intro x hx
    by_cases hxK : x ∈ K
    · exact (hgK hxK).trans (heq hx)
    · exact hgout (fun hi => hxK (interior_subset hi))
  let W := interior K ∪ (U ∩ φ.source)
  have hW : IsOpen W := isOpen_interior.union (hU.inter φ.open_source)
  have hKW : K ⊆ W := by
    intro x hx
    by_cases hi : x ∈ interior K
    · exact Or.inl hi
    · exact Or.inr ⟨hfrontier ⟨subset_closure hx, hi⟩, hsource hx⟩
  have hWs : W ⊆ φ.source := fun _ hx =>
    hx.elim (fun hi => hsource (interior_subset hi)) (fun hu => hu.2)
  have hgW : _root_.Set.EqOn g φ W := by
    intro x hx
    rcases hx with hi | hu
    · exact hgK (interior_subset hi)
    · exact (hgU hu.1).trans (heq hu.1).symm
  have hgdiff : IsLocalDiffeomorphOn I J n g W := fun x =>
    isLocalDiffeomorphAt_of_eqOn_open (φ.isLocalDiffeomorphAt I J n (hWs x.property))
      hW x.property hgW
  refine ⟨g, hgK, hgout, hgU, (_root_.Set.image_congr hgK).trans himage, ?_,
    W, hW, hKW, hWs, hgW, hgdiff⟩
  intro x hx
  by_cases hxK : x ∈ K
  · exact hgdiff ⟨x, hKW hxK⟩
  · exact isLocalDiffeomorphAt_of_eqOn_open hx hK.isOpen_compl hxK
      (fun y hy => hgout (fun hi => hy (interior_subset hi)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.exists_pasting_of_partialDiffeomorph then
    throwError "Refusing to shadow existing declaration Homeomorph.exists_pasting_of_partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.exists_pasting_of_partialDiffeomorph ``Submission.Homeomorph.exists_pasting_of_partialDiffeomorph

end Homeomorph
