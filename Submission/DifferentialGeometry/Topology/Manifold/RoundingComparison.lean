import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Inverse
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace PartialDiffeomorph
open _root_.PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : WithTop ℕ∞}

open _root_.PartialDiffeomorph in
theorem isLocalDiffeomorph_unrounding
    (c : PartialDiffeomorph I J M N n) (R₀ : M ≃ₜ M) (R₁ : N ≃ₜ N)
    (Q : Diffeomorph I J M N n) {K : Set M} {L : Set N}
    (hR₀ : ∀ x ∉ K, IsLocalDiffeomorphAt I I n R₀ x)
    (hR₁ : ∀ y ∉ L, IsLocalDiffeomorphAt J J n R₁ y)
    (hcKL : c '' K = L) {U : Set M} (hU : IsOpen U) (hKU : K ⊆ U)
    (hUc : U ⊆ c.source) (hcomm : ∀ x ∈ U, R₁ (c x) = Q (R₀ x)) :
    IsLocalDiffeomorph I J n (R₁.symm ∘ Q ∘ R₀) := by
  let F := (R₀.trans Q.toHomeomorph).trans R₁.symm
  have hFc : _root_.Set.EqOn F c U := by
    intro x hx
    change R₁.symm (Q (R₀ x)) = c x
    rw [← hcomm x hx, R₁.symm_apply_apply]
  intro x
  by_cases hx : x ∈ K
  · apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq
      (hg := c.isLocalDiffeomorphAt I J n (hUc (hKU hx)))
    filter_upwards [hU.mem_nhds (hKU hx)] with z hz
    exact hFc hz
  · have hy : F x ∉ L := by
      intro h
      rw [← hcKL] at h
      obtain ⟨z, hz, hze⟩ := h
      have hFz : F z = F x := (hFc (hKU hz)).trans hze
      exact hx (F.injective hFz ▸ hz)
    have hinv := R₁.isLocalDiffeomorphAt_symm (hR₁ (F x) hy)
    have heq : R₁ (F x) = Q (R₀ x) := R₁.apply_symm_apply _
    rw [heq] at hinv
    exact ((hR₀ x hx).comp _ _ (Q.isLocalDiffeomorph _)).comp _ _ hinv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.isLocalDiffeomorph_unrounding then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.isLocalDiffeomorph_unrounding"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.isLocalDiffeomorph_unrounding ``Submission.PartialDiffeomorph.isLocalDiffeomorph_unrounding

open _root_.PartialDiffeomorph in
theorem exists_diffeomorph_unrounding
    (c : PartialDiffeomorph I J M N n) (R₀ : M ≃ₜ M) (R₁ : N ≃ₜ N)
    (Q : Diffeomorph I J M N n) {K : Set M} {L : Set N}
    (hR₀ : ∀ x ∉ K, IsLocalDiffeomorphAt I I n R₀ x)
    (hR₁ : ∀ y ∉ L, IsLocalDiffeomorphAt J J n R₁ y)
    (hcKL : c '' K = L) {U : Set M} (hU : IsOpen U) (hKU : K ⊆ U)
    (hUc : U ⊆ c.source) (hcomm : ∀ x ∈ U, R₁ (c x) = Q (R₀ x))
    {A : Set M} {B : Set N} (hQ : Q '' (R₀ '' A) = R₁ '' B) :
    ∃ F : Diffeomorph I J M N n,
      (F : M → N) = R₁.symm ∘ Q ∘ R₀ ∧ F '' A = B ∧ _root_.Set.EqOn F c U := by
  let G := (R₀.trans Q.toHomeomorph).trans R₁.symm
  have hG : IsLocalDiffeomorph I J n G :=
    c.isLocalDiffeomorph_unrounding R₀ R₁ Q hR₀ hR₁ hcKL hU hKU hUc hcomm
  let F := hG.diffeomorphOfBijective G.bijective
  have hF : (F : M → N) = R₁.symm ∘ Q ∘ R₀ := rfl
  refine ⟨F, hF, ?_, ?_⟩
  · rw [hF, _root_.Set.image_comp, _root_.Set.image_comp, hQ, _root_.Set.image_image]
    simp only [R₁.symm_apply_apply, _root_.Set.image_id']
  · intro x hx
    rw [hF]
    change R₁.symm (Q (R₀ x)) = c x
    rw [← hcomm x hx, R₁.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `PartialDiffeomorph.exists_diffeomorph_unrounding then
    throwError "Refusing to shadow existing declaration PartialDiffeomorph.exists_diffeomorph_unrounding"
  Lean.modifyEnv fun env => Lean.addAlias env `PartialDiffeomorph.exists_diffeomorph_unrounding ``Submission.PartialDiffeomorph.exists_diffeomorph_unrounding

end PartialDiffeomorph
