import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.ContDiff _root_.Manifold

namespace Homeomorph
open _root_.Homeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : WithTop ℕ∞}

open _root_.Homeomorph in
theorem isLocalDiffeomorphAt_symm (h : M ≃ₜ N) {x : M}
    (hx : IsLocalDiffeomorphAt I J n h x) :
    IsLocalDiffeomorphAt J I n h.symm (h x) := by
  obtain ⟨e, hxe, he⟩ := hx
  refine ⟨e.symm, ?_, ?_⟩
  · change h x ∈ e.target
    rw [he hxe]
    exact e.map_source hxe
  · intro y hy
    apply h.injective
    rw [h.apply_symm_apply]
    have hy' : y ∈ e.target := hy
    exact ((he (e.map_target hy')).trans (e.right_inv hy')).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.isLocalDiffeomorphAt_symm then
    throwError "Refusing to shadow existing declaration Homeomorph.isLocalDiffeomorphAt_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.isLocalDiffeomorphAt_symm ``Submission.Homeomorph.isLocalDiffeomorphAt_symm

open _root_.Homeomorph in
theorem isLocalDiffeomorphAt_symm_iff (h : M ≃ₜ N) {y : N} :
    IsLocalDiffeomorphAt J I n h.symm y ↔
      IsLocalDiffeomorphAt I J n h (h.symm y) := by
  constructor
  · intro hy
    exact h.symm.isLocalDiffeomorphAt_symm hy
  · intro hx
    simpa only [h.apply_symm_apply] using h.isLocalDiffeomorphAt_symm hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.isLocalDiffeomorphAt_symm_iff then
    throwError "Refusing to shadow existing declaration Homeomorph.isLocalDiffeomorphAt_symm_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.isLocalDiffeomorphAt_symm_iff ``Submission.Homeomorph.isLocalDiffeomorphAt_symm_iff

end Homeomorph
