import Mathlib.Geometry.Manifold.ContMDiff.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open scoped _root_.Manifold _root_.ContDiff

namespace Function.LeftInverse
open _root_.Function _root_.Function.LeftInverse

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
  {H₀ : Type*} [TopologicalSpace H₀] {I₀ : ModelWithCorners 𝕜 E₀ H₀}
  {M₀ : Type*} [TopologicalSpace M₀] [ChartedSpace H₀ M₀]
variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners 𝕜 E₁ H₁}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
variable {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]

open _root_.Function _root_.Function.LeftInverse in
theorem contMDiffOn_of_comp {f : M₁ → M₂} {r : M₂ → M₁}
    (hleft : _root_.Function.LeftInverse r f) {g : M₀ → M₁} {s : Set M₀} {u : Set M₂} {n : ℕ∞ω}
    (hr : ContMDiffOn I₂ I₁ n r u) (hg : ContMDiffOn I₀ I₂ n (f ∘ g) s)
    (hmem : Set.MapsTo (f ∘ g) s u) : ContMDiffOn I₀ I₁ n g s := by
  exact (hr.comp hg hmem).congr (fun x _ => (hleft (g x)).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Function.LeftInverse.contMDiffOn_of_comp then
    throwError "Refusing to shadow existing declaration Function.LeftInverse.contMDiffOn_of_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `Function.LeftInverse.contMDiffOn_of_comp ``Submission.Function.LeftInverse.contMDiffOn_of_comp

open _root_.Function _root_.Function.LeftInverse in
theorem contMDiff_of_comp {f : M₁ → M₂} {r : M₂ → M₁}
    (hleft : _root_.Function.LeftInverse r f) {g : M₀ → M₁} {u : Set M₂} {n : ℕ∞ω}
    (hr : ContMDiffOn I₂ I₁ n r u) (hg : ContMDiff I₀ I₂ n (f ∘ g))
    (hmem : ∀ x, f (g x) ∈ u) : ContMDiff I₀ I₁ n g := by
  exact contMDiffOn_univ.mp
    (hleft.contMDiffOn_of_comp hr hg.contMDiffOn (fun x _ => hmem x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Function.LeftInverse.contMDiff_of_comp then
    throwError "Refusing to shadow existing declaration Function.LeftInverse.contMDiff_of_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `Function.LeftInverse.contMDiff_of_comp ``Submission.Function.LeftInverse.contMDiff_of_comp

end Function.LeftInverse

end
