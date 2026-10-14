import Submission.DifferentialGeometry.Topology.Covering.DeckGroup
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {H : Type*} [TopologicalSpace H]
variable {G : Type*} [TopologicalSpace G]
variable {I : ModelWithCorners 𝕜 E H}
variable {J : ModelWithCorners 𝕜 F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
variable {n : ℕ∞ω}

theorem IsLocalDiffeomorph.contMDiff_of_comp_eq_self
    {p : M → N} (hp : IsLocalDiffeomorph I J n p)
    {φ : M → M} (hφ : Continuous φ) (hcomp : p ∘ φ = p) :
    ContMDiff I I n φ := by
  intro x
  have hpx := hp (φ x)
  refine (hpx.localInverse_contMDiffAt.comp_of_eq
    hp.contMDiff.contMDiffAt (congrFun hcomp x).symm).congr_of_eventuallyEq ?_
  have hevent : ∀ᶠ y in 𝓝 x, φ y ∈ hpx.localInverse.target :=
    hφ.continuousAt
      (hpx.localInverse.open_target.mem_nhds hpx.localInverse_mem_target)
  filter_upwards [hevent] with y hy
  change φ y = hpx.localInverse (p y)
  rw [← congrFun hcomp y]
  exact (hpx.localInverse_left_inv hy).symm

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.IsLocalDiffeomorph
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.IsLocalDiffeomorph.contMDiff_of_comp_eq_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.IsLocalDiffeomorph.contMDiff_of_comp_eq_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.IsLocalDiffeomorph.contMDiff_of_comp_eq_self ``Submission.DifferentialGeometry.IsLocalDiffeomorph.contMDiff_of_comp_eq_self

theorem coveringDeckGroup_contMDiff
    {p : M → N} (hp : IsLocalDiffeomorph I J n p)
    (γ : coveringDeckGroup p) :
    ContMDiff I I n (fun x : M => γ • x) :=
  IsLocalDiffeomorph.contMDiff_of_comp_eq_self hp γ.property.1 (by
    funext x
    exact coveringDeckGroup_map γ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.coveringDeckGroup_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.coveringDeckGroup_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.coveringDeckGroup_contMDiff ``Submission.DifferentialGeometry.coveringDeckGroup_contMDiff

noncomputable def coveringDeckGroupDiffeomorph
    {p : M → N} (hp : IsLocalDiffeomorph I J n p)
    (γ : coveringDeckGroup p) : M ≃ₘ^n⟮I, I⟯ M where
  toEquiv := γ.1
  contMDiff_toFun := coveringDeckGroup_contMDiff hp γ
  contMDiff_invFun := by
    change ContMDiff I I n (fun x : M => γ⁻¹ • x)
    exact coveringDeckGroup_contMDiff hp γ⁻¹

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.coveringDeckGroupDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.coveringDeckGroupDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.coveringDeckGroupDiffeomorph ``Submission.DifferentialGeometry.coveringDeckGroupDiffeomorph

@[simp] theorem coveringDeckGroupDiffeomorph_apply
    {p : M → N} (hp : IsLocalDiffeomorph I J n p)
    (γ : coveringDeckGroup p) (x : M) :
    coveringDeckGroupDiffeomorph hp γ x = γ • x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.coveringDeckGroupDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.coveringDeckGroupDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.coveringDeckGroupDiffeomorph_apply ``Submission.DifferentialGeometry.coveringDeckGroupDiffeomorph_apply

@[simp] theorem coveringDeckGroupDiffeomorph_symm_apply
    {p : M → N} (hp : IsLocalDiffeomorph I J n p)
    (γ : coveringDeckGroup p) (x : M) :
    (coveringDeckGroupDiffeomorph hp γ).symm x = γ⁻¹ • x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.coveringDeckGroupDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.coveringDeckGroupDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.coveringDeckGroupDiffeomorph_symm_apply ``Submission.DifferentialGeometry.coveringDeckGroupDiffeomorph_symm_apply

end DifferentialGeometry
