import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace CovariantDerivative
open _root_.CovariantDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open _root_.CovariantDerivative in
def trivial : CovariantDerivative I F (Bundle.Trivial M F) where
  toFun σ x := mvfderiv (I := I) σ x
  isCovariantDerivativeOnUniv := by
    constructor
    · intro σ τ x hσ hτ hx
      have hσ' : MDifferentiableAt I 𝓘(𝕜, F) σ x :=
        (mdifferentiableAt_section (F := F) (E := Bundle.Trivial M F) I σ).mp hσ
      have hτ' : MDifferentiableAt I 𝓘(𝕜, F) τ x :=
        (mdifferentiableAt_section (F := F) (E := Bundle.Trivial M F) I τ).mp hτ
      exact mvfderiv_add hσ' hτ'
    · intro σ g x hσ hg hx
      have hσ' : MDifferentiableAt I 𝓘(𝕜, F) σ x :=
        (mdifferentiableAt_section (F := F) (E := Bundle.Trivial M F) I σ).mp hσ
      exact mvfderiv_smul hg hσ'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.trivial then
    throwError "Refusing to shadow existing declaration CovariantDerivative.trivial"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.trivial ``Submission.CovariantDerivative.trivial

open _root_.CovariantDerivative in
@[simp] theorem trivial_apply (σ : M → F) (x : M) :
    trivial I M F σ x = mvfderiv (I := I) σ x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.trivial_apply then
    throwError "Refusing to shadow existing declaration CovariantDerivative.trivial_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.trivial_apply ``Submission.CovariantDerivative.trivial_apply

variable [IsManifold I 1 M] (n : WithTop ℕ∞)

open _root_.CovariantDerivative in
instance trivial_contMDiff : _root_.CovariantDerivative.ContMDiffCovariantDerivative (trivial I M F) n where
  contMDiff := by
    constructor
    intro σ hσ
    rw [contMDiffOn_univ] at hσ ⊢
    intro x₀
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    have hσ' : ContMDiffAt I 𝓘(𝕜, F) (n + 1) σ x₀ :=
      (_root_.Bundle.contMDiffAt_section (F := F) (E := Bundle.Trivial M F) x₀).mp (hσ x₀)
    have h := hσ'.mfderiv_const (m := n) (le_refl _)
    convert h using 1
    ext x v
    simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
      Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.continuousLinearMapAt_trivialization,
      TangentBundle.continuousLinearMapAt_model_space,
      trivial_apply, mvfderiv, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_id', id_eq]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.trivial_contMDiff then
    throwError "Refusing to shadow existing declaration CovariantDerivative.trivial_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.trivial_contMDiff ``Submission.CovariantDerivative.trivial_contMDiff

end CovariantDerivative
