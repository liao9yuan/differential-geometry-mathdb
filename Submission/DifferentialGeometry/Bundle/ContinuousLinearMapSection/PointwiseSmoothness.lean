import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.Diffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Function
open scoped _root_.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace HB X]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [FiniteDimensional 𝕜 F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
variable {n : WithTop ℕ∞}

lemma contMDiffAt_clm_of_pointwise
    {A : X → (F₁ →L[𝕜] F₂)} {x : X}
    (h : ∀ v, ContMDiffAt IB 𝓘(𝕜, F₂) n (fun q => A q v) x) :
    ContMDiffAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂) n A x := by
  let d := Module.finrank 𝕜 F₁
  have hd : d = Module.finrank 𝕜 (Fin d → 𝕜) := (Module.finrank_fin_fun 𝕜).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F₂ ≃L[𝕜] F₂)).trans
    (ContinuousLinearEquiv.piRing (Fin d))
  rw [← _root_.Function.id_comp A, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contMDiff.contMDiffAt.comp _
    (contMDiffAt_pi_space.mpr fun _ => h _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `contMDiffAt_clm_of_pointwise then
    throwError "Refusing to shadow existing declaration contMDiffAt_clm_of_pointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `contMDiffAt_clm_of_pointwise ``Submission.contMDiffAt_clm_of_pointwise

lemma contMDiffWithinAt_clm_of_pointwise
    {A : X → (F₁ →L[𝕜] F₂)} {s : Set X} {x : X}
    (h : ∀ v, ContMDiffWithinAt IB 𝓘(𝕜, F₂) n (fun q => A q v) s x) :
    ContMDiffWithinAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂) n A s x := by
  let d := Module.finrank 𝕜 F₁
  have hd : d = Module.finrank 𝕜 (Fin d → 𝕜) := (Module.finrank_fin_fun 𝕜).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F₂ ≃L[𝕜] F₂)).trans
    (ContinuousLinearEquiv.piRing (Fin d))
  rw [← _root_.Function.id_comp A, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt _
    (contMDiffWithinAt_pi_space.mpr fun _ => h _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `contMDiffWithinAt_clm_of_pointwise then
    throwError "Refusing to shadow existing declaration contMDiffWithinAt_clm_of_pointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `contMDiffWithinAt_clm_of_pointwise ``Submission.contMDiffWithinAt_clm_of_pointwise
