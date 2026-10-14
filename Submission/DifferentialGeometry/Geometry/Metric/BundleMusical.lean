import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {J : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω}
  {b : P → M} {σ : ∀ p, V (b p)} {s : Set P} {p₀ : P}

section ContMDiff

variable [IsContMDiffRiemannianBundle I n F V]

open _root_.ContMDiffWithinAt in
theorem ContMDiffWithinAt.innerSL_bundle
    (hσ : ContMDiffWithinAt J (I.prod 𝓘(ℝ, F)) n
      (fun p => (⟨b p, σ p⟩ : _root_.Bundle.TotalSpace F V)) s p₀) :
    ContMDiffWithinAt J (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun p => (⟨b p, innerSL ℝ (σ p)⟩ : _root_.Bundle.TotalSpace (F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] ℝ))) s p₀ := by
  obtain ⟨g, hg, heq⟩ :=
    (inferInstance : IsContMDiffRiemannianBundle I n F V).exists_contMDiff
  have hb := ((_root_.Bundle.contMDiffWithinAt_totalSpace (F := F)).mp hσ).1
  have hgc : ContMDiffWithinAt J (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun p => (⟨b p, g (b p)⟩ : _root_.Bundle.TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] V x →L[ℝ] ℝ))) s p₀ :=
    (hg (b p₀)).comp_contMDiffWithinAt p₀ hb
  have h := hgc.clm_bundle_apply (F₂ := F →L[ℝ] ℝ)
    (E₂ := fun x => V x →L[ℝ] ℝ) hσ
  convert h using 1
  funext p
  congr 1
  ext w
  exact heq (b p) (σ p) w

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffWithinAt
  let env ← Lean.getEnv
  if env.contains `ContMDiffWithinAt.innerSL_bundle then
    throwError "Refusing to shadow existing declaration ContMDiffWithinAt.innerSL_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffWithinAt.innerSL_bundle ``Submission.ContMDiffWithinAt.innerSL_bundle

open _root_.ContMDiffAt in
theorem ContMDiffAt.innerSL_bundle
    (hσ : ContMDiffAt J (I.prod 𝓘(ℝ, F)) n
      (fun p => (⟨b p, σ p⟩ : _root_.Bundle.TotalSpace F V)) p₀) :
    ContMDiffAt J (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun p => (⟨b p, innerSL ℝ (σ p)⟩ : _root_.Bundle.TotalSpace (F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] ℝ))) p₀ :=
  ContMDiffWithinAt.innerSL_bundle hσ

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffAt
  let env ← Lean.getEnv
  if env.contains `ContMDiffAt.innerSL_bundle then
    throwError "Refusing to shadow existing declaration ContMDiffAt.innerSL_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffAt.innerSL_bundle ``Submission.ContMDiffAt.innerSL_bundle

open _root_.ContMDiffOn in
theorem ContMDiffOn.innerSL_bundle
    (hσ : ContMDiffOn J (I.prod 𝓘(ℝ, F)) n
      (fun p => (⟨b p, σ p⟩ : _root_.Bundle.TotalSpace F V)) s) :
    ContMDiffOn J (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun p => (⟨b p, innerSL ℝ (σ p)⟩ : _root_.Bundle.TotalSpace (F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] ℝ))) s :=
  fun p hp => (hσ p hp).innerSL_bundle

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffOn
  let env ← Lean.getEnv
  if env.contains `ContMDiffOn.innerSL_bundle then
    throwError "Refusing to shadow existing declaration ContMDiffOn.innerSL_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffOn.innerSL_bundle ``Submission.ContMDiffOn.innerSL_bundle

open _root_.ContMDiff in
theorem ContMDiff.innerSL_bundle
    (hσ : ContMDiff J (I.prod 𝓘(ℝ, F)) n
      (fun p => (⟨b p, σ p⟩ : _root_.Bundle.TotalSpace F V))) :
    ContMDiff J (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun p => (⟨b p, innerSL ℝ (σ p)⟩ : _root_.Bundle.TotalSpace (F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] ℝ))) :=
  fun p => (hσ p).innerSL_bundle

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiff
  let env ← Lean.getEnv
  if env.contains `ContMDiff.innerSL_bundle then
    throwError "Refusing to shadow existing declaration ContMDiff.innerSL_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiff.innerSL_bundle ``Submission.ContMDiff.innerSL_bundle

end ContMDiff

section MDifferentiable

variable [IsContMDiffRiemannianBundle I 1 F V]

open _root_.MDifferentiableWithinAt in
theorem MDifferentiableWithinAt.innerSL_bundle
    (hσ : MDifferentiableWithinAt J (I.prod 𝓘(ℝ, F))
      (fun p => (⟨b p, σ p⟩ : _root_.Bundle.TotalSpace F V)) s p₀) :
    MDifferentiableWithinAt J (I.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun p => (⟨b p, innerSL ℝ (σ p)⟩ : _root_.Bundle.TotalSpace (F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] ℝ))) s p₀ := by
  obtain ⟨g, hg, heq⟩ :=
    (inferInstance : IsContMDiffRiemannianBundle I 1 F V).exists_contMDiff
  have hb := ((mdifferentiableWithinAt_totalSpace (F := F) I _).mp hσ).1
  have hgc : MDifferentiableWithinAt J (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ))
      (fun p => (⟨b p, g (b p)⟩ : _root_.Bundle.TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] V x →L[ℝ] ℝ))) s p₀ :=
    ((hg (b p₀)).mdifferentiableAt (by simp)).comp_mdifferentiableWithinAt p₀ hb
  have h := hgc.clm_bundle_apply (F₂ := F →L[ℝ] ℝ)
    (E₂ := fun x => V x →L[ℝ] ℝ) hσ
  convert h using 1
  funext p
  congr 1
  ext w
  exact heq (b p) (σ p) w

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MDifferentiableWithinAt
  let env ← Lean.getEnv
  if env.contains `MDifferentiableWithinAt.innerSL_bundle then
    throwError "Refusing to shadow existing declaration MDifferentiableWithinAt.innerSL_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableWithinAt.innerSL_bundle ``Submission.MDifferentiableWithinAt.innerSL_bundle

open _root_.MDifferentiableAt in
theorem MDifferentiableAt.innerSL_bundle
    (hσ : MDifferentiableAt J (I.prod 𝓘(ℝ, F))
      (fun p => (⟨b p, σ p⟩ : _root_.Bundle.TotalSpace F V)) p₀) :
    MDifferentiableAt J (I.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun p => (⟨b p, innerSL ℝ (σ p)⟩ : _root_.Bundle.TotalSpace (F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] ℝ))) p₀ :=
  MDifferentiableWithinAt.innerSL_bundle hσ

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MDifferentiableAt
  let env ← Lean.getEnv
  if env.contains `MDifferentiableAt.innerSL_bundle then
    throwError "Refusing to shadow existing declaration MDifferentiableAt.innerSL_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableAt.innerSL_bundle ``Submission.MDifferentiableAt.innerSL_bundle

open _root_.MDifferentiableOn in
theorem MDifferentiableOn.innerSL_bundle
    (hσ : MDifferentiableOn J (I.prod 𝓘(ℝ, F))
      (fun p => (⟨b p, σ p⟩ : _root_.Bundle.TotalSpace F V)) s) :
    MDifferentiableOn J (I.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun p => (⟨b p, innerSL ℝ (σ p)⟩ : _root_.Bundle.TotalSpace (F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] ℝ))) s :=
  fun p hp => (hσ p hp).innerSL_bundle

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MDifferentiableOn
  let env ← Lean.getEnv
  if env.contains `MDifferentiableOn.innerSL_bundle then
    throwError "Refusing to shadow existing declaration MDifferentiableOn.innerSL_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableOn.innerSL_bundle ``Submission.MDifferentiableOn.innerSL_bundle

open _root_.MDifferentiable in
theorem MDifferentiable.innerSL_bundle
    (hσ : MDifferentiable J (I.prod 𝓘(ℝ, F))
      (fun p => (⟨b p, σ p⟩ : _root_.Bundle.TotalSpace F V))) :
    MDifferentiable J (I.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun p => (⟨b p, innerSL ℝ (σ p)⟩ : _root_.Bundle.TotalSpace (F →L[ℝ] ℝ)
        (fun x => V x →L[ℝ] ℝ))) :=
  fun p => (hσ p).innerSL_bundle

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MDifferentiable
  let env ← Lean.getEnv
  if env.contains `MDifferentiable.innerSL_bundle then
    throwError "Refusing to shadow existing declaration MDifferentiable.innerSL_bundle"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiable.innerSL_bundle ``Submission.MDifferentiable.innerSL_bundle

end MDifferentiable
