import Submission.DifferentialGeometry.Tensor.Alternating.BundleMaps
import Submission.DifferentialGeometry.Tensor.Multilinear.BundleComp
import Submission.DifferentialGeometry.Tensor.Alternating.Coordinates.Basis
import Submission.DifferentialGeometry.Bundle.Hom.Regularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] {J : ModelWithCorners 𝕜 EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, NormedSpace 𝕜 (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, NormedSpace 𝕜 (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  {n : ℕ∞ω} {k : ℕ} {b : P → M}
  {T : ∀ p, V₂ (b p) [⋀^Fin k]→L[𝕜] 𝕜}
  {A : ∀ p, V₁ (b p) →L[𝕜] V₂ (b p)} {s : Set P} {p₀ : P}

open _root_.ContMDiffWithinAt in
theorem ContMDiffWithinAt.alternating_bundle_comp
    (hT : ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₂ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace (F₂ [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₂ V₂ 𝕜 (Bundle.Trivial M 𝕜)))) s p₀)
    (hA : ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, A p⟩ : _root_.Bundle.TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s p₀) :
    ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₁ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, (T p).compContinuousLinearMap (A p)⟩ :
        _root_.Bundle.TotalSpace (F₁ [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₁ V₁ 𝕜 (Bundle.Trivial M 𝕜)))) s p₀ := by
  have h := (hT.alternating_bundle_toMultilinear.multilinear_bundle_comp
    (fun _ => hA)).multilinear_bundle_alternatization
  simpa only [ContinuousMultilinearMap.alternatizationCLM_compContinuousLinearMap,
    ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffWithinAt.alternating_bundle_comp then
    throwError "Refusing to shadow existing declaration ContMDiffWithinAt.alternating_bundle_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffWithinAt.alternating_bundle_comp ``Submission.ContMDiffWithinAt.alternating_bundle_comp

open _root_.ContMDiffAt in
theorem ContMDiffAt.alternating_bundle_comp
    (hT : ContMDiffAt J (I.prod 𝓘(𝕜, F₂ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace (F₂ [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₂ V₂ 𝕜 (Bundle.Trivial M 𝕜)))) p₀)
    (hA : ContMDiffAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, A p⟩ : _root_.Bundle.TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) p₀) :
    ContMDiffAt J (I.prod 𝓘(𝕜, F₁ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, (T p).compContinuousLinearMap (A p)⟩ :
        _root_.Bundle.TotalSpace (F₁ [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₁ V₁ 𝕜 (Bundle.Trivial M 𝕜)))) p₀ :=
  ContMDiffWithinAt.alternating_bundle_comp hT hA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffAt.alternating_bundle_comp then
    throwError "Refusing to shadow existing declaration ContMDiffAt.alternating_bundle_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffAt.alternating_bundle_comp ``Submission.ContMDiffAt.alternating_bundle_comp

open _root_.ContMDiffOn in
theorem ContMDiffOn.alternating_bundle_comp
    (hT : ContMDiffOn J (I.prod 𝓘(𝕜, F₂ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace (F₂ [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₂ V₂ 𝕜 (Bundle.Trivial M 𝕜)))) s)
    (hA : ContMDiffOn J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, A p⟩ : _root_.Bundle.TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s) :
    ContMDiffOn J (I.prod 𝓘(𝕜, F₁ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, (T p).compContinuousLinearMap (A p)⟩ :
        _root_.Bundle.TotalSpace (F₁ [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₁ V₁ 𝕜 (Bundle.Trivial M 𝕜)))) s :=
  fun p hp => (hT p hp).alternating_bundle_comp (hA p hp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffOn.alternating_bundle_comp then
    throwError "Refusing to shadow existing declaration ContMDiffOn.alternating_bundle_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffOn.alternating_bundle_comp ``Submission.ContMDiffOn.alternating_bundle_comp

open _root_.ContMDiff in
theorem ContMDiff.alternating_bundle_comp
    (hT : ContMDiff J (I.prod 𝓘(𝕜, F₂ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace (F₂ [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₂ V₂ 𝕜 (Bundle.Trivial M 𝕜)))))
    (hA : ContMDiff J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, A p⟩ : _root_.Bundle.TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x)))) :
    ContMDiff J (I.prod 𝓘(𝕜, F₁ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, (T p).compContinuousLinearMap (A p)⟩ :
        _root_.Bundle.TotalSpace (F₁ [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₁ V₁ 𝕜 (Bundle.Trivial M 𝕜)))) :=
  fun p => (hT p).alternating_bundle_comp (hA p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiff.alternating_bundle_comp then
    throwError "Refusing to shadow existing declaration ContMDiff.alternating_bundle_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiff.alternating_bundle_comp ``Submission.ContMDiff.alternating_bundle_comp

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁]

open _root_.ContMDiff in
theorem ContMDiff.alternating_bundle_congrLeft
    (φ : ∀ x, V₁ x ≃L[𝕜] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : _root_.Bundle.TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x)))) (k : ℕ) :
    ContMDiff I
      (I.prod 𝓘(𝕜, (F₁ [⋀^Fin k]→L[𝕜] 𝕜) →L[𝕜] F₂ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun x => (⟨x, ((φ x).continuousAlternatingMapCongrLeft (ι := Fin k)
        (F := 𝕜)).toContinuousLinearMap⟩ : _root_.Bundle.TotalSpace
          ((F₁ [⋀^Fin k]→L[𝕜] 𝕜) →L[𝕜] F₂ [⋀^Fin k]→L[𝕜] 𝕜)
          (fun x => (V₁ x [⋀^Fin k]→L[𝕜] 𝕜) →L[𝕜] V₂ x [⋀^Fin k]→L[𝕜] 𝕜))) := by
  let _ : CompleteSpace F₁ := FiniteDimensional.complete 𝕜 F₁
  let _ : FiniteDimensional 𝕜 (F₁ [⋀^Fin k]→L[𝕜] 𝕜) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
      (Module.finBasis 𝕜 F₁)).finiteDimensional_of_finite
  have hφinv : ContMDiff I (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x => (⟨x, (φ x).symm.toContinuousLinearMap⟩ : _root_.Bundle.TotalSpace (F₂ →L[𝕜] F₁)
        (fun x => V₂ x →L[𝕜] V₁ x))) := by
    simpa only [ContinuousLinearMap.inverse_equiv] using
      hφ.clm_bundle_inverse (fun _ => ContinuousLinearMap.isInvertible_equiv)
  apply ContMDiff.clm_bundle_of_map
  exact (contMDiff_id : ContMDiff
      (I.prod 𝓘(𝕜, F₁ [⋀^Fin k]→L[𝕜] 𝕜))
      (I.prod 𝓘(𝕜, F₁ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p : _root_.Bundle.TotalSpace (F₁ [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₁ V₁ 𝕜 (Bundle.Trivial M 𝕜)) => p))
    |>.alternating_bundle_comp (hφinv.comp (_root_.Bundle.contMDiff_proj _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiff.alternating_bundle_congrLeft then
    throwError "Refusing to shadow existing declaration ContMDiff.alternating_bundle_congrLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiff.alternating_bundle_congrLeft ``Submission.ContMDiff.alternating_bundle_congrLeft
