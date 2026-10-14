import Submission.DifferentialGeometry.Tensor.Alternating.Bundle.Defs
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Fiber

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Bundle _root_.Submission.Bundle _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] {J : ModelWithCorners 𝕜 EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : WithTop ℕ∞} {k : ℕ} {b : P → M}
  {a : ∀ p, V (b p) [⋀^Fin k]→L[𝕜] 𝕜}
  {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 k F V (b p)}
  {s : Set P} {p₀ : P}

private theorem alternating_trivialization_apply (x₀ x : M)
    (a : V x [⋀^Fin k]→L[𝕜] 𝕜) :
    (_root_.FiberBundle.trivializationAt (F [⋀^Fin k]→L[𝕜] 𝕜)
      (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜))
      x₀ ⟨x, a⟩).2 = a.compContinuousLinearMap ((_root_.FiberBundle.trivializationAt F V x₀).symmL 𝕜 x) := by
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply]
  ext v
  simp [ContinuousAlternatingMap.inCoordinates]

run_cmd do
  let target := ``Submission.alternating_trivialization_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `alternating_trivialization_apply target :: scope.openDecls } }

open _root_.ContMDiffWithinAt in
theorem ContMDiffWithinAt.alternating_bundle_toMultilinear
    (ha : ContMDiffWithinAt J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, a p⟩ : _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) s p₀) :
    ContMDiffWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, (a p).toContinuousMultilinearMap⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) s p₀ := by
  rw [_root_.Bundle.contMDiffWithinAt_totalSpace] at ha ⊢
  refine ⟨ha.1, ?_⟩
  let L : (F [⋀^Fin k]→L[𝕜] 𝕜) →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜 :=
    ContinuousAlternatingMap.toContinuousMultilinearMapCLM
    (E := F) (F := 𝕜) (ι := Fin k) 𝕜
  have hL : ContMDiff 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜) n L :=
    ContinuousLinearMap.contMDiff (𝕜 := 𝕜) (E := F [⋀^Fin k]→L[𝕜] 𝕜)
      (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜) L
  have h := hL.contMDiffAt.comp_contMDiffWithinAt p₀ ha.2
  have heq (p : P) :
      (_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V) (b p₀) ⟨b p, (a p).toContinuousMultilinearMap⟩).2 =
      L ((_root_.FiberBundle.trivializationAt (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜))
        (b p₀) ⟨b p, a p⟩).2) := by
    rw [alternating_trivialization_apply]
    rfl
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall heq) (heq p₀)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffWithinAt
  let env ← Lean.getEnv
  if env.contains `ContMDiffWithinAt.alternating_bundle_toMultilinear then
    throwError "Refusing to shadow existing declaration ContMDiffWithinAt.alternating_bundle_toMultilinear"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffWithinAt.alternating_bundle_toMultilinear ``Submission.ContMDiffWithinAt.alternating_bundle_toMultilinear

open _root_.ContMDiffWithinAt in
theorem ContMDiffWithinAt.multilinear_bundle_alternatization
    (hT : ContMDiffWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) s p₀) :
    ContMDiffWithinAt J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, ContinuousMultilinearMap.alternatizationCLM (T p)⟩ :
        _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) s p₀ := by
  rw [_root_.Bundle.contMDiffWithinAt_totalSpace] at hT ⊢
  refine ⟨hT.1, ?_⟩
  let L : ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜 →L[𝕜]
      F [⋀^Fin k]→L[𝕜] 𝕜 := ContinuousMultilinearMap.alternatizationCLM
  have hL : ContMDiff 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
      𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜) n L :=
    ContinuousLinearMap.contMDiff (𝕜 := 𝕜)
      (E := ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
      (F := F [⋀^Fin k]→L[𝕜] 𝕜) L
  have h := hL.contMDiffAt.comp_contMDiffWithinAt p₀ hT.2
  have heq (p : P) :
      (_root_.FiberBundle.trivializationAt (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜))
        (b p₀) ⟨b p, ContinuousMultilinearMap.alternatizationCLM (T p)⟩).2 =
      L ((_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V) (b p₀) ⟨b p, T p⟩).2) := by
    rw [alternating_trivialization_apply]
    exact (ContinuousMultilinearMap.alternatizationCLM_compContinuousLinearMap
      (T p) ((_root_.FiberBundle.trivializationAt F V (b p₀)).symmL 𝕜 (b p))).symm
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall heq) (heq p₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffWithinAt.multilinear_bundle_alternatization then
    throwError "Refusing to shadow existing declaration ContMDiffWithinAt.multilinear_bundle_alternatization"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffWithinAt.multilinear_bundle_alternatization ``Submission.ContMDiffWithinAt.multilinear_bundle_alternatization

open _root_.ContMDiffAt in
theorem ContMDiffAt.alternating_bundle_toMultilinear
    (ha : ContMDiffAt J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, a p⟩ : _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) p₀) :
    ContMDiffAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, (a p).toContinuousMultilinearMap⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) p₀ :=
  ContMDiffWithinAt.alternating_bundle_toMultilinear ha

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffAt
  let env ← Lean.getEnv
  if env.contains `ContMDiffAt.alternating_bundle_toMultilinear then
    throwError "Refusing to shadow existing declaration ContMDiffAt.alternating_bundle_toMultilinear"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffAt.alternating_bundle_toMultilinear ``Submission.ContMDiffAt.alternating_bundle_toMultilinear

open _root_.ContMDiffOn in
theorem ContMDiffOn.alternating_bundle_toMultilinear
    (ha : ContMDiffOn J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, a p⟩ : _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) s) :
    ContMDiffOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, (a p).toContinuousMultilinearMap⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) s :=
  fun p hp => (ha p hp).alternating_bundle_toMultilinear

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffOn
  let env ← Lean.getEnv
  if env.contains `ContMDiffOn.alternating_bundle_toMultilinear then
    throwError "Refusing to shadow existing declaration ContMDiffOn.alternating_bundle_toMultilinear"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffOn.alternating_bundle_toMultilinear ``Submission.ContMDiffOn.alternating_bundle_toMultilinear

open _root_.ContMDiff in
theorem ContMDiff.alternating_bundle_toMultilinear
    (ha : ContMDiff J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, a p⟩ : _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜))))) :
    ContMDiff J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, (a p).toContinuousMultilinearMap⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) :=
  fun p => (ha p).alternating_bundle_toMultilinear

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiff
  let env ← Lean.getEnv
  if env.contains `ContMDiff.alternating_bundle_toMultilinear then
    throwError "Refusing to shadow existing declaration ContMDiff.alternating_bundle_toMultilinear"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiff.alternating_bundle_toMultilinear ``Submission.ContMDiff.alternating_bundle_toMultilinear

open _root_.ContMDiffAt in
theorem ContMDiffAt.multilinear_bundle_alternatization
    (hT : ContMDiffAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) p₀) :
    ContMDiffAt J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, ContinuousMultilinearMap.alternatizationCLM (T p)⟩ :
        _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) p₀ :=
  ContMDiffWithinAt.multilinear_bundle_alternatization hT

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffAt.multilinear_bundle_alternatization then
    throwError "Refusing to shadow existing declaration ContMDiffAt.multilinear_bundle_alternatization"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffAt.multilinear_bundle_alternatization ``Submission.ContMDiffAt.multilinear_bundle_alternatization

open _root_.ContMDiffOn in
theorem ContMDiffOn.multilinear_bundle_alternatization
    (hT : ContMDiffOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) s) :
    ContMDiffOn J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, ContinuousMultilinearMap.alternatizationCLM (T p)⟩ :
        _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) s :=
  fun p hp => (hT p hp).multilinear_bundle_alternatization

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffOn.multilinear_bundle_alternatization then
    throwError "Refusing to shadow existing declaration ContMDiffOn.multilinear_bundle_alternatization"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffOn.multilinear_bundle_alternatization ``Submission.ContMDiffOn.multilinear_bundle_alternatization

open _root_.ContMDiff in
theorem ContMDiff.multilinear_bundle_alternatization
    (hT : ContMDiff J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V)))) :
    ContMDiff J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, ContinuousMultilinearMap.alternatizationCLM (T p)⟩ :
        _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) :=
  fun p => (hT p).multilinear_bundle_alternatization

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiff.multilinear_bundle_alternatization then
    throwError "Refusing to shadow existing declaration ContMDiff.multilinear_bundle_alternatization"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiff.multilinear_bundle_alternatization ``Submission.ContMDiff.multilinear_bundle_alternatization

open _root_.MDifferentiableWithinAt in
theorem MDifferentiableWithinAt.alternating_bundle_toMultilinear
    (ha : MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, a p⟩ : _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) s p₀) :
    MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, (a p).toContinuousMultilinearMap⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) s p₀ := by
  have hmap : ContMDiff (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜))
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) 1
      (fun q : _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)) =>
        (⟨q.1, q.2.toContinuousMultilinearMap⟩ : _root_.Bundle.TotalSpace
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
          (Bundle.continuousMultilinearMap 𝕜 k F V))) :=
    ContMDiff.alternating_bundle_toMultilinear contMDiff_id
  exact (hmap.mdifferentiableAt (by norm_num)).comp_mdifferentiableWithinAt p₀ ha

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MDifferentiableWithinAt
  let env ← Lean.getEnv
  if env.contains `MDifferentiableWithinAt.alternating_bundle_toMultilinear then
    throwError "Refusing to shadow existing declaration MDifferentiableWithinAt.alternating_bundle_toMultilinear"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableWithinAt.alternating_bundle_toMultilinear ``Submission.MDifferentiableWithinAt.alternating_bundle_toMultilinear

open _root_.MDifferentiableAt in
theorem MDifferentiableAt.alternating_bundle_toMultilinear
    (ha : MDifferentiableAt J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, a p⟩ : _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) p₀) :
    MDifferentiableAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, (a p).toContinuousMultilinearMap⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) p₀ :=
  MDifferentiableWithinAt.alternating_bundle_toMultilinear ha

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MDifferentiableAt
  let env ← Lean.getEnv
  if env.contains `MDifferentiableAt.alternating_bundle_toMultilinear then
    throwError "Refusing to shadow existing declaration MDifferentiableAt.alternating_bundle_toMultilinear"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableAt.alternating_bundle_toMultilinear ``Submission.MDifferentiableAt.alternating_bundle_toMultilinear

open _root_.MDifferentiableOn in
theorem MDifferentiableOn.alternating_bundle_toMultilinear
    (ha : MDifferentiableOn J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, a p⟩ : _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) s) :
    MDifferentiableOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, (a p).toContinuousMultilinearMap⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) s :=
  fun p hp => (ha p hp).alternating_bundle_toMultilinear

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MDifferentiableOn
  let env ← Lean.getEnv
  if env.contains `MDifferentiableOn.alternating_bundle_toMultilinear then
    throwError "Refusing to shadow existing declaration MDifferentiableOn.alternating_bundle_toMultilinear"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableOn.alternating_bundle_toMultilinear ``Submission.MDifferentiableOn.alternating_bundle_toMultilinear

open _root_.MDifferentiable in
theorem MDifferentiable.alternating_bundle_toMultilinear
    (ha : MDifferentiable J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, a p⟩ : _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜))))) :
    MDifferentiable J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, (a p).toContinuousMultilinearMap⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) :=
  fun p => (ha p).alternating_bundle_toMultilinear

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MDifferentiable
  let env ← Lean.getEnv
  if env.contains `MDifferentiable.alternating_bundle_toMultilinear then
    throwError "Refusing to shadow existing declaration MDifferentiable.alternating_bundle_toMultilinear"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiable.alternating_bundle_toMultilinear ``Submission.MDifferentiable.alternating_bundle_toMultilinear

open _root_.MDifferentiableWithinAt in
theorem MDifferentiableWithinAt.multilinear_bundle_alternatization
    (hT : MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) s p₀) :
    MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, ContinuousMultilinearMap.alternatizationCLM (T p)⟩ :
        _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) s p₀ := by
  have hmap : ContMDiff
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)) 1
      (fun q : _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V) =>
        (⟨q.1, ContinuousMultilinearMap.alternatizationCLM q.2⟩ : _root_.Bundle.TotalSpace
          (F [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) :=
    ContMDiff.multilinear_bundle_alternatization contMDiff_id
  exact (hmap.mdifferentiableAt (by norm_num)).comp_mdifferentiableWithinAt p₀ hT

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MDifferentiableWithinAt.multilinear_bundle_alternatization then
    throwError "Refusing to shadow existing declaration MDifferentiableWithinAt.multilinear_bundle_alternatization"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableWithinAt.multilinear_bundle_alternatization ``Submission.MDifferentiableWithinAt.multilinear_bundle_alternatization

open _root_.MDifferentiableAt in
theorem MDifferentiableAt.multilinear_bundle_alternatization
    (hT : MDifferentiableAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) p₀) :
    MDifferentiableAt J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, ContinuousMultilinearMap.alternatizationCLM (T p)⟩ :
        _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) p₀ :=
  MDifferentiableWithinAt.multilinear_bundle_alternatization hT

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MDifferentiableAt.multilinear_bundle_alternatization then
    throwError "Refusing to shadow existing declaration MDifferentiableAt.multilinear_bundle_alternatization"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableAt.multilinear_bundle_alternatization ``Submission.MDifferentiableAt.multilinear_bundle_alternatization

open _root_.MDifferentiableOn in
theorem MDifferentiableOn.multilinear_bundle_alternatization
    (hT : MDifferentiableOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) s) :
    MDifferentiableOn J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, ContinuousMultilinearMap.alternatizationCLM (T p)⟩ :
        _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) s :=
  fun p hp => (hT p hp).multilinear_bundle_alternatization

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MDifferentiableOn.multilinear_bundle_alternatization then
    throwError "Refusing to shadow existing declaration MDifferentiableOn.multilinear_bundle_alternatization"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableOn.multilinear_bundle_alternatization ``Submission.MDifferentiableOn.multilinear_bundle_alternatization

open _root_.MDifferentiable in
theorem MDifferentiable.multilinear_bundle_alternatization
    (hT : MDifferentiable J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V)))) :
    MDifferentiable J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, ContinuousMultilinearMap.alternatizationCLM (T p)⟩ :
        _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) :=
  fun p => (hT p).multilinear_bundle_alternatization

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MDifferentiable.multilinear_bundle_alternatization then
    throwError "Refusing to shadow existing declaration MDifferentiable.multilinear_bundle_alternatization"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiable.multilinear_bundle_alternatization ``Submission.MDifferentiable.multilinear_bundle_alternatization
