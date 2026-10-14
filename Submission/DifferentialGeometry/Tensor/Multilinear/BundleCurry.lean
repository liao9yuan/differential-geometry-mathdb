import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Fiber
import Mathlib.Geometry.Manifold.VectorBundle.Hom

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
  {T : ∀ p, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => V (b p)) 𝕜}
  {s : Set P} {p₀ : P}

private theorem curryLeftEquiv_inCoordinates
    (x₀ x : M) (hx : x ∈ (_root_.FiberBundle.trivializationAt F V x₀).baseSet)
    (T : Bundle.continuousMultilinearMap 𝕜 (k + 1) F V x) :
    ContinuousLinearMap.inCoordinates F V
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 k F V) x₀ x x₀ x
      (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k x T) =
    continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) => F) 𝕜
      ((_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V) x₀ ⟨x, T⟩).2) := by
  ext v w
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem]
  · change (T.curryLeft ((_root_.FiberBundle.trivializationAt F V x₀).symmL 𝕜 x v)).compContinuousLinearMap
      (fun _ => (_root_.FiberBundle.trivializationAt F V x₀).symmL 𝕜 x) w =
      (T.compContinuousLinearMap (fun _ => (_root_.FiberBundle.trivializationAt F V x₀).symmL 𝕜 x)).curryLeft v w
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.curryLeft_apply]
    congr 1
    ext i
    exact Fin.cases rfl (fun _ => rfl) i
  · exact hx

run_cmd do
  let target := ``Submission.curryLeftEquiv_inCoordinates
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `curryLeftEquiv_inCoordinates target :: scope.openDecls } }


open _root_.ContMDiffWithinAt in
theorem ContMDiffWithinAt.multilinear_bundle_curry_left
    (hT : ContMDiffWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) s p₀) :
    ContMDiffWithinAt J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p) (T p)⟩ : _root_.Bundle.TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) s p₀ := by
  rw [_root_.Bundle.contMDiffWithinAt_totalSpace] at hT
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨hT.1, ?_⟩
  let L : (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜) →L[𝕜]
      (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜) :=
    (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) => F) 𝕜).toContinuousLinearEquiv.toContinuousLinearMap
  have hL : ContMDiff
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
      𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜) n L :=
    ContinuousLinearMap.contMDiff (𝕜 := 𝕜)
      (E := ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
      (F := F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜) L
  have h := hL.contMDiffAt.comp_contMDiffWithinAt p₀ hT.2
  let e := _root_.FiberBundle.trivializationAt F V (b p₀)
  have hx : b p₀ ∈ e.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt F V (b p₀)
  apply h.congr_of_eventuallyEq
  · have hbase : ∀ᶠ p in 𝓝[s] p₀, b p ∈ e.baseSet :=
      hT.1.continuousWithinAt (e.open_baseSet.mem_nhds hx)
    filter_upwards [hbase] with p hp
    exact curryLeftEquiv_inCoordinates (b p₀) (b p) hp (T p)
  · exact curryLeftEquiv_inCoordinates (b p₀) (b p₀) hx (T p₀)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffWithinAt
  let env ← Lean.getEnv
  if env.contains `ContMDiffWithinAt.multilinear_bundle_curry_left then
    throwError "Refusing to shadow existing declaration ContMDiffWithinAt.multilinear_bundle_curry_left"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffWithinAt.multilinear_bundle_curry_left ``Submission.ContMDiffWithinAt.multilinear_bundle_curry_left

open _root_.ContMDiffAt in
theorem ContMDiffAt.multilinear_bundle_curry_left
    (hT : ContMDiffAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) p₀) :
    ContMDiffAt J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p) (T p)⟩ : _root_.Bundle.TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) p₀ :=
  ContMDiffWithinAt.multilinear_bundle_curry_left hT

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffAt
  let env ← Lean.getEnv
  if env.contains `ContMDiffAt.multilinear_bundle_curry_left then
    throwError "Refusing to shadow existing declaration ContMDiffAt.multilinear_bundle_curry_left"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffAt.multilinear_bundle_curry_left ``Submission.ContMDiffAt.multilinear_bundle_curry_left

open _root_.ContMDiffOn in
theorem ContMDiffOn.multilinear_bundle_curry_left
    (hT : ContMDiffOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) s) :
    ContMDiffOn J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p) (T p)⟩ : _root_.Bundle.TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) s :=
  fun p hp => (hT p hp).multilinear_bundle_curry_left

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffOn
  let env ← Lean.getEnv
  if env.contains `ContMDiffOn.multilinear_bundle_curry_left then
    throwError "Refusing to shadow existing declaration ContMDiffOn.multilinear_bundle_curry_left"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffOn.multilinear_bundle_curry_left ``Submission.ContMDiffOn.multilinear_bundle_curry_left

open _root_.ContMDiff in
theorem ContMDiff.multilinear_bundle_curry_left
    (hT : ContMDiff J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V)))) :
    ContMDiff J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p) (T p)⟩ : _root_.Bundle.TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) :=
  fun p => (hT p).multilinear_bundle_curry_left

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiff
  let env ← Lean.getEnv
  if env.contains `ContMDiff.multilinear_bundle_curry_left then
    throwError "Refusing to shadow existing declaration ContMDiff.multilinear_bundle_curry_left"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiff.multilinear_bundle_curry_left ``Submission.ContMDiff.multilinear_bundle_curry_left

open _root_.ContMDiffWithinAt in
theorem ContMDiffWithinAt.multilinear_bundle_uncurry_left
    {A : ∀ p, V (b p) →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V (b p)}
    (hA : ContMDiffWithinAt J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, A p⟩ : _root_.Bundle.TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) s p₀) :
    ContMDiffWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)) n
      (fun p => (⟨b p,
        (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p)).symm (A p)⟩ :
        _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) s p₀ := by
  rw [contMDiffWithinAt_hom_bundle] at hA
  rw [_root_.Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨hA.1, ?_⟩
  let L := (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) => F) 𝕜).toContinuousLinearEquiv
  have hL : ContMDiff
      𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜) n L.symm :=
    ContinuousLinearMap.contMDiff (𝕜 := 𝕜)
      (E := F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
      (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜) L.symm.toContinuousLinearMap
  have h := hL.contMDiffAt.comp_contMDiffWithinAt p₀ hA.2
  let e := _root_.FiberBundle.trivializationAt F V (b p₀)
  have hx : b p₀ ∈ e.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt F V (b p₀)
  have hinv (S : ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜) :
      L.symm (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) => F) 𝕜 S) = S :=
    L.symm_apply_apply S
  have heq (p : P) (hp : b p ∈ e.baseSet) :=
    congrArg L.symm (curryLeftEquiv_inCoordinates (b p₀) (b p) hp
      ((Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p)).symm (A p)))
  apply h.congr_of_eventuallyEq
  · have hbase : ∀ᶠ p in 𝓝[s] p₀, b p ∈ e.baseSet :=
      hA.1.continuousWithinAt (e.open_baseSet.mem_nhds hx)
    filter_upwards [hbase] with p hp
    simpa only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply,
      hinv, Function.comp_apply] using (heq p hp).symm
  · simpa only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply,
      hinv, Function.comp_apply] using (heq p₀ hx).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffWithinAt.multilinear_bundle_uncurry_left then
    throwError "Refusing to shadow existing declaration ContMDiffWithinAt.multilinear_bundle_uncurry_left"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffWithinAt.multilinear_bundle_uncurry_left ``Submission.ContMDiffWithinAt.multilinear_bundle_uncurry_left

open _root_.ContMDiffAt in
theorem ContMDiffAt.multilinear_bundle_uncurry_left
    {A : ∀ p, V (b p) →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V (b p)}
    (hA : ContMDiffAt J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, A p⟩ : _root_.Bundle.TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) p₀) :
    ContMDiffAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)) n
      (fun p => (⟨b p,
        (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p)).symm (A p)⟩ :
        _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) p₀ :=
  ContMDiffWithinAt.multilinear_bundle_uncurry_left hA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffAt.multilinear_bundle_uncurry_left then
    throwError "Refusing to shadow existing declaration ContMDiffAt.multilinear_bundle_uncurry_left"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffAt.multilinear_bundle_uncurry_left ``Submission.ContMDiffAt.multilinear_bundle_uncurry_left

open _root_.ContMDiffOn in
theorem ContMDiffOn.multilinear_bundle_uncurry_left
    {A : ∀ p, V (b p) →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V (b p)}
    (hA : ContMDiffOn J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, A p⟩ : _root_.Bundle.TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) s) :
    ContMDiffOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)) n
      (fun p => (⟨b p,
        (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p)).symm (A p)⟩ :
        _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) s :=
  fun p hp => (hA p hp).multilinear_bundle_uncurry_left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffOn.multilinear_bundle_uncurry_left then
    throwError "Refusing to shadow existing declaration ContMDiffOn.multilinear_bundle_uncurry_left"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffOn.multilinear_bundle_uncurry_left ``Submission.ContMDiffOn.multilinear_bundle_uncurry_left

open _root_.ContMDiff in
theorem ContMDiff.multilinear_bundle_uncurry_left
    {A : ∀ p, V (b p) →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V (b p)}
    (hA : ContMDiff J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, A p⟩ : _root_.Bundle.TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x)))) :
    ContMDiff J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)) n
      (fun p => (⟨b p,
        (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p)).symm (A p)⟩ :
        _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) :=
  fun p => (hA p).multilinear_bundle_uncurry_left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiff.multilinear_bundle_uncurry_left then
    throwError "Refusing to shadow existing declaration ContMDiff.multilinear_bundle_uncurry_left"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiff.multilinear_bundle_uncurry_left ``Submission.ContMDiff.multilinear_bundle_uncurry_left

open _root_.MDifferentiableWithinAt in
theorem MDifferentiableWithinAt.multilinear_bundle_curry_left
    (hT : MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) s p₀) :
    MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p) (T p)⟩ : _root_.Bundle.TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) s p₀ := by
  have hmap : ContMDiff (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜))
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) 1
      (fun q : _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜) (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V) =>
        (⟨q.1, Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k q.1 q.2⟩ : _root_.Bundle.TotalSpace (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜) (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) :=
    ContMDiff.multilinear_bundle_curry_left contMDiff_id
  exact (hmap.mdifferentiableAt (by norm_num)).comp_mdifferentiableWithinAt p₀ hT

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MDifferentiableWithinAt
  let env ← Lean.getEnv
  if env.contains `MDifferentiableWithinAt.multilinear_bundle_curry_left then
    throwError "Refusing to shadow existing declaration MDifferentiableWithinAt.multilinear_bundle_curry_left"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableWithinAt.multilinear_bundle_curry_left ``Submission.MDifferentiableWithinAt.multilinear_bundle_curry_left

open _root_.MDifferentiableAt in
theorem MDifferentiableAt.multilinear_bundle_curry_left
    (hT : MDifferentiableAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) p₀) :
    MDifferentiableAt J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p) (T p)⟩ : _root_.Bundle.TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) p₀ :=
  MDifferentiableWithinAt.multilinear_bundle_curry_left hT

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MDifferentiableAt
  let env ← Lean.getEnv
  if env.contains `MDifferentiableAt.multilinear_bundle_curry_left then
    throwError "Refusing to shadow existing declaration MDifferentiableAt.multilinear_bundle_curry_left"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableAt.multilinear_bundle_curry_left ``Submission.MDifferentiableAt.multilinear_bundle_curry_left

open _root_.MDifferentiableOn in
theorem MDifferentiableOn.multilinear_bundle_curry_left
    (hT : MDifferentiableOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) s) :
    MDifferentiableOn J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p) (T p)⟩ : _root_.Bundle.TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) s :=
  fun p hp => (hT p hp).multilinear_bundle_curry_left

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MDifferentiableOn
  let env ← Lean.getEnv
  if env.contains `MDifferentiableOn.multilinear_bundle_curry_left then
    throwError "Refusing to shadow existing declaration MDifferentiableOn.multilinear_bundle_curry_left"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableOn.multilinear_bundle_curry_left ``Submission.MDifferentiableOn.multilinear_bundle_curry_left

open _root_.MDifferentiable in
theorem MDifferentiable.multilinear_bundle_curry_left
    (hT : MDifferentiable J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V)))) :
    MDifferentiable J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p) (T p)⟩ : _root_.Bundle.TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) :=
  fun p => (hT p).multilinear_bundle_curry_left

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MDifferentiable
  let env ← Lean.getEnv
  if env.contains `MDifferentiable.multilinear_bundle_curry_left then
    throwError "Refusing to shadow existing declaration MDifferentiable.multilinear_bundle_curry_left"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiable.multilinear_bundle_curry_left ``Submission.MDifferentiable.multilinear_bundle_curry_left

open _root_.MDifferentiableWithinAt in
theorem MDifferentiableWithinAt.multilinear_bundle_uncurry_left
    {A : ∀ p, V (b p) →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V (b p)}
    (hA : MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, A p⟩ : _root_.Bundle.TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) s p₀) :
    MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜))
      (fun p => (⟨b p,
        (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p)).symm (A p)⟩ :
        _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) s p₀ := by
  have hmap : ContMDiff (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)) 1
      (fun q : _root_.Bundle.TotalSpace (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜) (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x) =>
        (⟨q.1, (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k q.1).symm q.2⟩ : _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜) (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) :=
    ContMDiff.multilinear_bundle_uncurry_left contMDiff_id
  exact (hmap.mdifferentiableAt (by norm_num)).comp_mdifferentiableWithinAt p₀ hA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MDifferentiableWithinAt.multilinear_bundle_uncurry_left then
    throwError "Refusing to shadow existing declaration MDifferentiableWithinAt.multilinear_bundle_uncurry_left"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableWithinAt.multilinear_bundle_uncurry_left ``Submission.MDifferentiableWithinAt.multilinear_bundle_uncurry_left

open _root_.MDifferentiableAt in
theorem MDifferentiableAt.multilinear_bundle_uncurry_left
    {A : ∀ p, V (b p) →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V (b p)}
    (hA : MDifferentiableAt J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, A p⟩ : _root_.Bundle.TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) p₀) :
    MDifferentiableAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜))
      (fun p => (⟨b p,
        (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p)).symm (A p)⟩ :
        _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) p₀ :=
  MDifferentiableWithinAt.multilinear_bundle_uncurry_left hA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MDifferentiableAt.multilinear_bundle_uncurry_left then
    throwError "Refusing to shadow existing declaration MDifferentiableAt.multilinear_bundle_uncurry_left"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableAt.multilinear_bundle_uncurry_left ``Submission.MDifferentiableAt.multilinear_bundle_uncurry_left

open _root_.MDifferentiableOn in
theorem MDifferentiableOn.multilinear_bundle_uncurry_left
    {A : ∀ p, V (b p) →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V (b p)}
    (hA : MDifferentiableOn J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, A p⟩ : _root_.Bundle.TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) s) :
    MDifferentiableOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜))
      (fun p => (⟨b p,
        (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p)).symm (A p)⟩ :
        _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) s :=
  fun p hp => (hA p hp).multilinear_bundle_uncurry_left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MDifferentiableOn.multilinear_bundle_uncurry_left then
    throwError "Refusing to shadow existing declaration MDifferentiableOn.multilinear_bundle_uncurry_left"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableOn.multilinear_bundle_uncurry_left ``Submission.MDifferentiableOn.multilinear_bundle_uncurry_left

open _root_.MDifferentiable in
theorem MDifferentiable.multilinear_bundle_uncurry_left
    {A : ∀ p, V (b p) →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V (b p)}
    (hA : MDifferentiable J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, A p⟩ : _root_.Bundle.TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x)))) :
    MDifferentiable J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜))
      (fun p => (⟨b p,
        (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p)).symm (A p)⟩ :
        _root_.Bundle.TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) :=
  fun p => (hA p).multilinear_bundle_uncurry_left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MDifferentiable.multilinear_bundle_uncurry_left then
    throwError "Refusing to shadow existing declaration MDifferentiable.multilinear_bundle_uncurry_left"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiable.multilinear_bundle_uncurry_left ``Submission.MDifferentiable.multilinear_bundle_uncurry_left

theorem contMDiffWithinAt_multilinear_bundle_zero
    {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 0 F V (b p)} :
    ContMDiffWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V))) s p₀ ↔
      ContMDiffWithinAt J I n b s p₀ ∧
        ContMDiffWithinAt J 𝓘(𝕜, 𝕜) n (fun p => T p Fin.elim0) s p₀ := by
  rw [_root_.Bundle.contMDiffWithinAt_totalSpace]
  let L := (continuousMultilinearCurryFin0 𝕜 F 𝕜).toContinuousLinearEquiv
  have hL : ContMDiff 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
      𝓘(𝕜, 𝕜) n L :=
    ContinuousLinearMap.contMDiff (𝕜 := 𝕜)
      (E := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
      (F := 𝕜) L.toContinuousLinearMap
  have hLinv : ContMDiff 𝓘(𝕜, 𝕜)
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) n L.symm :=
    ContinuousLinearMap.contMDiff (𝕜 := 𝕜) (E := 𝕜)
      (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) L.symm.toContinuousLinearMap
  have heq (p : P) :
      L ((_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V) (b p₀) ⟨b p, T p⟩).2) =
        T p Fin.elim0 :=
    Bundle.continuousMultilinearMap.triv_zero_apply_eq (b p₀) (b p) (T p) 0
  constructor
  · rintro ⟨hb, hT⟩
    refine ⟨hb, ?_⟩
    exact (hL.contMDiffAt.comp_contMDiffWithinAt p₀ hT).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun p => (heq p).symm) (heq p₀).symm
  · rintro ⟨hb, hT⟩
    refine ⟨hb, ?_⟩
    have heq' (p : P) := congrArg L.symm (heq p)
    exact (hLinv.contMDiffAt.comp_contMDiffWithinAt p₀ hT).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun p => by simpa only [ContinuousLinearEquiv.symm_apply_apply, Function.comp_apply]
        using (heq' p)) (by simpa only [ContinuousLinearEquiv.symm_apply_apply, Function.comp_apply] using (heq' p₀))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `contMDiffWithinAt_multilinear_bundle_zero then
    throwError "Refusing to shadow existing declaration contMDiffWithinAt_multilinear_bundle_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `contMDiffWithinAt_multilinear_bundle_zero ``Submission.contMDiffWithinAt_multilinear_bundle_zero

theorem contMDiffAt_multilinear_bundle_zero
    {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 0 F V (b p)} :
    ContMDiffAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V))) p₀ ↔
      ContMDiffAt J I n b p₀ ∧
        ContMDiffAt J 𝓘(𝕜, 𝕜) n (fun p => T p Fin.elim0) p₀ := contMDiffWithinAt_multilinear_bundle_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `contMDiffAt_multilinear_bundle_zero then
    throwError "Refusing to shadow existing declaration contMDiffAt_multilinear_bundle_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `contMDiffAt_multilinear_bundle_zero ``Submission.contMDiffAt_multilinear_bundle_zero

theorem contMDiffOn_multilinear_bundle_zero
    {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 0 F V (b p)} :
    ContMDiffOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V))) s ↔
      ContMDiffOn J I n b s ∧
        ContMDiffOn J 𝓘(𝕜, 𝕜) n (fun p => T p Fin.elim0) s := by
  constructor
  · intro h
    exact ⟨fun p hp => (contMDiffWithinAt_multilinear_bundle_zero.mp (h p hp)).1,
      fun p hp => (contMDiffWithinAt_multilinear_bundle_zero.mp (h p hp)).2⟩
  · rintro ⟨hb, hT⟩ p hp
    exact contMDiffWithinAt_multilinear_bundle_zero.mpr ⟨hb p hp, hT p hp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `contMDiffOn_multilinear_bundle_zero then
    throwError "Refusing to shadow existing declaration contMDiffOn_multilinear_bundle_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `contMDiffOn_multilinear_bundle_zero ``Submission.contMDiffOn_multilinear_bundle_zero

theorem contMDiff_multilinear_bundle_zero
    {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 0 F V (b p)} :
    ContMDiff J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V))) ↔
      ContMDiff J I n b ∧
        ContMDiff J 𝓘(𝕜, 𝕜) n (fun p => T p Fin.elim0) := by
  constructor
  · intro h
    exact ⟨fun p => (contMDiffAt_multilinear_bundle_zero.mp (h p)).1,
      fun p => (contMDiffAt_multilinear_bundle_zero.mp (h p)).2⟩
  · rintro ⟨hb, hT⟩ p
    exact contMDiffAt_multilinear_bundle_zero.mpr ⟨hb p, hT p⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `contMDiff_multilinear_bundle_zero then
    throwError "Refusing to shadow existing declaration contMDiff_multilinear_bundle_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `contMDiff_multilinear_bundle_zero ``Submission.contMDiff_multilinear_bundle_zero

theorem mdifferentiableWithinAt_multilinear_bundle_zero
    {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 0 F V (b p)} :
    MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V))) s p₀ ↔
      MDifferentiableWithinAt J I b s p₀ ∧
        MDifferentiableWithinAt J 𝓘(𝕜, 𝕜) (fun p => T p Fin.elim0) s p₀ := by
  rw [mdifferentiableWithinAt_totalSpace]
  let L := (continuousMultilinearCurryFin0 𝕜 F 𝕜).toContinuousLinearEquiv
  have hL : ContMDiff 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
      𝓘(𝕜, 𝕜) 1 L :=
    ContinuousLinearMap.contMDiff (𝕜 := 𝕜)
      (E := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
      (F := 𝕜) L.toContinuousLinearMap
  have hLinv : ContMDiff 𝓘(𝕜, 𝕜)
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) 1 L.symm :=
    ContinuousLinearMap.contMDiff (𝕜 := 𝕜) (E := 𝕜)
      (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) L.symm.toContinuousLinearMap
  have heq (p : P) :
      L ((_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V) (b p₀) ⟨b p, T p⟩).2) =
        T p Fin.elim0 :=
    Bundle.continuousMultilinearMap.triv_zero_apply_eq (b p₀) (b p) (T p) 0
  constructor
  · rintro ⟨hb, hT⟩
    refine ⟨hb, ?_⟩
    exact ((hL.mdifferentiableAt (by norm_num)).comp_mdifferentiableWithinAt p₀ hT).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun p => (heq p).symm) (heq p₀).symm
  · rintro ⟨hb, hT⟩
    refine ⟨hb, ?_⟩
    have heq' (p : P) := congrArg L.symm (heq p)
    exact ((hLinv.mdifferentiableAt (by norm_num)).comp_mdifferentiableWithinAt p₀ hT).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun p => by simpa only [ContinuousLinearEquiv.symm_apply_apply, Function.comp_apply]
        using (heq' p)) (by simpa only [ContinuousLinearEquiv.symm_apply_apply, Function.comp_apply] using (heq' p₀))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `mdifferentiableWithinAt_multilinear_bundle_zero then
    throwError "Refusing to shadow existing declaration mdifferentiableWithinAt_multilinear_bundle_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `mdifferentiableWithinAt_multilinear_bundle_zero ``Submission.mdifferentiableWithinAt_multilinear_bundle_zero

theorem mdifferentiableAt_multilinear_bundle_zero
    {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 0 F V (b p)} :
    MDifferentiableAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V))) p₀ ↔
      MDifferentiableAt J I b p₀ ∧
        MDifferentiableAt J 𝓘(𝕜, 𝕜) (fun p => T p Fin.elim0) p₀ := mdifferentiableWithinAt_multilinear_bundle_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `mdifferentiableAt_multilinear_bundle_zero then
    throwError "Refusing to shadow existing declaration mdifferentiableAt_multilinear_bundle_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `mdifferentiableAt_multilinear_bundle_zero ``Submission.mdifferentiableAt_multilinear_bundle_zero

theorem mdifferentiableOn_multilinear_bundle_zero
    {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 0 F V (b p)} :
    MDifferentiableOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V))) s ↔
      MDifferentiableOn J I b s ∧
        MDifferentiableOn J 𝓘(𝕜, 𝕜) (fun p => T p Fin.elim0) s := by
  constructor
  · intro h
    exact ⟨fun p hp => (mdifferentiableWithinAt_multilinear_bundle_zero.mp (h p hp)).1,
      fun p hp => (mdifferentiableWithinAt_multilinear_bundle_zero.mp (h p hp)).2⟩
  · rintro ⟨hb, hT⟩ p hp
    exact mdifferentiableWithinAt_multilinear_bundle_zero.mpr ⟨hb p hp, hT p hp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `mdifferentiableOn_multilinear_bundle_zero then
    throwError "Refusing to shadow existing declaration mdifferentiableOn_multilinear_bundle_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `mdifferentiableOn_multilinear_bundle_zero ``Submission.mdifferentiableOn_multilinear_bundle_zero

theorem mdifferentiable_multilinear_bundle_zero
    {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 0 F V (b p)} :
    MDifferentiable J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V))) ↔
      MDifferentiable J I b ∧
        MDifferentiable J 𝓘(𝕜, 𝕜) (fun p => T p Fin.elim0) := by
  constructor
  · intro h
    exact ⟨fun p => (mdifferentiableAt_multilinear_bundle_zero.mp (h p)).1,
      fun p => (mdifferentiableAt_multilinear_bundle_zero.mp (h p)).2⟩
  · rintro ⟨hb, hT⟩ p
    exact mdifferentiableAt_multilinear_bundle_zero.mpr ⟨hb p, hT p⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `mdifferentiable_multilinear_bundle_zero then
    throwError "Refusing to shadow existing declaration mdifferentiable_multilinear_bundle_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `mdifferentiable_multilinear_bundle_zero ``Submission.mdifferentiable_multilinear_bundle_zero

open _root_.ContMDiff in
theorem ContMDiff.multilinear_bundle_curry_zero
    {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 0 F V (b p)}
    (hT : ContMDiff J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V)))) :
    ContMDiff J (I.prod 𝓘(𝕜, 𝕜)) n
      (fun p => (⟨b p, Bundle.continuousMultilinearMap.curryFin0Equiv
        (𝕜 := 𝕜) (F := F) (E := V) (b p) (T p)⟩ : _root_.Bundle.TotalSpace 𝕜 (Bundle.Trivial M 𝕜))) := by
  obtain ⟨hb, hs⟩ := contMDiff_multilinear_bundle_zero.mp hT
  intro p
  rw [_root_.Bundle.contMDiffAt_totalSpace]
  refine ⟨hb p, ?_⟩
  simpa only [Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.trivialization_apply, Bundle.continuousMultilinearMap.curryFin0Equiv_apply]
    using hs p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiff.multilinear_bundle_curry_zero then
    throwError "Refusing to shadow existing declaration ContMDiff.multilinear_bundle_curry_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiff.multilinear_bundle_curry_zero ``Submission.ContMDiff.multilinear_bundle_curry_zero

open _root_.ContMDiff in
theorem ContMDiff.multilinear_bundle_uncurry_zero
    {A : P → 𝕜}
    (hA : ContMDiff J (I.prod 𝓘(𝕜, 𝕜)) n
      (fun p => (⟨b p, A p⟩ : _root_.Bundle.TotalSpace 𝕜 (Bundle.Trivial M 𝕜)))) :
    ContMDiff J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)) n
      (fun p => (⟨b p, (Bundle.continuousMultilinearMap.curryFin0Equiv
        (𝕜 := 𝕜) (F := F) (E := V) (b p)).symm (A p)⟩ : _root_.Bundle.TotalSpace
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
          (Bundle.continuousMultilinearMap 𝕜 0 F V))) := by
  rw [contMDiff_multilinear_bundle_zero]
  constructor
  · intro p
    exact (contMDiffAt_totalSpace.mp (hA p)).1
  · intro p
    have h := (contMDiffAt_totalSpace.mp (hA p)).2
    simpa only [Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.trivialization_apply,
      Bundle.continuousMultilinearMap.curryFin0Equiv_symm_apply] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiff.multilinear_bundle_uncurry_zero then
    throwError "Refusing to shadow existing declaration ContMDiff.multilinear_bundle_uncurry_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiff.multilinear_bundle_uncurry_zero ``Submission.ContMDiff.multilinear_bundle_uncurry_zero
