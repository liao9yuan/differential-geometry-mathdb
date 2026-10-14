import Submission.DifferentialGeometry.Topology.Manifold.InjectiveRegularity
import Submission.DifferentialGeometry.Bundle.Hom.Regularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Bundle _root_.Filter _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul 𝕜 (W x)]
  [FiberBundle G W] [VectorBundle 𝕜 G W]
  {n : ℕ∞ω} {A : ∀ x, V x →L[𝕜] W x} {s : ∀ x, V x} {x : M}

section Map

variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] {J : ModelWithCorners 𝕜 EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {b : P → M} {A : ∀ p, V (b p) →L[𝕜] W (b p)}
  {s : ∀ p, V (b p)} {p : P}

open _root_.ContMDiffWithinAt in
theorem ContMDiffWithinAt.of_clm_bundle_apply_of_injective
    {u : Set P}
    (hA : ContMDiffWithinAt J (I.prod 𝓘(𝕜, F →L[𝕜] G)) n
      (fun q => TotalSpace.mk' (F →L[𝕜] G) (E := fun x => V x →L[𝕜] W x) (b q) (A q)) u p)
    (hAs : ContMDiffWithinAt J (I.prod 𝓘(𝕜, G)) n
      (fun q => TotalSpace.mk' G (E := W) (b q) (A q (s q))) u p)
    (hinj : Function.Injective (A p)) :
    ContMDiffWithinAt J (I.prod 𝓘(𝕜, F)) n (fun q => TotalSpace.mk' F (E := V) (b q) (s q)) u p := by
  let e := _root_.FiberBundle.trivializationAt F V (b p)
  let f := _root_.FiberBundle.trivializationAt G W (b p)
  let B := fun q => ContinuousLinearMap.inCoordinates F V G W (b p) (b q) (b p) (b q) (A q)
  let vcoord := fun q => (e ⟨b q, s q⟩).2
  have hAB := (contMDiffWithinAt_hom_bundle _).mp hA
  have hB : ContMDiffWithinAt J 𝓘(𝕜, F →L[𝕜] G) n B u p := hAB.2
  have hBu : ContMDiffWithinAt J 𝓘(𝕜, G) n (fun q => B q (vcoord q)) u p := by
    have h := (contMDiffWithinAt_totalSpace.mp hAs).2
    apply h.congr_of_eventuallyEq
    · filter_upwards [hAB.1.continuousWithinAt (e.open_baseSet.mem_nhds
          (_root_.FiberBundle.mem_baseSet_trivializationAt F V (b p))),
        hAB.1.continuousWithinAt (f.open_baseSet.mem_nhds
          (_root_.FiberBundle.mem_baseSet_trivializationAt G W (b p)))] with q he hf
      dsimp only [B, vcoord, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
      rw [← Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 e he]
      rw [e.symmL_continuousLinearMapAt he]
      exact Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 f hf _
    · dsimp only [B, vcoord, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
      rw [← Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 e
        (_root_.FiberBundle.mem_baseSet_trivializationAt F V (b p))]
      rw [e.symmL_continuousLinearMapAt (_root_.FiberBundle.mem_baseSet_trivializationAt F V (b p))]
      exact Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 f
        (_root_.FiberBundle.mem_baseSet_trivializationAt G W (b p)) _
  have hBi : Function.Injective (B p) := by
    dsimp only [B]
    rw [ContinuousLinearMap.inCoordinates_eq
      (_root_.FiberBundle.mem_baseSet_trivializationAt F V (b p)) (_root_.FiberBundle.mem_baseSet_trivializationAt G W (b p))]
    exact (f.continuousLinearEquivAt 𝕜 (b p) (_root_.FiberBundle.mem_baseSet_trivializationAt G W (b p))).injective.comp
      (hinj.comp (e.continuousLinearEquivAt 𝕜 (b p)
        (_root_.FiberBundle.mem_baseSet_trivializationAt F V (b p))).symm.injective)
  rw [_root_.Bundle.contMDiffWithinAt_totalSpace]
  exact ⟨hAB.1, hB.of_clm_apply_of_injective hBu hBi⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffWithinAt.of_clm_bundle_apply_of_injective then
    throwError "Refusing to shadow existing declaration ContMDiffWithinAt.of_clm_bundle_apply_of_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffWithinAt.of_clm_bundle_apply_of_injective ``Submission.ContMDiffWithinAt.of_clm_bundle_apply_of_injective

open _root_.ContMDiffOn in
theorem ContMDiffOn.of_clm_bundle_apply_of_injective
    {u : Set P}
    (hA : ContMDiffOn J (I.prod 𝓘(𝕜, F →L[𝕜] G)) n
      (fun q => TotalSpace.mk' (F →L[𝕜] G)
        (E := fun x => V x →L[𝕜] W x) (b q) (A q)) u)
    (hAs : ContMDiffOn J (I.prod 𝓘(𝕜, G)) n
      (fun q => TotalSpace.mk' G (E := W) (b q) (A q (s q))) u)
    (hinj : ∀ q ∈ u, Function.Injective (A q)) :
    ContMDiffOn J (I.prod 𝓘(𝕜, F)) n (fun q => TotalSpace.mk' F (E := V) (b q) (s q)) u :=
  fun q hq => (hA q hq).of_clm_bundle_apply_of_injective (hAs q hq) (hinj q hq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffOn.of_clm_bundle_apply_of_injective then
    throwError "Refusing to shadow existing declaration ContMDiffOn.of_clm_bundle_apply_of_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffOn.of_clm_bundle_apply_of_injective ``Submission.ContMDiffOn.of_clm_bundle_apply_of_injective

end Map

open _root_.ContMDiffAt in
theorem ContMDiffAt.of_clm_bundle_apply_of_injective
    (hA : ContMDiffAt I (I.prod 𝓘(𝕜, F →L[𝕜] G)) n
      (fun y => TotalSpace.mk' (F →L[𝕜] G) y (A y)) x)
    (hAs : ContMDiffAt I (I.prod 𝓘(𝕜, G)) n
      (fun y => TotalSpace.mk' G y (A y (s y))) x)
    (hinj : Function.Injective (A x)) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun y => TotalSpace.mk' F y (s y)) x := by
  exact contMDiffWithinAt_univ.mp
    (hA.contMDiffWithinAt.of_clm_bundle_apply_of_injective
      hAs.contMDiffWithinAt hinj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiffAt.of_clm_bundle_apply_of_injective then
    throwError "Refusing to shadow existing declaration ContMDiffAt.of_clm_bundle_apply_of_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffAt.of_clm_bundle_apply_of_injective ``Submission.ContMDiffAt.of_clm_bundle_apply_of_injective

open _root_.ContMDiff in
theorem ContMDiff.of_clm_bundle_apply_of_injective
    (hA : ContMDiff I (I.prod 𝓘(𝕜, F →L[𝕜] G)) n
      (fun y => TotalSpace.mk' (F →L[𝕜] G) y (A y)))
    (hAs : ContMDiff I (I.prod 𝓘(𝕜, G)) n
      (fun y => TotalSpace.mk' G y (A y (s y))))
    (hinj : ∀ y, Function.Injective (A y)) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun y => TotalSpace.mk' F y (s y)) :=
  fun y => (hA y).of_clm_bundle_apply_of_injective (hAs y) (hinj y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContMDiff.of_clm_bundle_apply_of_injective then
    throwError "Refusing to shadow existing declaration ContMDiff.of_clm_bundle_apply_of_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiff.of_clm_bundle_apply_of_injective ``Submission.ContMDiff.of_clm_bundle_apply_of_injective
