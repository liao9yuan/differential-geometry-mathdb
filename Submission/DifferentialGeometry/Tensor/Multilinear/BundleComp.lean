import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Fiber
import Mathlib.Geometry.Manifold.VectorBundle.Hom

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace Bundle.continuousMultilinearMap
open _root_.Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {V₁ : B → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, NormedSpace 𝕜 (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  {V₂ : B → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, NormedSpace 𝕜 (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  {k : ℕ}

def compContinuousLinearMapL (x : B) (A : Fin k → V₁ x →L[𝕜] V₂ x) :
    Bundle.continuousMultilinearMap 𝕜 k F₂ V₂ x →L[𝕜]
      Bundle.continuousMultilinearMap 𝕜 k F₁ V₁ x :=
  (fiberContinuousLinearEquiv (F := F₁) k x).symm.toContinuousLinearMap.comp
    ((ContinuousMultilinearMap.compContinuousLinearMapL A).comp
      (fiberContinuousLinearEquiv (F := F₂) k x).toContinuousLinearMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.compContinuousLinearMapL then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.compContinuousLinearMapL"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.compContinuousLinearMapL ``Submission.Bundle.continuousMultilinearMap.compContinuousLinearMapL

@[simp] theorem compContinuousLinearMapL_apply (x : B)
    (A : Fin k → V₁ x →L[𝕜] V₂ x)
    (T : Bundle.continuousMultilinearMap 𝕜 k F₂ V₂ x) (v : Fin k → V₁ x) :
    compContinuousLinearMapL (F₁ := F₁) (F₂ := F₂) x A T v =
      T (fun i => A i (v i)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.compContinuousLinearMapL_apply then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.compContinuousLinearMapL_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.compContinuousLinearMapL_apply ``Submission.Bundle.continuousMultilinearMap.compContinuousLinearMapL_apply

def congrLeft (x : B) (φ : Fin k → V₁ x ≃L[𝕜] V₂ x) :
    Bundle.continuousMultilinearMap 𝕜 k F₂ V₂ x ≃L[𝕜]
      Bundle.continuousMultilinearMap 𝕜 k F₁ V₁ x :=
  (fiberContinuousLinearEquiv (F := F₂) k x).trans
    ((ContinuousLinearEquiv.continuousMultilinearMapCongrLeft 𝕜 φ).trans
      (fiberContinuousLinearEquiv (F := F₁) k x).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.congrLeft then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.congrLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.congrLeft ``Submission.Bundle.continuousMultilinearMap.congrLeft

@[simp] theorem congrLeft_apply (x : B) (φ : Fin k → V₁ x ≃L[𝕜] V₂ x)
    (T : Bundle.continuousMultilinearMap 𝕜 k F₂ V₂ x) (v : Fin k → V₁ x) :
    congrLeft (F₁ := F₁) (F₂ := F₂) x φ T v = T (fun i => φ i (v i)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.congrLeft_apply then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.congrLeft_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.congrLeft_apply ``Submission.Bundle.continuousMultilinearMap.congrLeft_apply

@[simp] theorem congrLeft_symm (x : B) (φ : Fin k → V₁ x ≃L[𝕜] V₂ x) :
    (congrLeft (F₁ := F₁) (F₂ := F₂) x φ).symm =
      congrLeft (F₁ := F₂) (F₂ := F₁) x (fun i => (φ i).symm) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.congrLeft_symm then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.congrLeft_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.congrLeft_symm ``Submission.Bundle.continuousMultilinearMap.congrLeft_symm

end Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
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
  {n : WithTop ℕ∞} {k : ℕ} {b : P → M}
  {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 k F₂ V₂ (b p)}
  {A : Fin k → ∀ p, V₁ (b p) →L[𝕜] V₂ (b p)} {s : Set P} {p₀ : P}

private theorem multilinear_comp_inCoordinates
    (x₀ x : M) (hx : x ∈ (_root_.FiberBundle.trivializationAt F₂ V₂ x₀).baseSet)
    (T : Bundle.continuousMultilinearMap 𝕜 k F₂ V₂ x)
    (A : Fin k → V₁ x →L[𝕜] V₂ x) :
    (_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 k F₁ V₁) x₀
        ⟨x, T.compContinuousLinearMap A⟩).2 =
      ((_root_.FiberBundle.trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₂ V₂) x₀ ⟨x, T⟩).2).compContinuousLinearMap
        (fun i => ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ x₀ x x₀ x (A i)) := by
  ext v
  change T (fun i => A i ((_root_.FiberBundle.trivializationAt F₁ V₁ x₀).symmL 𝕜 x (v i))) =
    T (fun i => (_root_.FiberBundle.trivializationAt F₂ V₂ x₀).symmL 𝕜 x
      (ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ x₀ x x₀ x (A i) (v i)))
  congr 1
  funext i
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.symmL_continuousLinearMapAt _ hx]

run_cmd do
  let target := ``Submission.multilinear_comp_inCoordinates
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `multilinear_comp_inCoordinates target :: scope.openDecls } }

open _root_.ContMDiffWithinAt in
theorem ContMDiffWithinAt.multilinear_bundle_comp
    (hT : ContMDiffWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₂ V₂))) s p₀)
    (hA : ∀ i, ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, A i p⟩ : _root_.Bundle.TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s p₀) :
    ContMDiffWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)) n
      (fun p => (⟨b p, (T p).compContinuousLinearMap (fun i => A i p)⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₁ V₁))) s p₀ := by
  rw [_root_.Bundle.contMDiffWithinAt_totalSpace] at hT ⊢
  refine ⟨hT.1, ?_⟩
  have hAc := fun i => ((contMDiffWithinAt_hom_bundle _).mp (hA i)).2
  let L := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : Fin k => F₁) (fun _ : Fin k => F₂) 𝕜
  have h := ((L.contDiff (n := n)).contMDiff.contMDiffAt.comp_contMDiffWithinAt p₀
    (contMDiffWithinAt_pi_space.mpr hAc)).clm_apply hT.2
  let e := _root_.FiberBundle.trivializationAt F₂ V₂ (b p₀)
  have hx : b p₀ ∈ e.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt F₂ V₂ (b p₀)
  apply h.congr_of_eventuallyEq
  · filter_upwards [hT.1.continuousWithinAt (e.open_baseSet.mem_nhds hx)] with p hp
    exact multilinear_comp_inCoordinates (b p₀) (b p) hp (T p) (fun i => A i p)
  · exact multilinear_comp_inCoordinates (b p₀) (b p₀) hx (T p₀) (fun i => A i p₀)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffWithinAt
  let env ← Lean.getEnv
  if env.contains `ContMDiffWithinAt.multilinear_bundle_comp then
    throwError "Refusing to shadow existing declaration ContMDiffWithinAt.multilinear_bundle_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffWithinAt.multilinear_bundle_comp ``Submission.ContMDiffWithinAt.multilinear_bundle_comp

open _root_.ContMDiffAt in
theorem ContMDiffAt.multilinear_bundle_comp
    (hT : ContMDiffAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₂ V₂))) p₀)
    (hA : ∀ i, ContMDiffAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, A i p⟩ : _root_.Bundle.TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) p₀) :
    ContMDiffAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)) n
      (fun p => (⟨b p, (T p).compContinuousLinearMap (fun i => A i p)⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₁ V₁))) p₀ :=
  ContMDiffWithinAt.multilinear_bundle_comp hT hA

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffAt
  let env ← Lean.getEnv
  if env.contains `ContMDiffAt.multilinear_bundle_comp then
    throwError "Refusing to shadow existing declaration ContMDiffAt.multilinear_bundle_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffAt.multilinear_bundle_comp ``Submission.ContMDiffAt.multilinear_bundle_comp

open _root_.ContMDiffOn in
theorem ContMDiffOn.multilinear_bundle_comp
    (hT : ContMDiffOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₂ V₂))) s)
    (hA : ∀ i, ContMDiffOn J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, A i p⟩ : _root_.Bundle.TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s) :
    ContMDiffOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)) n
      (fun p => (⟨b p, (T p).compContinuousLinearMap (fun i => A i p)⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₁ V₁))) s :=
  fun p hp => (hT p hp).multilinear_bundle_comp (fun i => hA i p hp)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffOn
  let env ← Lean.getEnv
  if env.contains `ContMDiffOn.multilinear_bundle_comp then
    throwError "Refusing to shadow existing declaration ContMDiffOn.multilinear_bundle_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffOn.multilinear_bundle_comp ``Submission.ContMDiffOn.multilinear_bundle_comp

open _root_.ContMDiff in
theorem ContMDiff.multilinear_bundle_comp
    (hT : ContMDiff J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₂ V₂))))
    (hA : ∀ i, ContMDiff J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, A i p⟩ : _root_.Bundle.TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x)))) :
    ContMDiff J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)) n
      (fun p => (⟨b p, (T p).compContinuousLinearMap (fun i => A i p)⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₁ V₁))) :=
  fun p => (hT p).multilinear_bundle_comp (fun i => hA i p)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiff
  let env ← Lean.getEnv
  if env.contains `ContMDiff.multilinear_bundle_comp then
    throwError "Refusing to shadow existing declaration ContMDiff.multilinear_bundle_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiff.multilinear_bundle_comp ``Submission.ContMDiff.multilinear_bundle_comp

open _root_.MDifferentiableWithinAt in
theorem MDifferentiableWithinAt.multilinear_bundle_comp
    (hT : MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜))
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₂ V₂))) s p₀)
    (hA : ∀ i, MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun p => (⟨b p, A i p⟩ : _root_.Bundle.TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s p₀) :
    MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜))
      (fun p => (⟨b p, (T p).compContinuousLinearMap (fun i => A i p)⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₁ V₁))) s p₀ := by
  rw [mdifferentiableWithinAt_totalSpace] at hT ⊢
  refine ⟨hT.1, ?_⟩
  have hAc := fun i => ((mdifferentiableWithinAt_hom_bundle _).mp (hA i)).2
  let L := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : Fin k => F₁) (fun _ : Fin k => F₂) 𝕜
  have hpi : MDifferentiableWithinAt J 𝓘(𝕜, Fin k → F₁ →L[𝕜] F₂)
      (fun p i => ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂
        (b p₀) (b p) (b p₀) (b p) (A i p)) s p₀ := by
    simpa only [mdifferentiableWithinAt_iff, continuousWithinAt_pi,
      differentiableWithinAt_pi, forall_and, extChartAt_model_space_eq_id,
      Function.comp_def, PartialEquiv.refl_coe, id] using hAc
  have hL : MDifferentiable 𝓘(𝕜, Fin k → F₁ →L[𝕜] F₂)
      𝓘(𝕜, (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜) →L[𝕜]
        ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜) L :=
    mdifferentiable_iff_differentiable.mpr
      ((show ContDiff 𝕜 1 (fun a : Fin k → F₁ →L[𝕜] F₂ => L a) from
        ContinuousMultilinearMap.contDiff (𝕜 := 𝕜) (E := fun _ : Fin k => F₁ →L[𝕜] F₂)
          (F := (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜) →L[𝕜]
            ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜) L).differentiable
        (by norm_num))
  have h := ((hL _).comp_mdifferentiableWithinAt p₀ hpi).clm_apply hT.2
  let e := _root_.FiberBundle.trivializationAt F₂ V₂ (b p₀)
  have hx : b p₀ ∈ e.baseSet := _root_.FiberBundle.mem_baseSet_trivializationAt F₂ V₂ (b p₀)
  apply h.congr_of_eventuallyEq
  · filter_upwards [hT.1.continuousWithinAt (e.open_baseSet.mem_nhds hx)] with p hp
    exact multilinear_comp_inCoordinates (b p₀) (b p) hp (T p) (fun i => A i p)
  · exact multilinear_comp_inCoordinates (b p₀) (b p₀) hx (T p₀) (fun i => A i p₀)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MDifferentiableWithinAt
  let env ← Lean.getEnv
  if env.contains `MDifferentiableWithinAt.multilinear_bundle_comp then
    throwError "Refusing to shadow existing declaration MDifferentiableWithinAt.multilinear_bundle_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableWithinAt.multilinear_bundle_comp ``Submission.MDifferentiableWithinAt.multilinear_bundle_comp

open _root_.MDifferentiableAt in
theorem MDifferentiableAt.multilinear_bundle_comp
    (hT : MDifferentiableAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜))
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₂ V₂))) p₀)
    (hA : ∀ i, MDifferentiableAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun p => (⟨b p, A i p⟩ : _root_.Bundle.TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) p₀) :
    MDifferentiableAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜))
      (fun p => (⟨b p, (T p).compContinuousLinearMap (fun i => A i p)⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₁ V₁))) p₀ :=
  MDifferentiableWithinAt.multilinear_bundle_comp hT hA

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MDifferentiableAt
  let env ← Lean.getEnv
  if env.contains `MDifferentiableAt.multilinear_bundle_comp then
    throwError "Refusing to shadow existing declaration MDifferentiableAt.multilinear_bundle_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableAt.multilinear_bundle_comp ``Submission.MDifferentiableAt.multilinear_bundle_comp

open _root_.MDifferentiableOn in
theorem MDifferentiableOn.multilinear_bundle_comp
    (hT : MDifferentiableOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜))
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₂ V₂))) s)
    (hA : ∀ i, MDifferentiableOn J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun p => (⟨b p, A i p⟩ : _root_.Bundle.TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s) :
    MDifferentiableOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜))
      (fun p => (⟨b p, (T p).compContinuousLinearMap (fun i => A i p)⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₁ V₁))) s :=
  fun p hp => (hT p hp).multilinear_bundle_comp (fun i => hA i p hp)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MDifferentiableOn
  let env ← Lean.getEnv
  if env.contains `MDifferentiableOn.multilinear_bundle_comp then
    throwError "Refusing to shadow existing declaration MDifferentiableOn.multilinear_bundle_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiableOn.multilinear_bundle_comp ``Submission.MDifferentiableOn.multilinear_bundle_comp

open _root_.MDifferentiable in
theorem MDifferentiable.multilinear_bundle_comp
    (hT : MDifferentiable J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜))
      (fun p => (⟨b p, T p⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₂ V₂))))
    (hA : ∀ i, MDifferentiable J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun p => (⟨b p, A i p⟩ : _root_.Bundle.TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x)))) :
    MDifferentiable J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜))
      (fun p => (⟨b p, (T p).compContinuousLinearMap (fun i => A i p)⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₁ V₁))) :=
  fun p => (hT p).multilinear_bundle_comp (fun i => hA i p)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MDifferentiable
  let env ← Lean.getEnv
  if env.contains `MDifferentiable.multilinear_bundle_comp then
    throwError "Refusing to shadow existing declaration MDifferentiable.multilinear_bundle_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `MDifferentiable.multilinear_bundle_comp ``Submission.MDifferentiable.multilinear_bundle_comp
