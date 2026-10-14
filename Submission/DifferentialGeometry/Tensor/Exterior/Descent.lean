import Submission.DifferentialGeometry.Tensor.Exterior.Pullback
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners Real F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {k : Nat} {f : M → N} {x : M}
  {α : ∀ y : N, TangentSpace J y [⋀^Fin k]→L[Real] Real}

private theorem alternating_pullback_inCoordinates (x₀ y : M)
    (hy : f y ∈ (_root_.FiberBundle.trivializationAt F (TangentSpace J) (f x₀)).baseSet) :
    (_root_.FiberBundle.trivializationAt (E [⋀^Fin k]→L[Real] Real)
      (Bundle.continuousAlternatingMap Real (Fin k) E (TangentSpace I) Real
        (Bundle.Trivial M Real)) x₀
      ⟨y, (α (f y)).compContinuousLinearMap (mfderiv I J f y)⟩).2 =
      ((_root_.FiberBundle.trivializationAt (F [⋀^Fin k]→L[Real] Real)
        (Bundle.continuousAlternatingMap Real (Fin k) F (TangentSpace J) Real
          (Bundle.Trivial N Real)) (f x₀) ⟨f y, α (f y)⟩).2).compContinuousLinearMap
        (inTangentCoordinates I J id f (mfderiv I J f) x₀ y) := by
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply,
    FiberBundle.trivializationAt_continuousAlternatingMap_apply]
  ext v
  simp only [ContinuousAlternatingMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, ContinuousLinearMap.coe_id', Function.comp_apply,
    id_eq, inTangentCoordinates, ContinuousLinearMap.inCoordinates]
  congr 1
  funext i
  exact ((_root_.FiberBundle.trivializationAt F (TangentSpace J) (f x₀)).symmL_continuousLinearMapAt hy _).symm

run_cmd do
  let target := ``Submission.alternating_pullback_inCoordinates
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `alternating_pullback_inCoordinates target :: scope.openDecls } }

open _root_.ContMDiffAt in
theorem ContMDiffAt.alternating_pullback
    (hf : ContMDiffAt I J ∞ f x)
    (hα : ContMDiffAt J (J.prod 𝓘(Real, F [⋀^Fin k]→L[Real] Real)) ∞
      (fun y => (⟨y, α y⟩ : _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[Real] Real)
        (Bundle.continuousAlternatingMap Real (Fin k) F (TangentSpace J) Real
          (Bundle.Trivial N Real)))) (f x)) :
    ContMDiffAt I (I.prod 𝓘(Real, E [⋀^Fin k]→L[Real] Real)) ∞
      (fun y => (⟨y, (α (f y)).compContinuousLinearMap (mfderiv I J f y)⟩ :
        _root_.Bundle.TotalSpace (E [⋀^Fin k]→L[Real] Real)
          (Bundle.continuousAlternatingMap Real (Fin k) E (TangentSpace I) Real
            (Bundle.Trivial M Real)))) x := by
  rw [_root_.Bundle.contMDiffAt_section] at hα ⊢
  have hAc := hf.mfderiv_const (m := ∞) (by simp)
  have hαc := hα.comp x hf
  have hcomp := (ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_of_space_real
    (F₁ := E) (F₁' := F) (F₂ := Real) (ι := Fin k)).of_le (show (∞ : ℕ∞ω) ≤ ⊤ from le_top)
  have hcompAt := hcomp.contMDiffAt.comp x hAc
  have h := hcompAt.clm_apply hαc
  apply h.congr_of_eventuallyEq
  have hx := _root_.FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (f x)
  filter_upwards [hf.continuousAt
    ((_root_.FiberBundle.trivializationAt F (TangentSpace J) (f x)).open_baseSet.mem_nhds hx)] with y hy
  exact alternating_pullback_inCoordinates x y hy

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffAt
  let env ← Lean.getEnv
  if env.contains `ContMDiffAt.alternating_pullback then
    throwError "Refusing to shadow existing declaration ContMDiffAt.alternating_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffAt.alternating_pullback ``Submission.ContMDiffAt.alternating_pullback

namespace DifferentialGeometry.DifferentialForm

theorem pullback_ne_zero
    (α : DifferentialForm J N k) (f : M → N) (hf : ContMDiff I J ∞ f) (x : M)
    (hα : α (f x) ≠ 0) (hdf : Function.Surjective (mfderiv I J f x)) :
    pullback f hf α x ≠ 0 := by
  intro h
  apply hα
  ext v
  choose w hw using fun i => hdf (v i)
  have hv := congrArg (fun β : TangentSpace I x [⋀^Fin k]→L[Real] Real => β w) h
  simpa [pullback_apply, Function.comp_def, hw] using hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.pullback_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.pullback_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.pullback_ne_zero ``Submission.DifferentialGeometry.DifferentialForm.pullback_ne_zero

end DifferentialGeometry.DifferentialForm


open _root_.IsLocalDiffeomorph in
theorem IsLocalDiffeomorph.contMDiff_alternating_of_pullback
    (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (hα : ContMDiff I (I.prod 𝓘(Real, E [⋀^Fin k]→L[Real] Real)) ∞
      (fun y => (⟨y, (α (f y)).compContinuousLinearMap (mfderiv I J f y)⟩ :
        _root_.Bundle.TotalSpace (E [⋀^Fin k]→L[Real] Real)
          (Bundle.continuousAlternatingMap Real (Fin k) E (TangentSpace I) Real
            (Bundle.Trivial M Real))))) :
    ContMDiff J (J.prod 𝓘(Real, F [⋀^Fin k]→L[Real] Real)) ∞
      (fun y => (⟨y, α y⟩ : _root_.Bundle.TotalSpace (F [⋀^Fin k]→L[Real] Real)
        (Bundle.continuousAlternatingMap Real (Fin k) F (TangentSpace J) Real
          (Bundle.Trivial N Real)))) := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  let s := (hf x).localInverse
  have hs : ContMDiffAt J I ∞ s (f x) := (hf x).localInverse_contMDiffAt
  have h := hs.alternating_pullback (hα (s (f x)))
  apply h.congr_of_eventuallyEq
  have heq : f ∘ s =ᶠ[𝓝 (f x)] id := (hf x).localInverse_eventuallyEq_right
  have hdiff : ∀ᶠ z in 𝓝 (f x), MDifferentiableAt J I s z := by
    filter_upwards [(hf x).localInverse.open_source.mem_nhds
      (hf x).localInverse_mem_source] with z hz
    exact ((hf x).localInverse_contMDiffOn.contMDiffAt
      ((hf x).localInverse.open_source.mem_nhds hz)).mdifferentiableAt (by simp)
  filter_upwards [heq, heq.eventuallyEq_nhds, hdiff] with z hz hloc hsz
  congr 1
  ext v
  have hd : (mfderiv I J f (s z)).comp (mfderiv J I s z) = ContinuousLinearMap.id Real F := by
    rw [← mfderiv_comp z ((hf (s z)).mdifferentiableAt (by simp)) hsz,
      hloc.mfderiv_eq, mfderiv_id]
    rfl
  change α z v = α (f (s z)) (fun i => mfderiv I J f (s z) (mfderiv J I s z (v i)))
  have hv : (fun i => mfderiv I J f (s z) (mfderiv J I s z (v i))) = v := by
    funext i
    exact congrArg (fun L : F →L[Real] F => L (v i)) hd
  rw [hv]
  change f (s z) = z at hz
  have hαz := congrArg (fun z : N => (show F [⋀^Fin k]→L[Real] Real from α z)) hz
  exact congrArg (fun L : F [⋀^Fin k]→L[Real] Real => L v) hαz.symm

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.IsLocalDiffeomorph
  let env ← Lean.getEnv
  if env.contains `IsLocalDiffeomorph.contMDiff_alternating_of_pullback then
    throwError "Refusing to shadow existing declaration IsLocalDiffeomorph.contMDiff_alternating_of_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `IsLocalDiffeomorph.contMDiff_alternating_of_pullback ``Submission.IsLocalDiffeomorph.contMDiff_alternating_of_pullback

attribute [local instance] DifferentialGeometry.normedAddCommGroupTangentSpace
  DifferentialGeometry.normedSpaceTangentSpace

namespace DifferentialGeometry.DifferentialForm

private def localPush
    (β : ∀ x : M, TangentSpace I x [⋀^Fin k]→L[Real] Real)
    (hf : IsLocalDiffeomorph I J ∞ f) (x : M) :
    TangentSpace J (f x) [⋀^Fin k]→L[Real] Real :=
  (β x).compContinuousLinearMap
    (hf.mfderivToContinuousLinearEquiv (by simp) x).symm.toContinuousLinearMap

run_cmd do
  let target := ``Submission.DifferentialGeometry.DifferentialForm.localPush
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.DifferentialForm.localPush target :: scope.openDecls } }

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
private theorem localPush_pullback
    (β : ∀ x : M, TangentSpace I x [⋀^Fin k]→L[Real] Real)
    (hf : IsLocalDiffeomorph I J ∞ f) (x : M) :
    (localPush β hf x).compContinuousLinearMap (mfderiv I J f x) = β x := by
  ext v
  change β x (fun i => (hf.mfderivToContinuousLinearEquiv (by simp) x).symm
    (hf.mfderivToContinuousLinearEquiv (by simp) x (v i))) = β x v
  simp only [ContinuousLinearEquiv.symm_apply_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.DifferentialForm.localPush_pullback
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.DifferentialForm.localPush_pullback target :: scope.openDecls } }

set_option backward.isDefEq.respectTransparency false in
private def descendedForm
    (β : DifferentialForm I M k)
    (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f) :
    ∀ y : N, TangentSpace J y [⋀^Fin k]→L[Real] Real := fun y =>
  (hsurj y).choose_spec ▸ localPush β hf (hsurj y).choose

run_cmd do
  let target := ``Submission.DifferentialGeometry.DifferentialForm.descendedForm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.DifferentialForm.descendedForm target :: scope.openDecls } }

set_option backward.isDefEq.respectTransparency false in
omit [IsManifold J ∞ N] in
private theorem descendedForm_eq
    (β : DifferentialForm I M k)
    (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (hβ : ∀ x y : M, ∀ h : f x = f y,
      h ▸ (β x).compContinuousLinearMap (hf.mfderivToContinuousLinearEquiv (by simp) x).symm.toContinuousLinearMap =
        (β y).compContinuousLinearMap (hf.mfderivToContinuousLinearEquiv (by simp) y).symm.toContinuousLinearMap)
    (x : M) : descendedForm β hf hsurj (f x) = localPush β hf x :=
  hβ _ _ (hsurj (f x)).choose_spec

run_cmd do
  let target := ``Submission.DifferentialGeometry.DifferentialForm.descendedForm_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.DifferentialForm.descendedForm_eq target :: scope.openDecls } }

set_option backward.isDefEq.respectTransparency false in
omit [IsManifold J ∞ N] in
private theorem descendedForm_pullback
    (β : DifferentialForm I M k)
    (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (hβ : ∀ x y : M, ∀ h : f x = f y,
      h ▸ (β x).compContinuousLinearMap (hf.mfderivToContinuousLinearEquiv (by simp) x).symm.toContinuousLinearMap =
        (β y).compContinuousLinearMap (hf.mfderivToContinuousLinearEquiv (by simp) y).symm.toContinuousLinearMap)
    (x : M) :
    (descendedForm β hf hsurj (f x)).compContinuousLinearMap (mfderiv I J f x) = β x := by
  rw [descendedForm_eq β hf hsurj hβ]
  exact localPush_pullback β hf x

run_cmd do
  let target := ``Submission.DifferentialGeometry.DifferentialForm.descendedForm_pullback
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.DifferentialForm.descendedForm_pullback target :: scope.openDecls } }

set_option backward.isDefEq.respectTransparency false in
def descend
    (β : DifferentialForm I M k)
    (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (hβ : ∀ x y : M, ∀ h : f x = f y,
      h ▸ (β x).compContinuousLinearMap (hf.mfderivToContinuousLinearEquiv (by simp) x).symm.toContinuousLinearMap =
        (β y).compContinuousLinearMap (hf.mfderivToContinuousLinearEquiv (by simp) y).symm.toContinuousLinearMap) :
    DifferentialForm J N k := by
  refine ⟨descendedForm β hf hsurj, hf.contMDiff_alternating_of_pullback hsurj ?_⟩
  have heq : (fun x => (⟨x, (descendedForm β hf hsurj (f x)).compContinuousLinearMap
      (mfderiv I J f x)⟩ : _root_.Bundle.TotalSpace (E [⋀^Fin k]→L[Real] Real)
        (Bundle.continuousAlternatingMap Real (Fin k) E (TangentSpace I) Real
          (Bundle.Trivial M Real)))) = fun x => ⟨x, β x⟩ := by
    funext x
    rw [descendedForm_pullback β hf hsurj hβ]
  rw [heq]
  exact β.contMDiff_toFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.descend then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.descend"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.descend ``Submission.DifferentialGeometry.DifferentialForm.descend

set_option backward.isDefEq.respectTransparency false in
theorem descend_pullback
    (β : DifferentialForm I M k)
    (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (hβ : ∀ x y : M, ∀ h : f x = f y,
      h ▸ (β x).compContinuousLinearMap (hf.mfderivToContinuousLinearEquiv (by simp) x).symm.toContinuousLinearMap =
        (β y).compContinuousLinearMap (hf.mfderivToContinuousLinearEquiv (by simp) y).symm.toContinuousLinearMap) :
    pullback f hf.contMDiff (descend β hf hsurj hβ) = β := by
  apply ContMDiffSection.ext
  intro x
  exact descendedForm_pullback β hf hsurj hβ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.descend_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.descend_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.descend_pullback ``Submission.DifferentialGeometry.DifferentialForm.descend_pullback


set_option backward.isDefEq.respectTransparency false in
theorem descend_ne_zero
    (β : DifferentialForm I M k)
    (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (hβ : ∀ x y : M, ∀ h : f x = f y,
      h ▸ (β x).compContinuousLinearMap (hf.mfderivToContinuousLinearEquiv (by simp) x).symm.toContinuousLinearMap =
        (β y).compContinuousLinearMap (hf.mfderivToContinuousLinearEquiv (by simp) y).symm.toContinuousLinearMap)
    (hne : ∀ x, β x ≠ 0) (y : N) : descend β hf hsurj hβ y ≠ 0 := by
  obtain ⟨x, rfl⟩ := hsurj y
  intro h
  apply hne x
  have hp := descendedForm_pullback β hf hsurj hβ x
  change (descend β hf hsurj hβ (f x)).compContinuousLinearMap (mfderiv I J f x) = β x at hp
  rw [h] at hp
  exact hp.symm.trans (by ext v; simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.descend_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.descend_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.descend_ne_zero ``Submission.DifferentialGeometry.DifferentialForm.descend_ne_zero

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
private theorem cast_continuousLinearEquiv_apply
    {y z : N} (hyz : y = z) (x : M)
    (D : TangentSpace I x ≃L[Real] TangentSpace J y) (v : TangentSpace I x) :
    (hyz ▸ D) v = hyz ▸ D v := by
  cases hyz
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.DifferentialForm.cast_continuousLinearEquiv_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.DifferentialForm.cast_continuousLinearEquiv_apply target :: scope.openDecls } }

omit [IsManifold J ∞ N] in
private theorem cast_tangent_eq_of_heq
    {y z : N} (hyz : y = z)
    (v : TangentSpace J y) (w : TangentSpace J z) (hvw : HEq v w) : hyz ▸ v = w := by
  cases hyz
  exact eq_of_heq hvw

run_cmd do
  let target := ``Submission.DifferentialGeometry.DifferentialForm.cast_tangent_eq_of_heq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.DifferentialForm.cast_tangent_eq_of_heq target :: scope.openDecls } }

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
private theorem cast_localPush_apply
    (β : ∀ x : M, TangentSpace I x [⋀^Fin k]→L[Real] Real)
    (hf : IsLocalDiffeomorph I J ∞ f) (x : M) {y : N} (hxy : f x = y)
    (v : Fin k → TangentSpace J y) :
    (hxy ▸ localPush β hf x) v =
      β x (fun i => (hxy ▸ hf.mfderivToContinuousLinearEquiv (by simp) x).symm (v i)) := by
  cases hxy
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.DifferentialForm.cast_localPush_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.DifferentialForm.cast_localPush_apply target :: scope.openDecls } }

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem comp_inverse_mfderiv_eq_of_fiber_preserving
    (β : ∀ x : M, TangentSpace I x [⋀^Fin k]→L[Real] Real)
    (hf : IsLocalDiffeomorph I J ∞ f)
    (Phi : M ≃ₘ⟮I, I⟯ M) (hcomp : f ∘ (Phi : M → M) = f)
    (hβ : ∀ x (v : Fin k → TangentSpace I x),
      β (Phi x) (fun i => mfderiv I I Phi x (v i)) = β x v)
    (x : M) :
    congrFun hcomp x ▸
      (β (Phi x)).compContinuousLinearMap
        (hf.mfderivToContinuousLinearEquiv (by simp) (Phi x)).symm.toContinuousLinearMap =
      (β x).compContinuousLinearMap
        (hf.mfderivToContinuousLinearEquiv (by simp) x).symm.toContinuousLinearMap := by
  let hmap : f (Phi x) = f x := congrFun hcomp x
  let A : TangentSpace I (Phi x) ≃L[Real] TangentSpace J (f x) :=
    hmap ▸ hf.mfderivToContinuousLinearEquiv (by simp) (Phi x)
  let B : TangentSpace I x ≃L[Real] TangentSpace J (f x) :=
    hf.mfderivToContinuousLinearEquiv (by simp) x
  let C : TangentSpace I x ≃L[Real] TangentSpace I (Phi x) :=
    Phi.mfderivToContinuousLinearEquiv (by simp) x
  have hchain := mfderiv_comp x
    (hf.contMDiff.mdifferentiableAt (by simp))
    (Phi.contMDiff.mdifferentiableAt (by simp))
  rw [hcomp] at hchain
  have hAC (u : TangentSpace I x) : A (C u) = B u := by
    have hu := ContinuousLinearMap.ext_iff.mp hchain u
    change A (C u) = B u
    dsimp only [A, B, C]
    rw [cast_continuousLinearEquiv_apply]
    exact cast_tangent_eq_of_heq hmap _ _ (heq_of_eq hu.symm)
  have hinv (v : TangentSpace J (f x)) : A.symm v = C (B.symm v) := by
    apply A.injective
    rw [A.apply_symm_apply, hAC, B.apply_symm_apply]
  change congrFun hcomp x ▸ localPush β hf (Phi x) = localPush β hf x
  ext v
  rw [cast_localPush_apply]
  change β (Phi x) (fun i => A.symm (v i)) = β x (fun i => B.symm (v i))
  simp only [hinv]
  exact hβ x (fun i => B.symm (v i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.comp_inverse_mfderiv_eq_of_fiber_preserving then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.comp_inverse_mfderiv_eq_of_fiber_preserving"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.comp_inverse_mfderiv_eq_of_fiber_preserving ``Submission.DifferentialGeometry.DifferentialForm.comp_inverse_mfderiv_eq_of_fiber_preserving


theorem pullback_injective
    (f : M → N) (hf : ContMDiff I J ∞ f) (hsurj : Function.Surjective f)
    (hdf : ∀ x, Function.Surjective (mfderiv I J f x)) :
    Function.Injective (pullback f hf : DifferentialForm J N k → DifferentialForm I M k) := by
  intro α β h
  apply ContMDiffSection.ext
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  ext v
  choose w hw using fun i => hdf x (v i)
  have hx := congrArg (fun form : DifferentialForm I M k => form x) h
  have hv := congrArg (fun form : TangentSpace I x [⋀^Fin k]→L[Real] Real => form w) hx
  simpa [pullback_apply, Function.comp_def, hw] using hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.pullback_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.pullback_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.pullback_injective ``Submission.DifferentialGeometry.DifferentialForm.pullback_injective

theorem eq_descend_of_pullback_eq
    (β : DifferentialForm I M k)
    (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (hβ : ∀ x y : M, ∀ h : f x = f y,
      h ▸ (β x).compContinuousLinearMap
          (hf.mfderivToContinuousLinearEquiv (by simp) x).symm.toContinuousLinearMap =
        (β y).compContinuousLinearMap
          (hf.mfderivToContinuousLinearEquiv (by simp) y).symm.toContinuousLinearMap)
    (α : DifferentialForm J N k) (hα : pullback f hf.contMDiff α = β) :
    α = descend β hf hsurj hβ := by
  apply pullback_injective f hf.contMDiff hsurj
    (fun x => (hf.mfderivToContinuousLinearEquiv (by simp) x).surjective)
  rw [hα, descend_pullback]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.eq_descend_of_pullback_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.eq_descend_of_pullback_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.eq_descend_of_pullback_eq ``Submission.DifferentialGeometry.DifferentialForm.eq_descend_of_pullback_eq

end DifferentialGeometry.DifferentialForm
