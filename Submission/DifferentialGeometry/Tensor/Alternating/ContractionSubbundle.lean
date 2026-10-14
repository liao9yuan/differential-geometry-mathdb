import Submission.DifferentialGeometry.Bundle.SmoothSubbundle.KernelAPI
import Submission.DifferentialGeometry.Tensor.Alternating.Coordinates.Basis
import Submission.DifferentialGeometry.Tensor.Alternating.Bundle.Defs
import Submission.DifferentialGeometry.Tensor.Alternating.Contraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace ContinuousAlternatingMap
open _root_.ContinuousAlternatingMap

universe uE uH uM uF uV

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type uV} [∀ x, NormedAddCommGroup (V x)]
variable [∀ x, NormedSpace ℝ (V x)]
variable [totalSpaceTopology : TopologicalSpace (TotalSpace F V)]
variable [fiberBundle : FiberBundle F V]
variable [vectorBundle : VectorBundle ℝ F V]
variable [smoothVectorBundle : ContMDiffVectorBundle ∞ F V I]

open _root_.ContinuousAlternatingMap in
noncomputable local instance contractionCurryTopology :
    TopologicalSpace (_root_.Bundle.TotalSpace
      (F →L[ℝ] F [⋀^Fin 1]→L[ℝ] ℝ)
      (fun x : M => V x →L[ℝ] V x [⋀^Fin 1]→L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ)
    F V (F [⋀^Fin 1]→L[ℝ] ℝ)
      (fun x : M => V x [⋀^Fin 1]→L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.contractionCurryTopology then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.contractionCurryTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.contractionCurryTopology ``Submission.ContinuousAlternatingMap.contractionCurryTopology

open _root_.ContinuousAlternatingMap in
noncomputable local instance contractionCurryFiber :
    FiberBundle (F →L[ℝ] F [⋀^Fin 1]→L[ℝ] ℝ)
      (fun x : M => V x →L[ℝ] V x [⋀^Fin 1]→L[ℝ] ℝ) :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id ℝ)
    F V (F [⋀^Fin 1]→L[ℝ] ℝ)
      (fun x : M => V x [⋀^Fin 1]→L[ℝ] ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.contractionCurryFiber then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.contractionCurryFiber"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.contractionCurryFiber ``Submission.ContinuousAlternatingMap.contractionCurryFiber

open _root_.ContinuousAlternatingMap in
private theorem exists_smooth_contractionAnnihilator_of_local_curry
    (hF : Module.finrank ℝ F = 3)
    (K : ∀ x : M,
      Submodule ℝ (V x [⋀^Fin 2]→L[ℝ] ℝ))
    (hK : ∀ x, Module.finrank ℝ (K x) = 1)
    (hlocal : ∀ x₀, ∃ W : Set M,
      ∃ form : (x : M) → V x [⋀^Fin 2]→L[ℝ] ℝ,
      IsOpen W ∧ x₀ ∈ W ∧
      ContMDiffOn I (I.prod
        𝓘(ℝ, F →L[ℝ] F [⋀^Fin 1]→L[ℝ] ℝ)) ∞
        (fun x => TotalSpace.mk'
          (F →L[ℝ] F [⋀^Fin 1]→L[ℝ] ℝ) x (form x).curryLeft) W ∧
      ∀ x ∈ W, K x = Submodule.span ℝ {form x}) :
    ∃ S : ContMDiffVectorSubbundle
        (I := I) (F := F) (V := V) (n := (∞ : WithTop ℕ∞)),
      S.rank = 1 ∧
      ∀ x, S.fiber x = contractionAnnihilator (K x) := by
  let basis := Module.finBasis ℝ F
  let _ : FiniteDimensional ℝ (F [⋀^Fin 1]→L[ℝ] ℝ) :=
    (elementaryCovectorBasis (k := 1) basis).finiteDimensional_of_finite
  apply ContMDiffVectorSubbundle.exists_smooth_subbundle_of_locally_eq_kernel
    (F₂ := F [⋀^Fin 1]→L[ℝ] ℝ)
    (V₂ := fun x : M => V x [⋀^Fin 1]→L[ℝ] ℝ)
    (fun x => contractionAnnihilator (K x)) 1
  intro x₀
  obtain ⟨W, form, hW, hx₀W, hform, hspan⟩ := hlocal x₀
  let A : ∀ x : M, V x →L[ℝ] V x [⋀^Fin 1]→L[ℝ] ℝ :=
    fun x => (form x).curryLeft
  refine ⟨W, A, hW, hx₀W, ?_, ?_, ?_⟩
  · simpa [A] using hform
  · intro x hx
    let e := (_root_.FiberBundle.trivializationAt F V x).linearEquivAt ℝ x
      (_root_.FiberBundle.mem_baseSet_trivializationAt F V x)
    let _ : FiniteDimensional ℝ (V x) :=
      FiniteDimensional.of_injective e.toLinearMap e.injective
    have hV : Module.finrank ℝ (V x) = 3 := e.finrank_eq.trans hF
    rw [← contractionAnnihilator_span_singleton (form x), ← hspan x hx]
    exact finrank_contractionAnnihilator_eq_one hV (K x) (hK x)
  · intro x hx
    rw [hspan x hx, contractionAnnihilator_span_singleton]

run_cmd do
  let target := ``Submission.ContinuousAlternatingMap.exists_smooth_contractionAnnihilator_of_local_curry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `ContinuousAlternatingMap.exists_smooth_contractionAnnihilator_of_local_curry target :: scope.openDecls } }

open _root_.ContinuousAlternatingMap in
theorem exists_smooth_contractionAnnihilator
    (hF : Module.finrank ℝ F = 3)
    (K : ContMDiffVectorSubbundle
      (I := I) (F := F [⋀^Fin 2]→L[ℝ] ℝ)
      (V := fun x => V x [⋀^Fin 2]→L[ℝ] ℝ) (n := (∞ : WithTop ℕ∞)))
    (hK : K.rank = 1) :
    ∃ S : ContMDiffVectorSubbundle
        (I := I) (F := F) (V := V) (n := (∞ : WithTop ℕ∞)),
      S.rank = 1 ∧
      ∀ x, S.fiber x = contractionAnnihilator (K.fiber x) := by
  apply exists_smooth_contractionAnnihilator_of_local_curry hF K.fiber
  · intro x
    rw [K.finrank_fiber, hK]
  · intro x₀
    obtain ⟨W, s, hW, hx₀W, hs⟩ := K.exists_frame x₀
    let i₀ : Fin K.rank := ⟨0, by omega⟩
    refine ⟨W, fun x => s i₀ x, hW, hx₀W, ?_, ?_⟩
    · exact contMDiffOn_curryLeft (form := fun x => s i₀ x) (hs.contMDiffOn i₀)
    · intro x hx
      have hrange_s : Set.range (s · x) = {s i₀ x} := by
        ext form
        constructor
        · rintro ⟨i, rfl⟩
          have hi : i = i₀ := by
            apply Fin.ext
            omega
          subst i
          exact Set.mem_singleton _
        · intro hform
          have hform' : form = s i₀ x := by simpa using hform
          exact ⟨i₀, hform'.symm⟩
      rw [← hs.spans hx, hrange_s]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.exists_smooth_contractionAnnihilator then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.exists_smooth_contractionAnnihilator"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.exists_smooth_contractionAnnihilator ``Submission.ContinuousAlternatingMap.exists_smooth_contractionAnnihilator

end ContinuousAlternatingMap
