import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.FixedChart.Models
import Submission.DifferentialGeometry.Bundle.TangentSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry
namespace TensorLieDeriv

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.VectorField _root_.Filter
    DifferentialGeometry.Tensor0SBundle Function
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section SmoothVectorFieldRSNabla

variable [IsManifold I 1 M] [IsManifold I (n + 1) M]

noncomputable def fixedChartNabla0SModel (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (x₀ : M) [IsManifold I 2 M] (y : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  covariantDerivTensor0SModelWithin (𝕜 := 𝕜) (E := E) s
    (fun z => tangentSpaceModelContinuousLinearEquiv z
      (_root_.VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (_root_.Set.range I) z))
    (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
    (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) s x₀ (fun x => α x))
    (_root_.Set.range I) y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.fixedChartNabla0SModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.fixedChartNabla0SModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.fixedChartNabla0SModel ``Submission.DifferentialGeometry.TensorLieDeriv.fixedChartNabla0SModel

omit [IsManifold I n M] [IsManifold I (n + 1) M] in
theorem fixedChartNabla0SModel_apply_slots (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (x₀ : M) [IsManifold I 2 M] (y : E) (slots : Fin s → E) :
    fixedChartNabla0SModel (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (n := n) s cov X α x₀ y slots =
      fderivWithin 𝕜
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) s x₀ (fun x => α x))
        (_root_.Set.range I) y
        (tangentSpaceModelContinuousLinearEquiv y
          (_root_.VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (_root_.Set.range I) y))
        slots -
      ∑ a : Fin s,
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) s x₀ (fun x => α x)) y
          (Function.update slots a
            ((connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov
              (fun x => X x) x₀ y) (slots a))) := by
  unfold fixedChartNabla0SModel
  rw [covariantDeriv_tensor0SModelWithin_apply_slots]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.fixedChartNabla0SModel_apply_slots then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.fixedChartNabla0SModel_apply_slots"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.fixedChartNabla0SModel_apply_slots ``Submission.DifferentialGeometry.TensorLieDeriv.fixedChartNabla0SModel_apply_slots

omit [IsManifold I n M] [IsManifold I (n + 1) M] in
theorem fixedChartNabla0SModel_apply_slots_of_mem (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (x₀ : M) [IsManifold I 2 M] {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (slots : Fin s → E) :
    fixedChartNabla0SModel (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (n := n) s cov X α x₀ y slots =
      fderivWithin 𝕜
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) s x₀ (fun x => α x))
        (_root_.Set.range I) y
        (tangentSpaceModelContinuousLinearEquiv y
          (_root_.VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (_root_.Set.range I) y))
        slots -
      ∑ a : Fin s,
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) s x₀ (fun x => α x)) y
          (Function.update slots a
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearMapAt
              𝕜 ((extChartAt I x₀).symm y)
                ((cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (slots a))
                ((extChartAt I x₀).symm y))
                (X ((extChartAt I x₀).symm y))))) := by
  unfold fixedChartNabla0SModel
  rw [covariantDeriv_tensor0SModelWithin_apply_slots]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 2
  exact connectionEndomorphismInChart_apply_of_mem
    (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀ hy (slots a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.fixedChartNabla0SModel_apply_slots_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.fixedChartNabla0SModel_apply_slots_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.fixedChartNabla0SModel_apply_slots_of_mem ``Submission.DifferentialGeometry.TensorLieDeriv.fixedChartNabla0SModel_apply_slots_of_mem

omit [IsManifold I n M] in
theorem fixedChartNabla0SModel_contDiffWithinAt (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov n)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s)
    (x₀ : M) [IsManifold I 2 M] [IsManifold I (n + 1 + 1) M]
    (hmn : n + 1 ≤ n) :
    ContDiffWithinAt 𝕜 n
      (fixedChartNabla0SModel (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (n := n) s cov X α x₀)
      (_root_.Set.range I) (extChartAt I x₀ x₀) := by
  have hα :
      ContDiffWithinAt 𝕜 n
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) s x₀ (fun x => α x))
        (_root_.Set.range I) (extChartAt I x₀ x₀) := by
    have h := tensor0SModelInChart_contMDiffWithinAt
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := n) s x₀ α
    simpa using h.contDiffWithinAt
  have hX :
      ContDiffWithinAt 𝕜 n
        (fun y => tangentSpaceModelContinuousLinearEquiv y
          (_root_.VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (_root_.Set.range I) y))
        (_root_.Set.range I) (extChartAt I x₀ x₀) := by
    have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
    let z₀ : E := extChartAt I x₀ x₀
    let Wraw : (y : E) → TangentSpace 𝓘(𝕜, E) y :=
      _root_.VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (_root_.Set.range I)
    let W : E → E := fun y => tangentSpaceModelContinuousLinearEquiv y (Wraw y)
    let e := _root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(𝕜, E) : E → Type _) z₀
    have h :=
      VectorField.contMDiffWithinAt_mpullbackWithin_extChartAt_symm
        (I := I) (M := M) (n := n + 1)
        (m := n) (s := Set.univ) (V := fun x => X x)
        (X.contMDiff x₀) uniqueMDiffOn_univ (Set.mem_univ x₀)
        (by simp)
    have htotal :
        ContMDiffWithinAt 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E)) n
          (fun y : E =>
            (⟨y, Wraw y⟩ :
              _root_.Bundle.TotalSpace E (TangentSpace 𝓘(𝕜, E) : E → Type _)))
          (_root_.Set.range I) z₀ := by
      have htarget :
          (extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' Set.univ
            ∈ 𝓝[_root_.Set.range I] z₀ := by
        simpa [z₀] using extChartAt_target_mem_nhdsWithin (I := I) x₀
      have h' := h.mono_of_mem_nhdsWithin htarget
      simpa [Wraw, z₀, Set.univ_inter] using h'
    have hzsrc :
        (⟨z₀, Wraw z₀⟩ :
          TotalSpace E (TangentSpace 𝓘(𝕜, E) : E → Type _)) ∈ e.source := by
      exact FiberBundle.mem_trivializationAt_proj_source
    have hcoord :
        ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E) n
          (fun y : E =>
            (e (⟨y, Wraw y⟩ :
              _root_.Bundle.TotalSpace E (TangentSpace 𝓘(𝕜, E) : E → Type _))).2)
          (_root_.Set.range I) z₀ :=
      ((Bundle.Trivialization.contMDiffWithinAt_iff
        (e := e)
        (f := fun y : E =>
          (⟨y, Wraw y⟩ :
            _root_.Bundle.TotalSpace E (TangentSpace 𝓘(𝕜, E) : E → Type _)))
        (s := _root_.Set.range I) (x₀ := z₀) hzsrc).mp htotal).2
    have heq :
        (fun y : E =>
            (e (⟨y, Wraw y⟩ :
              _root_.Bundle.TotalSpace E (TangentSpace 𝓘(𝕜, E) : E → Type _))).2)
          =ᶠ[𝓝[_root_.Set.range I] z₀] W := by
      filter_upwards with y
      simp [e, W, tangentSpaceModelContinuousLinearEquiv_apply]
      rfl
    have heq₀ :
        (e (⟨z₀, Wraw z₀⟩ :
          TotalSpace E (TangentSpace 𝓘(𝕜, E) : E → Type _))).2 = W z₀ := by
      simp [e, W, tangentSpaceModelContinuousLinearEquiv_apply]
      rfl
    simpa [Wraw, W, z₀] using
      hcoord.contDiffWithinAt.congr_of_eventuallyEq heq.symm heq₀.symm
  have hΓ :
      ContDiffWithinAt 𝕜 n
        (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
        (_root_.Set.range I) (extChartAt I x₀ x₀) :=
    connectionEndomorphismInChart_contDiffWithinAt
      (𝕜 := 𝕜) (I := I) (M := M) (n := n) cov hcov X x₀
  have hx : extChartAt I x₀ x₀ ∈ _root_.Set.range I :=
    extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)
  unfold fixedChartNabla0SModel
  exact contDiffWithinAt_covariantDeriv_tensor0SModelWithin
    (𝕜 := 𝕜) (E := E) s hα hX hΓ I.uniqueDiffOn hmn hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.TensorLieDeriv.fixedChartNabla0SModel_contDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.TensorLieDeriv.fixedChartNabla0SModel_contDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.TensorLieDeriv.fixedChartNabla0SModel_contDiffWithinAt ``Submission.DifferentialGeometry.TensorLieDeriv.fixedChartNabla0SModel_contDiffWithinAt
end SmoothVectorFieldRSNabla

end

end TensorLieDeriv
end DifferentialGeometry
