import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Pullback
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Basic
import Submission.DifferentialGeometry.Tensor.RSTensor.Functoriality.Pullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Tensor0SBundle

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

theorem totalNabla0SFun_apply_eq_multilinear
    (s : Nat) (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (A : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) s)
    (x : M) (X : TangentSpace I x) (tail : Fin s → TangentSpace I x) :
    totalNabla0SFun s cov A x (Fin.cons X tail) =
      cov.multilinear s (fun y => A y) x X tail := by
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  choose V hV using fun i : Fin s => ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (tail i)
  have htail : (fun i => V i x) = tail := funext hV
  rw [← hY, ← htail, totalNabla0SFun_apply_section,
    nabla0SFun_eval_smooth_slots]
  exact (CovariantDerivative.multilinear_apply cov s (fun i y => V i y)
    A.mdifferentiableAt (fun i => (V i).mdifferentiableAt) (Y x)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_apply_eq_multilinear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_apply_eq_multilinear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_apply_eq_multilinear ``Submission.DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_apply_eq_multilinear

theorem multilinear_pullback_eq_totalNabla0SFun
    (φ : ∀ x : M, TangentSpace I x ≃L[Real] TangentSpace I x)
    (hφ : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ :
        _root_.Bundle.TotalSpace (E →L[Real] E)
          (fun x => TangentSpace I x →L[Real] TangentSpace I x))))
    (s : Nat) (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (A : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) s)
    (x : M) (X : TangentSpace I x) (tail : Fin s → TangentSpace I x) :
    CovariantDerivative.multilinear
        (CovariantDerivative.pullbackFiberwiseLinearEquiv
          (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov) s
        (fun y => tensor0SPullbackCLE (I := I) (M := M) s (φ y).toLinearEquiv (A y))
        x (φ x X) tail =
      tensor0SPullbackCLE (I := I) (M := M) (s + 1) (φ x).toLinearEquiv
        (totalNabla0SFun s cov A x) (Fin.cons X tail) := by
  have hp := CovariantDerivative.multilinear_pullbackFiberwiseLinearEquiv
    φ hφ cov s A.mdifferentiableAt (φ x X)
  have hpull (y : M) :
      tensor0SPullbackCLE (I := I) (M := M) s (φ y).toLinearEquiv (A y) =
        (A y).compContinuousLinearMap (fun _ => (φ y).toContinuousLinearMap) := by
    apply tensor0SSpace_ext s y
    intro v
    simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply]
    rfl
  simp_rw [hpull]
  rw [hp, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply]
  have hslots : (fun i : Fin (s + 1) => (φ x).toLinearEquiv
      ((Fin.cons X tail : Fin (s + 1) → TangentSpace I x) i)) =
      Fin.cons (φ x X) (fun i => φ x (tail i)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [hslots, totalNabla0SFun_apply_eq_multilinear]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.multilinear_pullback_eq_totalNabla0SFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.multilinear_pullback_eq_totalNabla0SFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.multilinear_pullback_eq_totalNabla0SFun ``Submission.DifferentialGeometry.Tensor0SBundle.multilinear_pullback_eq_totalNabla0SFun

end DifferentialGeometry.Tensor0SBundle
