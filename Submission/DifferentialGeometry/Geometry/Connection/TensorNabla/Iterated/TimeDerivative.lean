import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Basic
import Submission.DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace Tensor0SBundle

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Submission.DifferentialGeometry.TensorLieDeriv
    DifferentialGeometry
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [T2Space M]

omit [CompleteSpace E] [T2Space M] in
theorem nabla0SFun_hasDerivWithinAt_pt {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (α β : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (timeSet : Set Real) (x₀ : M) (t : Real)
    (hswap :
      HasDerivWithinAt
        (fun r : Real => mvfderiv (I := I)
          (fun p : M => (α r) p (fun a : Fin s => V a p)) x₀ (X x₀))
        (mvfderiv (I := I)
          (fun p : M => (β t) p (fun a : Fin s => V a p)) x₀ (X x₀))
        timeSet t)
    (hpt : ∀ a : Fin s,
      HasDerivWithinAt
        (fun r : Real => (α r) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        ((β t) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        timeSet t) :
    HasDerivWithinAt
      (fun r : Real =>
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X (α r) x₀) (fun a : Fin s => V a x₀))
      ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X (β t) x₀) (fun a : Fin s => V a x₀))
      timeSet t := by
  simp only [nabla0SFun_eval_smooth_slots]
  refine HasDerivWithinAt.sub ?_ ?_
  · exact hswap
  · have key :
        (fun r : Real => ∑ a : Fin s, (α r) x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (fun p : M => V a p) x₀) (X x₀))))
          = ∑ a : Fin s, (fun r : Real => (α r) x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (fun p : M => V a p) x₀) (X x₀)))) := by
      funext r
      simp only [Finset.sum_apply]
    rw [key]
    exact HasDerivWithinAt.sum (fun (a : Fin s) (_ : a ∈ Finset.univ) => hpt a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.nabla0SFun_hasDerivWithinAt_pt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.nabla0SFun_hasDerivWithinAt_pt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.nabla0SFun_hasDerivWithinAt_pt ``Submission.DifferentialGeometry.Tensor0SBundle.nabla0SFun_hasDerivWithinAt_pt

omit [CompleteSpace E] [T2Space M] in
theorem nabla0SFun_hasDerivWithinAt {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (α β : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (timeSet : Set Real) (x₀ : M) (t : Real)
    (hswap :
      FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet ({x₀} : Set M)
        (fun r p => (α r) p (fun a : Fin s => V a p))
        (fun r p => (β r) p (fun a : Fin s => V a p)))
    (hpt : ∀ a : Fin s,
      HasDerivWithinAt
        (fun r : Real => (α r) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        ((β t) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        timeSet t) :
    HasDerivWithinAt
      (fun r : Real =>
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X (α r) x₀) (fun a : Fin s => V a x₀))
      ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X (β t) x₀) (fun a : Fin s => V a x₀))
      timeSet t :=
  nabla0SFun_hasDerivWithinAt_pt cov X V α β timeSet x₀ t
    (hswap t x₀ (Set.mem_singleton x₀) (X x₀)) hpt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.nabla0SFun_hasDerivWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.nabla0SFun_hasDerivWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.nabla0SFun_hasDerivWithinAt ``Submission.DifferentialGeometry.Tensor0SBundle.nabla0SFun_hasDerivWithinAt

omit [CompleteSpace E] [T2Space M] in
theorem totalNabla0SFun_hasDerivWithinAt_pt {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (α β : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (timeSet : Set Real) (x₀ : M) (t : Real)
    (hswap :
      HasDerivWithinAt
        (fun r : Real => mvfderiv (I := I)
          (fun p : M => (α r) p (fun a : Fin s => V a p)) x₀ (X x₀))
        (mvfderiv (I := I)
          (fun p : M => (β t) p (fun a : Fin s => V a p)) x₀ (X x₀))
        timeSet t)
    (hpt : ∀ a : Fin s,
      HasDerivWithinAt
        (fun r : Real => (α r) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        ((β t) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        timeSet t) :
    HasDerivWithinAt
      (fun r : Real =>
        (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov (α r) x₀) (Fin.cons (X x₀) (fun a : Fin s => V a x₀)))
      ((totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov (β t) x₀) (Fin.cons (X x₀) (fun a : Fin s => V a x₀)))
      timeSet t := by
  simpa only [totalNabla0SFun_apply_section] using
    nabla0SFun_hasDerivWithinAt_pt cov X V α β timeSet x₀ t hswap hpt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_hasDerivWithinAt_pt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_hasDerivWithinAt_pt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_hasDerivWithinAt_pt ``Submission.DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_hasDerivWithinAt_pt

omit [CompleteSpace E] [T2Space M] in
theorem totalNabla0SFun_hasDerivWithinAt {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (α β : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (timeSet : Set Real) (x₀ : M) (t : Real)
    (hswap :
      FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet ({x₀} : Set M)
        (fun r p => (α r) p (fun a : Fin s => V a p))
        (fun r p => (β r) p (fun a : Fin s => V a p)))
    (hpt : ∀ a : Fin s,
      HasDerivWithinAt
        (fun r : Real => (α r) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        ((β t) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        timeSet t) :
    HasDerivWithinAt
      (fun r : Real =>
        (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov (α r) x₀) (Fin.cons (X x₀) (fun a : Fin s => V a x₀)))
      ((totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov (β t) x₀) (Fin.cons (X x₀) (fun a : Fin s => V a x₀)))
      timeSet t :=
  totalNabla0SFun_hasDerivWithinAt_pt cov X V α β timeSet x₀ t
    (hswap t x₀ (Set.mem_singleton x₀) (X x₀)) hpt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_hasDerivWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_hasDerivWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_hasDerivWithinAt ``Submission.DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_hasDerivWithinAt

end Tensor0SBundle
end DifferentialGeometry
