import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Basic

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
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [T2Space M]

omit [CompleteSpace E] in
theorem totalNabla0SFun_smul {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (c : Real)
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov (c • α) x
      = c • totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov α x := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro idx
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis (idx 0))).choose
  have hX : X x = basis (idx 0) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis (idx 0))).choose_spec
  have hcons :
      (fun a : Fin (s + 1) => basis (idx a))
        = Fin.cons (X x) (fun a : Fin s => basis (idx a.succ)) := by
    funext a
    induction a using Fin.cases with
    | zero => rw [Fin.cons_zero]; exact hX.symm
    | succ j => rw [Fin.cons_succ]
  rw [component0S_apply, component0S_apply, hcons]
  rw [Tensor0SSpace.smul_apply, totalNabla0SFun_apply_section,
    totalNabla0SFun_apply_section, nabla0SFun_smul]
  rw [Tensor0SSpace.smul_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_smul ``Submission.DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_smul

omit [CompleteSpace E] in
theorem totalNabla0SFun_add {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov (α + β) x
      = totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov α x
        + totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov β x := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro idx
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis (idx 0))).choose
  have hX : X x = basis (idx 0) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis (idx 0))).choose_spec
  have hcons :
      (fun a : Fin (s + 1) => basis (idx a))
        = Fin.cons (X x) (fun a : Fin s => basis (idx a.succ)) := by
    funext a
    induction a using Fin.cases with
    | zero => rw [Fin.cons_zero]; exact hX.symm
    | succ j => rw [Fin.cons_succ]
  rw [component0S_apply, component0S_apply, hcons]
  rw [Tensor0SSpace.add_apply, totalNabla0SFun_apply_section,
    totalNabla0SFun_apply_section, totalNabla0SFun_apply_section, nabla0SFun_add]
  rw [Tensor0SSpace.add_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_add ``Submission.DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_add

end Tensor0SBundle
end DifferentialGeometry
