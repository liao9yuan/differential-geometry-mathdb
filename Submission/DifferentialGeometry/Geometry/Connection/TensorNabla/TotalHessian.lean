import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.TotalPullback
import Submission.DifferentialGeometry.Geometry.Connection.Hessian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Tensor0SBundle

open _root_.Bundle _root_.Submission.Bundle _root_.CovariantDerivative _root_.Submission.CovariantDerivative
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem totalNabla0S_curryLeft_eq_multilinear
    (s : Nat) (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (A : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) s)
    (hreg : TotalNabla0SRegular s cov A) (x : M) :
    Bundle.continuousMultilinearMap.curryLeftEquiv
        (𝕜 := ℝ) (F := E) (E := TangentSpace I) s x
        (totalNabla0S s cov A hreg x) =
      cov.multilinear s (fun y => A y) x := by
  ext X tail
  change totalNabla0SFun s cov A x (Fin.cons X tail) = _
  exact totalNabla0SFun_apply_eq_multilinear s cov A x X tail

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.totalNabla0S_curryLeft_eq_multilinear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.totalNabla0S_curryLeft_eq_multilinear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.totalNabla0S_curryLeft_eq_multilinear ``Submission.DifferentialGeometry.Tensor0SBundle.totalNabla0S_curryLeft_eq_multilinear

theorem totalNabla0SFun_totalNabla0S_apply_eq_hessian
    (s : Nat) (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (A : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) s)
    (hreg : TotalNabla0SRegular s cov A)
    (x : M) (X Y : TangentSpace I x) (tail : Fin s → TangentSpace I x) :
    totalNabla0SFun (s + 1) cov (totalNabla0S s cov A hreg) x
        (Fin.cons X (Fin.cons Y tail)) =
      (cov.multilinear s).hessian cov (fun y => A y) x X Y tail := by
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Y
  let B := totalNabla0S s cov A hreg
  have hDB : (fun y => Bundle.continuousMultilinearMap.curryLeftEquiv
      (𝕜 := ℝ) (F := E) (E := TangentSpace I) s y (B y)) =
      (fun y => cov.multilinear s (fun z => A z) y) := by
    exact funext (totalNabla0S_curryLeft_eq_multilinear s cov A hreg)
  have hD : MDifferentiableAt I
      (I.prod 𝓘(ℝ, E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ))
      (fun y => TotalSpace.mk'
        (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) y
        (cov.multilinear s (fun z => A z) y)) x := by
    change MDifferentiableAt I _ (fun y => TotalSpace.mk' _ y
      ((fun z => cov.multilinear s (fun w => A w) z) y)) x
    rw [← hDB]
    exact B.mdifferentiableAt.multilinear_bundle_curry_left
  have hAB : (fun y => Bundle.continuousMultilinearMap.curryLeftEquiv
      (𝕜 := ℝ) (F := E) (E := TangentSpace I) s y (B y) (Z y)) =
      (fun y => cov.multilinear s (fun z => A z) y (Z y)) := by
    funext y
    ext v
    change B y (Fin.cons (Z y) v) = _
    exact totalNabla0SFun_apply_eq_multilinear s cov A y (Z y) v
  erw [← hZ, totalNabla0SFun_apply_eq_multilinear,
    multilinear_apply_succ cov s B.mdifferentiableAt Z.mdifferentiableAt,
    hAB, totalNabla0S_apply, totalNabla0SFun_apply_eq_multilinear,
    hessian_apply (cov.multilinear s) cov hD Z.mdifferentiableAt]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_totalNabla0S_apply_eq_hessian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_totalNabla0S_apply_eq_hessian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_totalNabla0S_apply_eq_hessian ``Submission.DifferentialGeometry.Tensor0SBundle.totalNabla0SFun_totalNabla0S_apply_eq_hessian

end DifferentialGeometry.Tensor0SBundle
