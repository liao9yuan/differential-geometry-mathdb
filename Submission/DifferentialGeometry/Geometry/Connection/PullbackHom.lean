import Submission.DifferentialGeometry.Bundle.Hom
import Submission.DifferentialGeometry.Bundle.Equiv
import Submission.DifferentialGeometry.Geometry.Connection.Pullback
import Submission.DifferentialGeometry.Geometry.Connection.HomBundle.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.CovariantDerivative _root_.Submission.CovariantDerivative
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.HomConnectionGen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle ∞ F₁ V₁ I]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]

variable [∀ x, T2Space (V₂ x)]

theorem homBundleCovariantDerivativeGen_pullbackFiberwiseLinearEquiv
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : _root_.Bundle.TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))))
    (cov : CovariantDerivative I F₂ V₂) :
    homBundleCovariantDerivativeGen I M F₁ V₁ F₂ V₂
      (pullbackFiberwiseLinearEquiv (fun x => (φ x).toLinearEquiv) hφ.clm_bundle_map cov)
      cov (fun x => (φ x).toContinuousLinearMap) = 0 := by
  funext x
  ext v w
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I) (F := F₁)
    (V := V₁) (n := (⊤ : ℕ∞)) x w
  rw [← hX, ← hY]
  rw [homBundleCovariantDerivativeGen_apply_of_mdifferentiableAt I M F₁ V₁ F₂ V₂
    _ cov _ ((hφ x).mdifferentiableAt (by simp)) X.mdifferentiableAt Y.mdifferentiableAt]
  have hp := CovariantDerivative.map_pullbackFiberwiseLinearEquiv_apply
    (fun x => (φ x).toLinearEquiv) hφ.clm_bundle_map cov (fun y => Y y) x (X x)
  change cov (fun y => φ y (Y y)) x (X x) -
    φ x (pullbackFiberwiseLinearEquiv (fun x => (φ x).toLinearEquiv)
      hφ.clm_bundle_map cov (fun y => Y y) x (X x)) = 0
  exact sub_eq_zero.mpr hp.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_pullbackFiberwiseLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_pullbackFiberwiseLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_pullbackFiberwiseLinearEquiv ``Submission.DifferentialGeometry.HomConnectionGen.homBundleCovariantDerivativeGen_pullbackFiberwiseLinearEquiv

variable [ContMDiffVectorBundle ∞ F₂ V₂ I]

theorem map_homBundleCovariantDerivativeGen_conjugate
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : _root_.Bundle.TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))))
    (cov : CovariantDerivative I F₂ V₂)
    {A : ∀ x, V₂ x →L[ℝ] V₂ x} {x : M}
    (hA : MDifferentiableAt I (I.prod 𝓘(ℝ, F₂ →L[ℝ] F₂))
      (fun y => (⟨y, A y⟩ : _root_.Bundle.TotalSpace (F₂ →L[ℝ] F₂)
        (fun y => V₂ y →L[ℝ] V₂ y))) x)
    (v : TangentSpace I x) :
    (φ x).toContinuousLinearMap.comp
      (homBundleCovariantDerivativeGen I M F₁ V₁ F₁ V₁
        (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov)
        (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov)
        (fun y => (φ y).symm.toContinuousLinearMap.comp
          ((A y).comp (φ y).toContinuousLinearMap)) x v) =
      (homBundleCovariantDerivativeGen I M F₂ V₂ F₂ V₂ cov cov A x v).comp
        (φ x).toContinuousLinearMap := by
  let _ : CompleteSpace F₁ := FiniteDimensional.complete ℝ F₁
  let D := pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov
  let B := fun y => (φ y).symm.toContinuousLinearMap.comp
    ((A y).comp (φ y).toContinuousLinearMap)
  have hφinv : ContMDiff I (I.prod 𝓘(ℝ, F₂ →L[ℝ] F₁)) 1
      (fun y => (⟨y, (φ y).symm.toContinuousLinearMap⟩ : _root_.Bundle.TotalSpace (F₂ →L[ℝ] F₁)
        (fun y => V₂ y →L[ℝ] V₁ y))) := by
    simpa only [ContinuousLinearMap.inverse_equiv] using
      hφ.clm_bundle_inverse (fun _ => ContinuousLinearMap.isInvertible_equiv)
  have hφx := (hφ x).mdifferentiableAt (by simp)
  have hBx := ((hφinv x).mdifferentiableAt (by simp)).clm_bundle_comp
    (hA.clm_bundle_comp hφx)
  have hp : homBundleCovariantDerivativeGen I M F₁ V₁ F₂ V₂
      D cov (fun y => (φ y).toContinuousLinearMap) = 0 :=
    homBundleCovariantDerivativeGen_pullbackFiberwiseLinearEquiv φ hφ cov
  have hl := homBundleCovariantDerivativeGen_comp D D cov hBx hφx v
  have hr := homBundleCovariantDerivativeGen_comp D cov cov hφx hA v
  have heq : (fun y => (φ y).toContinuousLinearMap.comp (B y)) =
      (fun y => (A y).comp (φ y).toContinuousLinearMap) := by
    funext y
    ext w
    simp [B]
  change (φ x).toContinuousLinearMap.comp
      (homBundleCovariantDerivativeGen I M F₁ V₁ F₁ V₁ D D B x v) = _
  change homBundleCovariantDerivativeGen I M F₁ V₁ F₂ V₂ D cov
    (fun y => (φ y).toContinuousLinearMap.comp (B y)) x v = _ at hl
  rw [hp] at hl hr
  simp only [Pi.zero_apply, zero_apply, ContinuousLinearMap.zero_comp, zero_add,
    ContinuousLinearMap.comp_zero, add_zero] at hl hr
  rw [← hl, heq, hr]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomConnectionGen.map_homBundleCovariantDerivativeGen_conjugate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomConnectionGen.map_homBundleCovariantDerivativeGen_conjugate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomConnectionGen.map_homBundleCovariantDerivativeGen_conjugate ``Submission.DifferentialGeometry.HomConnectionGen.map_homBundleCovariantDerivativeGen_conjugate

end DifferentialGeometry.HomConnectionGen
