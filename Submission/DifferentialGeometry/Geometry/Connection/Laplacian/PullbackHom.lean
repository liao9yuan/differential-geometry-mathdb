import Submission.DifferentialGeometry.Geometry.Connection.PullbackHom
import Submission.DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.CovariantDerivative _root_.Submission.CovariantDerivative
open _root_.Submission.DifferentialGeometry.HomConnectionGen
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, NormedSpace ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle ∞ F₁ V₁ I]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, NormedSpace ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle ∞ F₂ V₂ I]

theorem map_secondCovDeriv_hom_conjugate
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : _root_.Bundle.TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))))
    (cov : CovariantDerivative I F₂ V₂) [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (base : CovariantDerivative I E (TangentSpace I : M → Type _))
    (A : Cₛ^∞⟮I; F₂ →L[ℝ] F₂, (fun x => V₂ x →L[ℝ] V₂ x)⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (X : TangentSpace I x) :
    let D := pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov
    let DE := homBundleCovariantDerivativeGen I M F₁ V₁ F₁ V₁ D D
    let CE := homBundleCovariantDerivativeGen I M F₂ V₂ F₂ V₂ cov cov
    let B := fun y => (φ y).symm.toContinuousLinearMap.comp
      ((A y).comp (φ y).toContinuousLinearMap)
    (φ x).toContinuousLinearMap.comp
      (DE (covApply DE (fun y => Y y) B) x X - DE B x (base (fun y => Y y) x X)) =
      (CE (covApply CE (fun y => Y y) (fun y => A y)) x X -
        CE (fun y => A y) x (base (fun y => Y y) x X)).comp (φ x).toContinuousLinearMap := by
  dsimp only
  let D := pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv)
    hφ.clm_bundle_map cov
  let DE := homBundleCovariantDerivativeGen I M F₁ V₁ F₁ V₁ D D
  let CE := homBundleCovariantDerivativeGen I M F₂ V₂ F₂ V₂ cov cov
  let B := fun y => (φ y).symm.toContinuousLinearMap.comp
    ((A y).comp (φ y).toContinuousLinearMap)
  have hfirst (T : Cₛ^∞⟮I; F₂ →L[ℝ] F₂, (fun y => V₂ y →L[ℝ] V₂ y)⟯)
      (y : M) (v : TangentSpace I y) :
      (φ y).toContinuousLinearMap.comp
        (DE (fun z => (φ z).symm.toContinuousLinearMap.comp
          ((T z).comp (φ z).toContinuousLinearMap)) y v) =
        (CE (fun z => T z) y v).comp (φ y).toContinuousLinearMap :=
    map_homBundleCovariantDerivativeGen_conjugate φ hφ cov
      T.mdifferentiableAt v
  let C : Cₛ^∞⟮I; F₂ →L[ℝ] F₂, (fun y => V₂ y →L[ℝ] V₂ y)⟯ :=
    ⟨covApply CE Y (fun y => A y), contMDiffOn_univ.mp
      (covApply_contMDiffOn (cov := CE) Y.contMDiff
        (by simpa using A.contMDiff))⟩
  have hDB : covApply DE Y B = fun y => (φ y).symm.toContinuousLinearMap.comp
      ((C y).comp (φ y).toContinuousLinearMap) := by
    funext y
    ext z
    apply (φ y).injective
    have h := congrArg (fun L => L z) (hfirst A y (Y y))
    simpa [B, C, covApply] using h
  ext w
  simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub]
  change φ x ((DE (covApply DE Y B) x X) w) -
      φ x ((DE B x (base Y x X)) w) =
    (CE (covApply CE Y (fun y => A y)) x X) (φ x w) -
      (CE (fun y => A y) x (base Y x X)) (φ x w)
  rw [hDB]
  have hs := congrArg (fun L => L w) (hfirst C x X)
  have hf := congrArg (fun L => L w) (hfirst A x (base Y x X))
  exact congrArg₂ (fun a b : V₂ x => a - b) hs hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.map_secondCovDeriv_hom_conjugate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.map_secondCovDeriv_hom_conjugate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.map_secondCovDeriv_hom_conjugate ``Submission.DifferentialGeometry.Geometry.Connection.map_secondCovDeriv_hom_conjugate


theorem map_rawBundleConnLap_hom_conjugate
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : _root_.Bundle.TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))))
    (cov : CovariantDerivative I F₂ V₂) [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (g : SmoothRiemannianMetric I M)
    (A : Cₛ^∞⟮I; F₂ →L[ℝ] F₂, (fun x => V₂ x →L[ℝ] V₂ x)⟯)
    (x : M) :
    (φ x).toContinuousLinearMap.comp
      (rawBundleConnLap g
        (homBundleCovariantDerivativeGen I M F₁ V₁ F₁ V₁
          (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv)
            hφ.clm_bundle_map cov)
          (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv)
            hφ.clm_bundle_map cov))
        (fun y => (φ y).symm.toContinuousLinearMap.comp
          ((A y).comp (φ y).toContinuousLinearMap)) x) =
      (rawBundleConnLap g
        (homBundleCovariantDerivativeGen I M F₂ V₂ F₂ V₂ cov cov) (fun y => A y) x).comp
          (φ x).toContinuousLinearMap := by
  ext w
  simp only [ContinuousLinearMap.comp_apply, rawBundleConnLap_def, _root_.sum_apply,
    sub_apply, map_sum, map_sub]
  apply Finset.sum_congr rfl
  intro i _
  let _ : NeZero (Module.finrank ℝ E) :=
    ⟨Nat.ne_of_gt ((Nat.zero_le i.val).trans_lt i.isLt)⟩
  have h := map_secondCovDeriv_hom_conjugate φ hφ cov (LeviCivita g) A
    ⟨smoothOrthoFrame g x i, smoothOrthoFrame_smooth g x i⟩ x
    (smoothOrthoFrame g x i x)
  simpa only [ContMDiffSection.coeFn_mk, ContinuousLinearMap.comp_apply, sub_apply, map_sub] using
    congrArg (fun L => L w) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.map_rawBundleConnLap_hom_conjugate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.map_rawBundleConnLap_hom_conjugate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.map_rawBundleConnLap_hom_conjugate ``Submission.DifferentialGeometry.Geometry.Connection.map_rawBundleConnLap_hom_conjugate

end DifferentialGeometry.Geometry.Connection
