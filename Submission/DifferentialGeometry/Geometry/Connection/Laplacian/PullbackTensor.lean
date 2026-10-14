import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Alternating
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Pullback
import Submission.DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.CovariantDerivative _root_.Submission.CovariantDerivative
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

theorem rawBundleConnLap_multilinear_pullbackFiberwiseLinearEquiv
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : _root_.Bundle.TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))))
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I F₂ V₂) [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] (k : ℕ)
    {T : ∀ x, Bundle.continuousMultilinearMap ℝ k F₂ V₂ x} {x : M}
    (hT : ContMDiffAt I
      (I.prod 𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin k => F₂) ℝ)) 2
      (fun y => (⟨y, T y⟩ : _root_.Bundle.TotalSpace
        (ContinuousMultilinearMap ℝ (fun _ : Fin k => F₂) ℝ)
        (Bundle.continuousMultilinearMap ℝ k F₂ V₂))) x) :
    rawBundleConnLap g
      (multilinear
        (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov) k)
      (fun y => (T y).compContinuousLinearMap (fun _ => (φ y).toContinuousLinearMap)) x =
      (rawBundleConnLap g (multilinear cov k) T x).compContinuousLinearMap
        (fun _ => (φ x).toContinuousLinearMap) := by
  let L := Bundle.continuousMultilinearMap.compContinuousLinearMapL
    (F₁ := F₁) (F₂ := F₂) x (fun _ : Fin k => (φ x).toContinuousLinearMap)
  change _ = L (rawBundleConnLap g (multilinear cov k) T x)
  simp only [rawBundleConnLap_def, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  let _ : NeZero (Module.finrank ℝ E) :=
    ⟨Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
  exact multilinear_secondCovDeriv_pullbackFiberwiseLinearEquiv φ hφ cov (LeviCivita g) k hT
    ((smoothOrthoFrame_smooth g x i).mdifferentiableAt (by simp)) (smoothOrthoFrame g x i x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.rawBundleConnLap_multilinear_pullbackFiberwiseLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.rawBundleConnLap_multilinear_pullbackFiberwiseLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.rawBundleConnLap_multilinear_pullbackFiberwiseLinearEquiv ``Submission.DifferentialGeometry.Geometry.Connection.rawBundleConnLap_multilinear_pullbackFiberwiseLinearEquiv

theorem rawBundleConnLap_alternating_pullbackFiberwiseLinearEquiv
    (φ : ∀ x, V₁ x ≃L[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : _root_.Bundle.TotalSpace (F₁ →L[ℝ] F₂)
        (fun x => V₁ x →L[ℝ] V₂ x))))
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I F₂ V₂) [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] (k : ℕ)
    {T : ∀ x, V₂ x [⋀^Fin k]→L[ℝ] ℝ} {x : M}
    (hT : ContMDiffAt I
      (I.prod 𝓘(ℝ, F₂ [⋀^Fin k]→L[ℝ] ℝ)) 2
      (fun y => (⟨y, T y⟩ : _root_.Bundle.TotalSpace
        (F₂ [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) F₂ V₂ ℝ (Bundle.Trivial M ℝ)))) x) :
    rawBundleConnLap g
      (alternating
        (pullbackFiberwiseLinearEquiv (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map cov) k)
      (fun y => (T y).compContinuousLinearMap (φ y).toContinuousLinearMap) x =
      (rawBundleConnLap g (alternating cov k) T x).compContinuousLinearMap
        (φ x).toContinuousLinearMap := by
  let L := ContinuousAlternatingMap.compContinuousLinearMapCLM
    (F := ℝ) (ι := Fin k) (φ x).toContinuousLinearMap
  change _ = L (rawBundleConnLap g (alternating cov k) T x)
  simp only [rawBundleConnLap_def, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  let _ : NeZero (Module.finrank ℝ E) :=
    ⟨Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
  exact alternating_secondCovDeriv_pullbackFiberwiseLinearEquiv φ hφ cov (LeviCivita g) k hT
    ((smoothOrthoFrame_smooth g x i).mdifferentiableAt (by simp)) (smoothOrthoFrame g x i x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.rawBundleConnLap_alternating_pullbackFiberwiseLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.rawBundleConnLap_alternating_pullbackFiberwiseLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.rawBundleConnLap_alternating_pullbackFiberwiseLinearEquiv ``Submission.DifferentialGeometry.Geometry.Connection.rawBundleConnLap_alternating_pullbackFiberwiseLinearEquiv

end DifferentialGeometry.Geometry.Connection
