import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.ContractionJetTower
import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.InverseCometricMultiplier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.TensorRSNabla
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
  (metricCauchySchwarzBound)

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

def inverseMetricDifferenceSlotCoefficient (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M => TensorRSSpace.ofCLM (metricComparisonDifferenceSlotEndo (I := I) g₀ g₁ x)
      contMDiff_toFun := gInvDiffSlotEndo_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.inverseMetricDifferenceSlotCoefficient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.inverseMetricDifferenceSlotCoefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.inverseMetricDifferenceSlotCoefficient ``Submission.DifferentialGeometry.Analysis.Spectral.inverseMetricDifferenceSlotCoefficient

def inverseMetricDifferenceCoefficientFamily (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∀ r : ℕ, SmoothCcTensor g₀ (r + 0) (r + 0) :=
  fun r => match r with
    | 2 => inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁
    | _ => 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.inverseMetricDifferenceCoefficientFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.inverseMetricDifferenceCoefficientFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.inverseMetricDifferenceCoefficientFamily ``Submission.DifferentialGeometry.Analysis.Spectral.inverseMetricDifferenceCoefficientFamily

end NormedSpaceModel

section InnerProductSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem inverseMetricDifferenceCoefficientFamily_iteratedCovGrad_singleSum_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (x₀ : M) (W : SmoothCcTensor g₀ 0 2) (a : ℕ) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x₀
        ((iteratedCovGrad g₀ 0 2 a
          ((fixedCoeffDiffOp (I := I) (M := M) g₀
            (inverseMetricDifferenceCoefficientFamily (I := I) g₀ g₁)).op 0 2 W)).toSection x₀) ≤
      ((4 : ℝ) ^ a * gridWindowSum
          (fixedCoeffDiffOp (I := I) (M := M) g₀
            (inverseMetricDifferenceCoefficientFamily (I := I) g₀ g₁)).kappa 0 2 a) *
        ∑ q ∈ Finset.range (a + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x₀
            ((iteratedCovGrad g₀ 0 2 q W).toSection x₀) :=
  fixedCoeffDiffOp_iteratedCovGrad_singleSum_le (I := I) (M := M) g₀
    (inverseMetricDifferenceCoefficientFamily (I := I) g₀ g₁) x₀ 2 W a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.inverseMetricDifferenceCoefficientFamily_iteratedCovGrad_singleSum_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.inverseMetricDifferenceCoefficientFamily_iteratedCovGrad_singleSum_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.inverseMetricDifferenceCoefficientFamily_iteratedCovGrad_singleSum_le ``Submission.DifferentialGeometry.Analysis.Spectral.inverseMetricDifferenceCoefficientFamily_iteratedCovGrad_singleSum_le

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem covGrad_inverseMetricDifferenceSlotCoefficient_toSection_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (covGrad (I := I) (M := M) g₀ 2 2 (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁)).toSection x =
      covGradBundleEquiv (I := I) (M := M) 2 2 x
        (tensorRSCovariantDerivative I M 2 2 (LeviCivita (I := I) g₀)
          (fun y : M => (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁).toSection y) x) :=
  covGrad_toSection_apply (I := I) (M := M) g₀ 2 2 (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.covGrad_inverseMetricDifferenceSlotCoefficient_toSection_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.covGrad_inverseMetricDifferenceSlotCoefficient_toSection_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.covGrad_inverseMetricDifferenceSlotCoefficient_toSection_eq ``Submission.DifferentialGeometry.Analysis.Spectral.covGrad_inverseMetricDifferenceSlotCoefficient_toSection_eq

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem covGrad_inverseMetricDifferenceSlotCoefficient_leibniz
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (w : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, (fun x : M => Tensor0SSpace 2 I x)⟯)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorCovDerivAt (I := I) (M := M) g₀ 2 2
          (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁) x
            (tangentSpaceModelContinuousLinearEquiv (I := I) x v)) (w x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
        (fun y => metricComparisonDifferenceSlotEndo (I := I) g₀ g₁ y (w y)) x v -
      metricComparisonDifferenceSlotEndo (I := I) g₀ g₁ x
        (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀) w x v) := by
  rw [tensorCovDerivAt_def, ContinuousLinearEquiv.symm_apply_apply]
  exact tensorRSCovariantDerivative_apply I M 2 2 (LeviCivita (I := I) g₀)
    (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁).toSection w x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.covGrad_inverseMetricDifferenceSlotCoefficient_leibniz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.covGrad_inverseMetricDifferenceSlotCoefficient_leibniz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.covGrad_inverseMetricDifferenceSlotCoefficient_leibniz ``Submission.DifferentialGeometry.Analysis.Spectral.covGrad_inverseMetricDifferenceSlotCoefficient_leibniz

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem covGrad_inverseMetricDifferenceSlotCoefficient_leibniz_value
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace 2 I x) :
    ∃ w : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, (fun x : M => Tensor0SSpace 2 I x)⟯,
      w x = D ∧
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          tensorCovDerivAt (I := I) (M := M) g₀ 2 2
            (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁) x
              (tangentSpaceModelContinuousLinearEquiv (I := I) x v)) D =
        Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀)
          (fun y => metricComparisonDifferenceSlotEndo (I := I) g₀ g₁ y (w y)) x v -
        metricComparisonDifferenceSlotEndo (I := I) g₀ g₁ x
          (Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g₀) w x v) := by
  obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 2 ℝ E) (V := fun y : M => Tensor0SSpace 2 I y)
    (n := (⊤ : ℕ∞)) x D
  refine ⟨w, hw, ?_⟩
  rw [← hw, tensorCovDerivAt_def, ContinuousLinearEquiv.symm_apply_apply]
  exact tensorRSCovariantDerivative_apply I M 2 2 (LeviCivita (I := I) g₀)
    (inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁).toSection w x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.covGrad_inverseMetricDifferenceSlotCoefficient_leibniz_value then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.covGrad_inverseMetricDifferenceSlotCoefficient_leibniz_value"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.covGrad_inverseMetricDifferenceSlotCoefficient_leibniz_value ``Submission.DifferentialGeometry.Analysis.Spectral.covGrad_inverseMetricDifferenceSlotCoefficient_leibniz_value

end InnerProductSpaceModel

end Spectral
end Analysis
end DifferentialGeometry

end
