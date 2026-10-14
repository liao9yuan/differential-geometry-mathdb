import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalCometric.CoefficientBounds
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Application.SecondCovariantDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck
open _root_.Submission.DifferentialGeometry.Analysis.Spectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

noncomputable def principalCometricOperatorH2
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    TensorHs (I := I) (M := M) g₀ 0 2 (4 : ℝ) →L[ℝ]
      TensorHs (I := I) (M := M) g₀ 0 2 (2 : ℝ) :=
  secondCovariantDerivativeApplication (I := I) (M := M) g₀ 2 2
    (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.principalCometricOperatorH2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.principalCometricOperatorH2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.principalCometricOperatorH2 ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.principalCometricOperatorH2

theorem principalCometricOperatorH2_norm_bound
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g₀ 0 2) (g₁ : SmoothRiemannianMetric I M),
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ ≤ ρ →
        (∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ T y v w) →
        ‖principalCometricOperatorH2 (I := I) (M := M) g₀ g₁‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖ := by
  obtain ⟨ρ, Ccoeff, hρ, hCcoeff, hcoeff⟩ :=
    exists_deTurckPrincipalCometricCoefficient_secondOrder_bound (I := I) (M := M) hDim g₀
  obtain ⟨Capp, hCapp, happ⟩ :=
    secondCovariantDerivativeApplication_norm (I := I) (M := M) hDim g₀ 2 2
  refine ⟨ρ, Capp * Ccoeff, hρ, mul_nonneg hCapp hCcoeff, ?_⟩
  intro T g₁ hT htie
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T‖
  let A : ℝ := Ccoeff * N
  have hN : 0 ≤ N := norm_nonneg _
  have hA : 0 ≤ A := mul_nonneg hCcoeff hN
  obtain ⟨_, hjet⟩ := hcoeff T g₁ (by simpa only [N] using hT) htie
  have hbound := happ
    (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)
    A hA (by simpa only [A, N] using hjet)
  simpa only [principalCometricOperatorH2, A, N, mul_assoc] using hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.principalCometricOperatorH2_norm_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.principalCometricOperatorH2_norm_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.principalCometricOperatorH2_norm_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.principalCometricOperatorH2_norm_bound

theorem principalCometricOperatorH2_apply_smoothCore
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (U : SmoothCcTensor g₀ 0 2) :
    principalCometricOperatorH2 (I := I) (M := M) g₀ g₁
        (ccTensorToHs (I := I) (M := M) g₀ 2 (4 : ℝ) U) =
      ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
        (deTurckPrincipalCometricTerm (I := I) (M := M) g₀ g₁ U) := by
  simpa only [principalCometricOperatorH2, deTurckPrincipalCometricTerm] using
    secondCovariantDerivativeApplication_ccTensorToHs (I := I) (M := M) hDim g₀ 2 2
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁) U

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.principalCometricOperatorH2_apply_smoothCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.principalCometricOperatorH2_apply_smoothCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.principalCometricOperatorH2_apply_smoothCore ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.principalCometricOperatorH2_apply_smoothCore

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
