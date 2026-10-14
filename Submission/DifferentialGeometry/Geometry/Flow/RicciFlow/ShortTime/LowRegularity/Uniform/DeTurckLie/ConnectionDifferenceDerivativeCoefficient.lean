import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Kernel.Uniform
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Application.FixedConnectionSecondOrderBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Grid.TameBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }


theorem exists_uniform_deTurckLieConnectionDifferenceDerivativeCoefficient_covariantJetNormSq_one_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ g₀ : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ →
        ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2),
          (∀ (y : M) (v w : TangentSpace I y),
            g₁.inner y v w = g₀.inner y v w +
              ccTensorBilinSymm (I := I) g₀ P y v w) →
          ∀ {δ : ℝ}, δ ≤ δ₀ → 0 ≤ δ →
          gFibreOpBound (I := I) (M := M) g₀
              (ccTensorBilinSymm (I := I) g₀ P) δ →
          ∀ R A : ℝ, 0 ≤ R → 0 ≤ A →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
          ‖iteratedCovGrad (I := I) g₀ 0 2 3 P‖ ≤ A →
          (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M)
                g₀ g₁ gBase)‖ ^ 2) ≤
            (B0 R + B1 R * A) ^ 2 := by
  classical
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨F, hF, hfix⟩ := connFix_grid_uniform
    (I := I) (M := M) gBase hΛ
  obtain ⟨C, hC, hpt⟩ := exists_deTurckLieConnectionDifferenceDerivativeKernel_gridBound_of_connectionDifference
    (I := I) (M := M) hδ₀ F hF
  obtain ⟨B0, B1, hB0, hB1, hint⟩ := h1_grid_uniform
    (I := I) (M := M) hDim gBase hΛ0 C hC
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro g₀ hEq hjet1 hjet2 hjet3 g₁ P htie δ hδ_le hδ_nonneg hbound
    R A hR hA hP htop
  apply hint g₀ hEq hjet1 hjet2 P
    (deTurckLieConnectionDifferenceDerivCoeffField (I := I) (M := M) g₀ g₁ gBase)
    R A hR hA hP htop
  intro i hi x
  simpa only [lowJetGrid, Combinatorics.antidiagonalTupleGrid] using
    hpt g₀ gBase (hfix g₀ hEq hjet1 hjet2 hjet3)
      g₁ P htie hδ_le hδ_nonneg hbound i hi x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_uniform_deTurckLieConnectionDifferenceDerivativeCoefficient_covariantJetNormSq_one_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_uniform_deTurckLieConnectionDifferenceDerivativeCoefficient_covariantJetNormSq_one_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_uniform_deTurckLieConnectionDifferenceDerivativeCoefficient_covariantJetNormSq_one_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.exists_uniform_deTurckLieConnectionDifferenceDerivativeCoefficient_covariantJetNormSq_one_bound

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
