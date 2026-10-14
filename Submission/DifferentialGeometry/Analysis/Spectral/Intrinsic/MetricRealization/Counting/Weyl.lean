import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Spectrum.TailSummability

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral
namespace MetricRealization

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

def EigenvalueCountingBound (g : SmoothRiemannianMetric I M) (r s : ℕ) : Prop :=
  ∃ (q : ℕ) (A : ℝ), 0 ≤ A ∧
    ∃ count : ℝ → Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s),
      (∀ (Λ : ℝ) (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s),
        1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ → i ∈ count Λ) ∧
      (∀ Λ : ℝ, ((count Λ).card : ℝ) ≤ A * Λ ^ q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.EigenvalueCountingBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.EigenvalueCountingBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.EigenvalueCountingBound ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.EigenvalueCountingBound

omit [NeZero (Module.finrank ℝ E)] in
theorem eigenvalueTailSummable_of_countingBound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h : EigenvalueCountingBound (I := I) (M := M) g r s) :
    EigenvalueTailSummable (I := I) (M := M) g r s := by
  obtain ⟨q, A, hA, count, hcount_mem, hcount_card⟩ := h
  refine eigenvalueTailSummable_of_polynomial_counting_bound (I := I) (M := M) g r s q A hA
    (fun n => count ((2 : ℝ) ^ (n + 1))) ?_ ?_
  · intro n i hi
    exact hcount_mem ((2 : ℝ) ^ (n + 1)) i hi
  · intro n
    refine (hcount_card ((2 : ℝ) ^ (n + 1))).trans (le_of_eq ?_)
    congr 1
    rw [← pow_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenvalueTailSummable_of_countingBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenvalueTailSummable_of_countingBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenvalueTailSummable_of_countingBound ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenvalueTailSummable_of_countingBound

theorem spectralChartRegularity_of_countingBound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h : EigenvalueCountingBound (I := I) (M := M) g r s) :
    SpectralChartRegularity (I := I) (M := M) g r s :=
  spectralChartRegularity_of_eigenvalueTailSummable (I := I) (M := M) g r s
    (eigenvalueTailSummable_of_countingBound (I := I) (M := M) g r s h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralChartRegularity_of_countingBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralChartRegularity_of_countingBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralChartRegularity_of_countingBound ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralChartRegularity_of_countingBound

theorem spectralSmoothRealizesAsSmooth_of_countingBound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h : EigenvalueCountingBound (I := I) (M := M) g r s) :
    SpectralSmoothRealizesAsSmooth (I := I) (M := M) g r s :=
  spectralSmoothRealizesAsSmooth_of_eigenvalueTailSummable (I := I) (M := M) g r s
    (eigenvalueTailSummable_of_countingBound (I := I) (M := M) g r s h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralSmoothRealizesAsSmooth_of_countingBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralSmoothRealizesAsSmooth_of_countingBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralSmoothRealizesAsSmooth_of_countingBound ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralSmoothRealizesAsSmooth_of_countingBound

end MetricRealization
end Spectral
end Analysis
end DifferentialGeometry

end
