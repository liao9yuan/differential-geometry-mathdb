import Submission.DifferentialGeometry.Analysis.Integration.Integral.LocalIntegrabilityTests
import Submission.DifferentialGeometry.Analysis.Convex.DirectionalSecondDerivative
import Submission.DifferentialGeometry.Analysis.Convex.IntegrableDirectionalDistribution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis.Calculus

theorem exists_locallyIntegrableOn_directional_second_derivative_of_concave_sub_quadratic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : _root_.MeasureTheory.Measure E} [Measure.IsAddHaarMeasure μ]
    {f : E → ℝ} {U : Set E} (hU : IsOpen U) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : ConcaveOn ℝ U (fun x => f x - B x x / 2))
    (v : E) (h : ℕ → ℝ) (hh : _root_.Filter.Tendsto h _root_.Filter.atTop (𝓝 0)) (hne : ∀ n, h n ≠ 0) :
    ∃ q : E → ℝ, Measurable q ∧ _root_.MeasureTheory.LocallyIntegrableOn q U μ ∧
      (∀ x, q x = _root_.Filter.limUnder _root_.Filter.atTop (fun n =>
        (U.indicator f (x + h n • v) - 2 * U.indicator f x +
          U.indicator f (x - h n • v)) / (h n) ^ 2)) ∧
      ∀ᵐ x ∂μ, x ∈ U →
        _root_.Filter.Tendsto (fun n => (f (x + h n • v) - 2 * f x + f (x - h n • v)) / (h n) ^ 2)
          atTop (𝓝 (q x)) := by
  obtain ⟨q, hqmeas, hqeq, hqdiff⟩ :=
    exists_measurable_directional_second_derivative_of_concave_sub_quadratic
      (μ := μ) hU B hf v h hh hne
  refine ⟨q, hqmeas, ?_, hqeq, hqdiff⟩
  apply MeasureTheory.locallyIntegrableOn_of_integrable_mul_contDiff (n := 2) hU
  intro φ hφ hφsupp hφU hφnonneg
  exact
    (integrable_mul_and_integral_mul_fderiv_fderiv_le_of_concaveOn_sub_quadratic
    B hf hU hφ hφsupp hφU hφnonneg v h hh hne hqdiff).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.exists_locallyIntegrableOn_directional_second_derivative_of_concave_sub_quadratic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.exists_locallyIntegrableOn_directional_second_derivative_of_concave_sub_quadratic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.exists_locallyIntegrableOn_directional_second_derivative_of_concave_sub_quadratic ``Submission.DifferentialGeometry.Analysis.Calculus.exists_locallyIntegrableOn_directional_second_derivative_of_concave_sub_quadratic

end DifferentialGeometry.Analysis.Calculus
