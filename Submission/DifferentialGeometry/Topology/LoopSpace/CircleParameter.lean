import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Real.Pi.Bounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Analysis

theorem exists_circle_parameter_eq_of_mem_sphere {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ _root_.Metric.sphere (0 : ℂ) R) :
    ∃ t ∈ _root_.Set.Icc (0 : ℝ) 1, circleMap 0 R (2 * Real.pi * t - Real.pi) = z := by
  have hmem : z ∈ _root_.Set.range (circleMap 0 R) := by
    rw [range_circleMap]
    simpa only [abs_of_pos hR] using hz
  rw [← (periodic_circleMap 0 R).image_Ioc Real.two_pi_pos (-Real.pi)] at hmem
  obtain ⟨θ, hθ, hθz⟩ := hmem
  refine ⟨(θ + Real.pi) / (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
  · exact div_nonneg (by linarith [hθ.1]) (by positivity)
  · exact (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr (by linarith [hθ.2])
  · have heq : 2 * Real.pi * ((θ + Real.pi) / (2 * Real.pi)) - Real.pi = θ := by
      field_simp
      ring
    rwa [heq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_circle_parameter_eq_of_mem_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_circle_parameter_eq_of_mem_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_circle_parameter_eq_of_mem_sphere ``Submission.DifferentialGeometry.Analysis.exists_circle_parameter_eq_of_mem_sphere

end DifferentialGeometry.Analysis

end

end
