import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Regularization.Limit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.MeasureTheory _root_.Filter

namespace DifferentialGeometry.Analysis



theorem integrable_regularizedConformalWeight_comp_mul
    {X : Type*} [MeasurableSpace X] {μ : _root_.MeasureTheory.Measure X} {c : X → ℂ} {a f : ℂ → ℝ} {b : X → ℝ}
    (hc : Measurable c) (ha : Measurable a) (hf : Measurable f)
    (han : ∀ᵐ z ∂μ, 0 ≤ a (c z)) (hb : _root_.MeasureTheory.Integrable b μ) (ε : ℝ) :
    Integrable (fun z => regularizedConformalWeight a f ε (c z) * b z) μ := by
  have hw : Measurable (regularizedConformalWeight a f ε) :=
    ha.div (ha.add (measurable_const.mul ((measurable_const.mul hf).exp)))
  apply hb.norm.mono' ((hw.comp hc).aestronglyMeasurable.mul hb.aestronglyMeasurable)
  filter_upwards [han] with z hz
  have hbound := regularizedConformalWeight_mem_Icc_all (f := f) hz ε
  change ‖regularizedConformalWeight a f ε (c z) * b z‖ ≤ ‖b z‖
  rw [norm_mul, Real.norm_of_nonneg hbound.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hbound.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integrable_regularizedConformalWeight_comp_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integrable_regularizedConformalWeight_comp_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integrable_regularizedConformalWeight_comp_mul ``Submission.DifferentialGeometry.Analysis.integrable_regularizedConformalWeight_comp_mul

end DifferentialGeometry.Analysis
