import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Regularization.Integrability

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.MeasureTheory _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis



theorem tendsto_integral_regularizedConformalWeight_comp_of_zero
    {X : Type*} [MeasurableSpace X] {μ : _root_.MeasureTheory.Measure X} {c : X → ℂ} {a f : ℂ → ℝ} {b : X → ℝ}
    (hc : Measurable c) (ha : Measurable a) (hf : Measurable f)
    (han : ∀ᵐ z ∂μ, 0 ≤ a (c z)) (hb : _root_.MeasureTheory.Integrable b μ)
    (hzero : ∀ᵐ z ∂μ, a (c z) = 0 → b z = 0) :
    _root_.Filter.Tendsto (fun ε : ℝ => ∫ z, regularizedConformalWeight a f ε (c z) * b z ∂μ) (𝓝 0)
      (𝓝 (∫ z, b z ∂μ)) := by
  have h := tendsto_integral_regularizedConformalWeight_comp hc ha hf han hb
  have heq : (fun z => if a (c z) = 0 then 0 else b z) =ᵐ[μ] b := by
    filter_upwards [hzero] with z hz
    split_ifs with hza
    · exact (hz hza).symm
    · rfl
  rwa [_root_.MeasureTheory.integral_congr_ae heq] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendsto_integral_regularizedConformalWeight_comp_of_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendsto_integral_regularizedConformalWeight_comp_of_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendsto_integral_regularizedConformalWeight_comp_of_zero ``Submission.DifferentialGeometry.Analysis.tendsto_integral_regularizedConformalWeight_comp_of_zero




theorem tendsto_integral_one_sub_regularizedConformalWeight_comp
    {X : Type*} [MeasurableSpace X] {μ : _root_.MeasureTheory.Measure X} {c : X → ℂ} {a f : ℂ → ℝ} {b : X → ℝ}
    (hc : Measurable c) (ha : Measurable a) (hf : Measurable f)
    (han : ∀ᵐ z ∂μ, 0 ≤ a (c z)) (hb : _root_.MeasureTheory.Integrable b μ)
    (hzero : ∀ᵐ z ∂μ, a (c z) = 0 → b z = 0) :
    _root_.Filter.Tendsto (fun ε : ℝ => ∫ z, (1 - regularizedConformalWeight a f ε (c z)) * b z ∂μ) (𝓝 0)
      (𝓝 0) := by
  have h := tendsto_integral_regularizedConformalWeight_comp_of_zero hc ha hf han hb hzero
  have heq (ε : ℝ) : (∫ z, (1 - regularizedConformalWeight a f ε (c z)) * b z ∂μ) =
      (∫ z, b z ∂μ) - ∫ z, regularizedConformalWeight a f ε (c z) * b z ∂μ := by
    rw [← _root_.MeasureTheory.integral_sub hb (integrable_regularizedConformalWeight_comp_mul hc ha hf han hb ε)]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [] with z
    ring
  simp_rw [heq]
  simpa only [sub_self] using
    (tendsto_const_nhds : _root_.Filter.Tendsto (fun _ : ℝ => ∫ z, b z ∂μ) (𝓝 0) (𝓝 (∫ z, b z ∂μ))).sub h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendsto_integral_one_sub_regularizedConformalWeight_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendsto_integral_one_sub_regularizedConformalWeight_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendsto_integral_one_sub_regularizedConformalWeight_comp ``Submission.DifferentialGeometry.Analysis.tendsto_integral_one_sub_regularizedConformalWeight_comp

end DifferentialGeometry.Analysis
