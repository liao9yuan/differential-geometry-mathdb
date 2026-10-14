import Submission.DifferentialGeometry.Geometry.Operator.Gradient.ChartPairing
import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.LocallyLipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open _root_.Filter _root_.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {μ : Measure ℝ} [Measure.IsAddHaarMeasure μ]
  {ν : Measure E} [Measure.IsAddHaarMeasure ν]

theorem ae_chartGradientBilin_fderiv_eq_inner_gradientFun_family
    (g : ℝ → SmoothRiemannianMetric I M) (α : M)
    {f : ℝ → M → ℝ} {h : ℝ → M → ℝ} {S : Set ℝ} {W : Set E}
    (hS : IsOpen S) (hW : IsOpen W) (hWt : W ⊆ (extChartAt I α).target)
    (hf : LocallyLipschitzOn (S ×ˢ W)
      (fun z : ℝ × E => f z.1 ((extChartAt I α).symm z.2)))
    (hh : LocallyLipschitzOn (S ×ˢ W)
      (fun z : ℝ × E => h z.1 ((extChartAt I α).symm z.2))) :
    ∀ᵐ z ∂μ.prod ν, z ∈ S ×ˢ W →
      chartGradientBilin (g z.1) α ((extChartAt I α).symm z.2)
        (fderiv ℝ (fun y : E => f z.1 ((extChartAt I α).symm y)) z.2)
        (fderiv ℝ (fun y : E => h z.1 ((extChartAt I α).symm y)) z.2) =
      (g z.1).inner ((extChartAt I α).symm z.2)
        (gradientFun (g z.1) (f z.1) ((extChartAt I α).symm z.2))
        (gradientFun (g z.1) (h z.1) ((extChartAt I α).symm z.2)) := by
  have hdiff := hf.ae_differentiableAt_of_isOpen (μ := μ.prod ν) (hS.prod hW)
  have htest := hh.ae_differentiableAt_of_isOpen (μ := μ.prod ν) (hS.prod hW)
  filter_upwards [hdiff, htest] with z hfz hhz hz
  have hzt : z.2 ∈ (extChartAt I α).target := hWt hz.2
  have hzs : (extChartAt I α).symm z.2 ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target hzt
  have hd : DifferentiableAt ℝ
      (fun v : ℝ × E => f v.1 ((extChartAt I α).symm v.2)) z := hfz hz
  have hfspatial := hd.comp z.2
    (show DifferentiableAt ℝ (fun y : E => (z.1, y)) z.2 from
      (differentiableAt_const z.1).prodMk differentiableAt_id)
  have hfm : MDifferentiableAt I 𝓘(ℝ, ℝ) (f z.1) ((extChartAt I α).symm z.2) := by
    rw [mdifferentiableAt_iff_source_of_mem_source hzs,
      mdifferentiableWithinAt_iff_differentiableWithinAt, (extChartAt I α).right_inv hzt]
    exact hfspatial.differentiableWithinAt
  have hdψ : DifferentiableAt ℝ
      (fun v : ℝ × E => h v.1 ((extChartAt I α).symm v.2)) z := hhz hz
  have hψspatial := hdψ.comp z.2
    (show DifferentiableAt ℝ (fun y : E => (z.1, y)) z.2 from
      (differentiableAt_const z.1).prodMk differentiableAt_id)
  have hhm : MDifferentiableAt I 𝓘(ℝ, ℝ) (h z.1) ((extChartAt I α).symm z.2) := by
    rw [mdifferentiableAt_iff_source_of_mem_source hzs,
      mdifferentiableWithinAt_iff_differentiableWithinAt, (extChartAt I α).right_inv hzt]
    exact hψspatial.differentiableWithinAt
  have hid := (inner_gradientFun_eq_chartGradientBilin (g z.1) α hfm hhm hzs).symm
  rw [(extChartAt I α).right_inv hzt] at hid
  exact hid

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.ae_chartGradientBilin_fderiv_eq_inner_gradientFun_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.ae_chartGradientBilin_fderiv_eq_inner_gradientFun_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.ae_chartGradientBilin_fderiv_eq_inner_gradientFun_family ``Submission.DifferentialGeometry.Geometry.Operator.ae_chartGradientBilin_fderiv_eq_inner_gradientFun_family

end DifferentialGeometry.Geometry.Operator
