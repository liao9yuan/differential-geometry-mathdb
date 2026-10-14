import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.Profile
import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Filter _root_.MeasureTheory
open scoped _root_.ENNReal _root_.NNReal _root_.Topology
namespace DifferentialGeometry.Analysis.CutoffProfile
variable {Q ι F : Type*} [MeasurableSpace Q]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem tendsto_integral_evalue_smul
    {μ : _root_.MeasureTheory.Measure Q} {r : Q → ℝ≥0∞} (hr : AEMeasurable r μ)
    (hrfin : ∀ᵐ q ∂μ, r q ≠ ⊤) {f : Q → F} (hf : _root_.MeasureTheory.Integrable f μ)
    {l : Filter ι} [l.IsCountablyGenerated] (a : ι → ℝ≥0) (ha : _root_.Filter.Tendsto a l (𝓝 0)) :
    _root_.Filter.Tendsto (fun i => ∫ q, evalue ((a i : ℝ≥0∞) * r q) • f q ∂μ)
      l (𝓝 (∫ q, f q ∂μ)) := by
  apply _root_.MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun q => ‖f q‖)
  · exact Eventually.of_forall fun i =>
      (continuous_evalue.measurable.comp_aemeasurable (aemeasurable_const.mul hr)).aestronglyMeasurable.smul
        hf.aestronglyMeasurable
  · exact Eventually.of_forall fun i => Eventually.of_forall fun q => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (evalue_mem_Icc _).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (evalue_mem_Icc _).2
  · exact hf.norm
  · filter_upwards [hrfin] with q hq
    have he : _root_.Filter.Tendsto (fun i => (a i : ℝ≥0∞)) l (𝓝 0) :=
      ENNReal.continuous_coe.continuousAt.tendsto.comp ha
    have hm := (ENNReal.continuous_mul_const hq).continuousAt.tendsto.comp he
    have hc := continuous_evalue.continuousAt.tendsto.comp hm
    simpa only [Function.comp_apply, _root_.MulZeroClass.zero_mul, evalue_one_of_le (show (0 : ℝ≥0∞) ≤ 1 from zero_le_one), one_smul]
      using hc.smul_const (f q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.CutoffProfile.tendsto_integral_evalue_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.CutoffProfile.tendsto_integral_evalue_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.CutoffProfile.tendsto_integral_evalue_smul ``Submission.DifferentialGeometry.Analysis.CutoffProfile.tendsto_integral_evalue_smul
end DifferentialGeometry.Analysis.CutoffProfile
