import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Set

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.MeasureTheory
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis



theorem exists_smooth_nonneg_density
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : _root_.MeasureTheory.Measure E}
    [_root_.MeasureTheory.IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {s : Set E} (hs : IsOpen s) (hne : s.Nonempty) {mass : ℝ} (hmass : 0 < mass) :
    ∃ κ : E → ℝ, ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧ tsupport κ ⊆ s ∧
      (∀ z, 0 ≤ κ z) ∧ (∫ z, κ z ∂μ) = mass := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨f, hfs, hfc, hf, hrange, hfx⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (hs.mem_nhds hx)
  have hn (z : E) : 0 ≤ f z := (hrange (_root_.Set.mem_range_self z)).1
  have hpos : 0 < ∫ z, f z ∂μ :=
    hf.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hn (by rw [hfx]; norm_num)
  refine ⟨fun z => (mass / ∫ z, f z ∂μ) * f z,
    contDiff_const.mul hf, hfc.mul_left, tsupport_mul_subset_right.trans hfs,
    fun z => mul_nonneg (div_nonneg hmass.le hpos.le) (hn z), ?_⟩
  rw [_root_.MeasureTheory.integral_const_mul]
  exact div_mul_cancel₀ mass hpos.ne'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_smooth_nonneg_density then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_smooth_nonneg_density"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_smooth_nonneg_density ``Submission.DifferentialGeometry.Analysis.exists_smooth_nonneg_density

end DifferentialGeometry.Analysis
