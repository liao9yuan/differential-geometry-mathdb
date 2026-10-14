import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.MeasureTheory _root_.Filter _root_.Metric _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis.Calculus

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E]

theorem hasDerivWithinAt_integral_of_dominated_loc_of_lip
    {μ : _root_.MeasureTheory.Measure α} {F : 𝕜 → α → E} {F' : α → E} {x₀ : 𝕜} {s t : Set 𝕜}
    {bound : α → ℝ} (hacc : AccPt x₀ (𝓟 t)) (hs : s ∈ 𝓝[t] x₀) (hx : x₀ ∈ s)
    (hF_meas : ∀ᶠ x in 𝓝[t] x₀, _root_.MeasureTheory.AEStronglyMeasurable (F x) μ)
    (hF_int : _root_.MeasureTheory.Integrable (F x₀) μ) (hF'_meas : _root_.MeasureTheory.AEStronglyMeasurable F' μ)
    (h_lip : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs (bound a)) (F · a) s)
    (bound_integrable : _root_.MeasureTheory.Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, HasDerivWithinAt (F · a) (F' a) t x₀) :
    _root_.MeasureTheory.Integrable F' μ ∧
      HasDerivWithinAt (fun x => ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) t x₀ := by
  have : (𝓝[t \ {x₀}] x₀).NeBot := accPt_principal_iff_nhdsWithin.mp hacc
  have hmono : 𝓝[t \ {x₀}] x₀ ≤ 𝓝[t] x₀ := nhdsWithin_mono x₀ _root_.Set.sdiff_subset
  have hF_int' : ∀ᶠ x in 𝓝[t \ {x₀}] x₀, _root_.MeasureTheory.Integrable (F x) μ := by
    filter_upwards [hmono hs, hF_meas.filter_mono hmono] with x hxs hxm
    refine _root_.MeasureTheory.integrable_of_norm_sub_le hxm hF_int
      (bound_integrable.norm.mul_const ‖x - x₀‖) ?_
    filter_upwards [h_lip] with a ha
    simpa only [norm_sub_rev (F x₀ a), Real.norm_eq_abs, Real.coe_nnabs] using ha.norm_sub_le hxs hx
  have h_slope : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖slope (F · a) x₀ x‖ ≤ |bound a| := by
    filter_upwards [h_lip] with a ha x hxs
    rw [slope_def_module, norm_smul, norm_inv]
    calc
      ‖x - x₀‖⁻¹ * ‖F x a - F x₀ a‖ ≤
          ‖x - x₀‖⁻¹ * (|bound a| * ‖x - x₀‖) := by
        gcongr
        exact ha.norm_sub_le hxs hx
      _ ≤ |bound a| := by
        rw [← div_eq_inv_mul]
        exact div_le_of_le_mul₀ (norm_nonneg _) (abs_nonneg _) (le_refl _)
  have hF'_int : _root_.MeasureTheory.Integrable F' μ := by
    refine bound_integrable.norm.mono' hF'_meas ?_
    filter_upwards [h_diff, h_slope] with a ha hd
    apply le_of_tendsto (hasDerivWithinAt_iff_tendsto_slope.mp ha).norm
    filter_upwards [hmono hs] with x hxs
    exact hd x hxs
  refine ⟨hF'_int, ?_⟩
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have heq : (fun x => ∫ a, slope (F · a) x₀ x ∂μ) =ᶠ[𝓝[t \ {x₀}] x₀]
      slope (fun x => ∫ a, F x a ∂μ) x₀ := by
    filter_upwards [hF_int'] with x hxi
    simp only [slope_def_module, _root_.MeasureTheory.integral_smul, _root_.MeasureTheory.integral_sub hxi hF_int]
  refine Filter.Tendsto.congr' heq ?_
  apply _root_.MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun a => |bound a|)
  · filter_upwards [hF_meas.filter_mono hmono] with x hxm
    simp only [slope_def_module]
    exact (hxm.sub hF_int.aestronglyMeasurable).const_smul _
  · filter_upwards [hmono hs] with x hxs
    exact h_slope.mono (fun a ha => ha x hxs)
  · exact bound_integrable.norm
  · exact h_diff.mono (fun a ha => hasDerivWithinAt_iff_tendsto_slope.mp ha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.hasDerivWithinAt_integral_of_dominated_loc_of_lip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.hasDerivWithinAt_integral_of_dominated_loc_of_lip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.hasDerivWithinAt_integral_of_dominated_loc_of_lip ``Submission.DifferentialGeometry.Analysis.Calculus.hasDerivWithinAt_integral_of_dominated_loc_of_lip

theorem hasDerivWithinAt_integral_Icc_of_dominated_loc_of_lip
    {μ : _root_.MeasureTheory.Measure α} {F : ℝ → α → E} {F' : α → E} {x₀ a b : ℝ} {s : Set ℝ}
    {bound : α → ℝ} (hx : x₀ ∈ _root_.Set.Ico a b) (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝[_root_.Set.Icc a b] x₀, _root_.MeasureTheory.AEStronglyMeasurable (F x) μ)
    (hF_int : _root_.MeasureTheory.Integrable (F x₀) μ) (hF'_meas : _root_.MeasureTheory.AEStronglyMeasurable F' μ)
    (h_lip : ∀ᵐ u ∂μ, LipschitzOnWith (Real.nnabs (bound u)) (F · u) (_root_.Set.Icc a b ∩ s))
    (bound_integrable : _root_.MeasureTheory.Integrable bound μ)
    (h_diff : ∀ᵐ u ∂μ, HasDerivWithinAt (F · u) (F' u) (_root_.Set.Icc a b) x₀) :
    _root_.MeasureTheory.Integrable F' μ ∧
      HasDerivWithinAt (fun x => ∫ u, F x u ∂μ) (∫ u, F' u ∂μ) (_root_.Set.Icc a b) x₀ := by
  have hacc : AccPt x₀ (𝓟 (_root_.Set.Icc a b)) := by
    apply accPt_principal_iff_nhdsWithin.mpr
    apply (left_nhdsWithin_Ioc_neBot hx.2).mono
    apply nhdsWithin_mono
    intro y hy
    exact ⟨⟨hx.1.trans hy.1.le, hy.2⟩, by simpa using hy.1.ne'⟩
  exact hasDerivWithinAt_integral_of_dominated_loc_of_lip hacc
    (_root_.Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds hs))
    ⟨⟨hx.1, hx.2.le⟩, mem_of_mem_nhds hs⟩
    hF_meas hF_int hF'_meas h_lip bound_integrable h_diff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.hasDerivWithinAt_integral_Icc_of_dominated_loc_of_lip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.hasDerivWithinAt_integral_Icc_of_dominated_loc_of_lip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.hasDerivWithinAt_integral_Icc_of_dominated_loc_of_lip ``Submission.DifferentialGeometry.Analysis.Calculus.hasDerivWithinAt_integral_Icc_of_dominated_loc_of_lip

end DifferentialGeometry.Analysis.Calculus
