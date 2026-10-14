import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.LipschitzApproximation
import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.Support
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.LocallyLipschitz.CompactSupport
import Mathlib.Analysis.SpecificLimits.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter _root_.Set
open scoped _root_.NNReal _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem integrable_fderiv_of_lipschitzWith_hasCompactSupport
    {u : E → ℝ} {C : ℝ≥0} (hu : LipschitzWith C u) (huc : HasCompactSupport u) :
    Integrable (fderiv ℝ u) volume := by
  have hbound : _root_.MeasureTheory.Integrable ((tsupport u).indicator (fun _ : E => (C : ℝ))) volume :=
    (_root_.MeasureTheory.integrableOn_const huc.measure_lt_top.ne).integrable_indicator
      (isClosed_tsupport u).measurableSet
  refine hbound.mono' (measurable_fderiv ℝ u).aestronglyMeasurable ?_
  filter_upwards with x
  by_cases hx : x ∈ tsupport u
  · rw [Set.indicator_of_mem hx]
    exact norm_fderiv_le_of_lipschitz ℝ hu
  · rw [Set.indicator_of_notMem hx, fderiv_of_notMem_tsupport ℝ hx, norm_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.integrable_fderiv_of_lipschitzWith_hasCompactSupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.integrable_fderiv_of_lipschitzWith_hasCompactSupport target :: scope.openDecls } }

theorem exists_nonneg_smooth_compactSupport_approx_of_locallyLipschitz
    {u : E → ℝ} (hu : LocallyLipschitz u) (huc : HasCompactSupport u)
    (hunonneg : ∀ x, 0 ≤ u x) {Ω : Set E} (hΩ : IsOpen Ω) (hsupport : tsupport u ⊆ Ω) :
    ∃ K : Set E, IsCompact K ∧ K ⊆ Ω ∧ tsupport u ⊆ K ∧
      _root_.MeasureTheory.Integrable u _root_.MeasureTheory.MeasureSpace.volume ∧ _root_.MeasureTheory.Integrable (fderiv ℝ u) _root_.MeasureTheory.MeasureSpace.volume ∧
      ∃ v : ℕ → E → ℝ,
        (∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n) ∧ tsupport (v n) ⊆ K ∧
          (∀ x, 0 ≤ v n x) ∧ _root_.MeasureTheory.Integrable (v n) _root_.MeasureTheory.MeasureSpace.volume ∧ _root_.MeasureTheory.Integrable (fderiv ℝ (v n)) _root_.MeasureTheory.MeasureSpace.volume) ∧
        _root_.Filter.Tendsto (fun n => ∫ x, ‖v n x - u x‖) _root_.Filter.atTop (𝓝 0) ∧
        Tendsto (fun n => ∫ x, ‖fderiv ℝ (v n) x - fderiv ℝ u x‖) _root_.Filter.atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := Euclidean.exists_lipschitzWith_of_locallyLipschitz_hasCompactSupport hu huc
  obtain ⟨δ, hδ, K, hK, hKΩ, huK, hmollK⟩ :=
    exists_isCompact_tsupport_mollifyEps_subset huc hΩ hsupport
  let ε : ℕ → ℝ := fun n => δ / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hεδ (n : ℕ) : ε n ≤ δ := by
    exact div_le_self hδ.le (by linarith [Nat.cast_nonneg (α := ℝ) n] : 1 ≤ (n : ℝ) + 1)
  have hεlim : _root_.Filter.Tendsto ε _root_.Filter.atTop (𝓝 0) := by
    simpa only [ε, div_eq_mul_inv, one_mul, _root_.MulZeroClass.mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
  let v : ℕ → E → ℝ := fun n => mollifyEps (hε n) u
  have hvK (n : ℕ) : tsupport (v n) ⊆ K := hmollK (ε n) (hε n) (hεδ n)
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top⟩
  refine ⟨K, hK, hKΩ, huK, hu.continuous.integrable_of_hasCompactSupport huc,
    integrable_fderiv_of_lipschitzWith_hasCompactSupport hC huc, v, ?_, ?_, ?_⟩
  · intro n
    have hvsmooth := mollifyEps_contDiff (hε n) hu.continuous.locallyIntegrable
    have hvc := mollifyEps_hasCompactSupport (hε n) huc
    exact ⟨hvsmooth, hvK n, mollifyEps_nonneg (hε n) hunonneg,
      hvsmooth.continuous.integrable_of_hasCompactSupport hvc,
      integrable_fderiv_of_lipschitzWith_hasCompactSupport
        (lipschitzWith_mollifyEps (hε n) hC) hvc⟩
  · have hlim := tendsto_integral_norm_mollifyEps_sub_of_lipschitzWith
      (s := K) hε hεlim hC
    apply hlim.congr
    intro n
    apply _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hux : u x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (huK h))
    have hvx : v n x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hvK n h))
    simp only [v] at hvx
    simp only [hux, hvx, sub_self, norm_zero]
  · have hlim := tendsto_integral_norm_fderiv_mollifyEps_sub_of_lipschitzWith
      (s := K) hε hεlim hC
    apply hlim.congr
    intro n
    apply _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hux := fderiv_of_notMem_tsupport ℝ (fun h => hx (huK h))
    have hvx := fderiv_of_notMem_tsupport ℝ (fun h => hx (hvK n h))
    simp only [v] at hvx
    simp only [hux, hvx, sub_self, norm_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.exists_nonneg_smooth_compactSupport_approx_of_locallyLipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.exists_nonneg_smooth_compactSupport_approx_of_locallyLipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.exists_nonneg_smooth_compactSupport_approx_of_locallyLipschitz ``Submission.DifferentialGeometry.Analysis.Sobolev.exists_nonneg_smooth_compactSupport_approx_of_locallyLipschitz

end DifferentialGeometry.Analysis.Sobolev
