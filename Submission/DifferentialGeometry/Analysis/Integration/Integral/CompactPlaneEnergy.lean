import Submission.DifferentialGeometry.Analysis.Integration.Lp.QuadraticDomination
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.LocallyIntegrable

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.NNReal _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [SecondCountableTopology F]

private theorem memLp_fderiv_apply_of_lipschitz_of_isCompact
    {q : ℂ → F} {L : ℝ≥0} (hq : LipschitzWith L q)
    {s : Set ℂ} (hs : IsCompact s) (w : ℂ) :
    MemLp (fun z => fderiv ℝ q z w) 2 (volume.restrict s) := by
  borelize F
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hs.measure_ne_top
  apply MemLp.of_bound (measurable_fderiv_apply_const ℝ q w).aestronglyMeasurable
    ((L : ℝ) * ‖w‖)
  exact Eventually.of_forall fun z =>
    ((fderiv ℝ q z).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hq) (norm_nonneg w))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.memLp_fderiv_apply_of_lipschitz_of_isCompact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.memLp_fderiv_apply_of_lipschitz_of_isCompact target :: scope.openDecls } }

theorem exists_uniform_integral_plane_quadratic_bound_of_isCompact
    {K : Set F} (hK : IsCompact K) (A : F → F →L[ℝ] F →L[ℝ] ℝ)
    (hA : ContinuousOn A K) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ (∀ y ∈ K, ‖A y‖ ≤ Λ) ∧
      ∀ (q : ℂ → F) (L : ℝ≥0), LipschitzWith L q →
      ∀ (s : Set ℂ), IsCompact s → _root_.Set.MapsTo q s K →
        _root_.MeasureTheory.IntegrableOn (fun z =>
          (A (q z) (fderiv ℝ q z 1) (fderiv ℝ q z 1) +
            A (q z) (fderiv ℝ q z Complex.I) (fderiv ℝ q z Complex.I)) / 2) s ∧
        _root_.MeasureTheory.IntegrableOn (fun z =>
          (‖fderiv ℝ q z 1‖ ^ 2 + ‖fderiv ℝ q z Complex.I‖ ^ 2) / 2) s ∧
        |∫ z in s,
          (A (q z) (fderiv ℝ q z 1) (fderiv ℝ q z 1) +
            A (q z) (fderiv ℝ q z Complex.I) (fderiv ℝ q z Complex.I)) / 2| ≤
          Λ * ∫ z in s, (‖fderiv ℝ q z 1‖ ^ 2 + ‖fderiv ℝ q z Complex.I‖ ^ 2) / 2 := by
  have hnorm : ContinuousOn (fun y => ‖A y‖) K :=
    (@continuous_norm (F →L[ℝ] F →L[ℝ] ℝ) inferInstance).comp_continuousOn hA
  obtain ⟨R, hR⟩ := (hK.image_of_continuousOn hnorm).bddAbove
  let Λ := _root_.Max.max 0 R
  have hAK : ∀ y ∈ K, ‖A y‖ ≤ Λ := fun y hy =>
    (hR (_root_.Set.mem_image_of_mem (fun y => ‖A y‖) hy)).trans (le_max_right 0 R)
  refine ⟨Λ, le_max_left 0 R, hAK, ?_⟩
  intro q L hq s hs hqK
  have ha := memLp_fderiv_apply_of_lipschitz_of_isCompact hq hs (1 : ℂ)
  have hb := memLp_fderiv_apply_of_lipschitz_of_isCompact hq hs Complex.I
  have hcomp : ContinuousOn (fun z => A (q z)) s :=
    hA.comp hq.continuous.continuousOn hqK
  have hmeas (v w : F) :
      AEStronglyMeasurable (fun z => A (q z) v w) (volume.restrict s) :=
    ((hcomp.clm_apply continuousOn_const).clm_apply continuousOn_const).integrableOn_compact hs
      |>.aestronglyMeasurable
  have hbound : ∀ᵐ z ∂volume.restrict s, ‖A (q z)‖ ≤ Λ := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hs.measurableSet] with z hz
    exact hAK (q z) (hqK hz)
  have hia := integrable_bilinear_of_apply_aestronglyMeasurable
    (fun z => A (q z)) hmeas hbound ha ha
  have hib := integrable_bilinear_of_apply_aestronglyMeasurable
    (fun z => A (q z)) hmeas hbound hb hb
  have hsa := (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).mp ha
  have hsb := (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).mp hb
  refine ⟨(hia.add hib).div_const 2, (hsa.add hsb).div_const 2, ?_⟩
  simpa only [Real.norm_eq_abs] using
    norm_integral_quadratic_add_div_two_le (fun z => A (q z)) hmeas hbound ha hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_uniform_integral_plane_quadratic_bound_of_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_uniform_integral_plane_quadratic_bound_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_uniform_integral_plane_quadratic_bound_of_isCompact ``Submission.DifferentialGeometry.Analysis.exists_uniform_integral_plane_quadratic_bound_of_isCompact

end DifferentialGeometry.Analysis

end
