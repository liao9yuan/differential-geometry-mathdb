import Submission.DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.MeanValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Filter
open scoped _root_.Topology _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

private theorem lipschitz_circle_parameter :
    LipschitzWith ⟨2 * Real.pi, by positivity⟩
      (fun t : ℝ => circleMap 0 1 (2 * Real.pi * t - Real.pi)) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => circleMap 0 1 (2 * Real.pi * t - Real.pi))
      ((2 * Real.pi) • (circleMap 0 1 (2 * Real.pi * t - Real.pi) * Complex.I)) t := by
    have hθ : HasDerivAt (fun t : ℝ => 2 * Real.pi * t - Real.pi) (2 * Real.pi) t := by
      simpa using ((hasDerivAt_id t).const_mul (2 * Real.pi)).sub_const Real.pi
    exact (hasDerivAt_circleMap 0 1 (2 * Real.pi * t - Real.pi)).scomp t hθ
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hd t).differentiableAt)
  intro t
  change ‖deriv (fun t : ℝ => circleMap 0 1 (2 * Real.pi * t - Real.pi)) t‖ ≤ _
  rw [(hd t).deriv]
  simp [abs_of_pos Real.pi_pos]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.lipschitz_circle_parameter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.lipschitz_circle_parameter target :: scope.openDecls } }

private theorem norm_sub_start_sq_le_integral_deriv_sq
    {b : ℝ → F} {C : ℝ≥0} (hb : LipschitzWith C b)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) :
    ‖b t - b 0‖ ^ 2 ≤ ∫ s in _root_.Set.Icc (0 : ℝ) 1, ‖deriv b s‖ ^ 2 := by
  let μ : _root_.MeasureTheory.Measure ℝ := volume.restrict (_root_.Set.Icc (0 : ℝ) 1)
  have hdb : _root_.MeasureTheory.MemLp (deriv b) 2 μ := MemLp.of_bound (aestronglyMeasurable_deriv b _) C
    (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hb)
  have hdi : _root_.MeasureTheory.Integrable (fun s => ‖deriv b s‖) μ := hdb.norm.integrable (by norm_num)
  have hac : AbsolutelyContinuousOnInterval b 0 t :=
    hb.lipschitzOnWith.absolutelyContinuousOnInterval
  have hnorm : ‖b t - b 0‖ ≤ ∫ s, ‖deriv b s‖ ∂μ := by
    rw [← hac.integral_deriv_eq_sub_vector]
    calc
      _ ≤ ∫ s in _root_.Set.uIoc (0 : ℝ) t, ‖deriv b s‖ :=
        intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ s, ‖deriv b s‖ ∂μ := by
        exact _root_.MeasureTheory.setIntegral_mono_set hdi
          (Eventually.of_forall fun _ => norm_nonneg _) (by
            apply Eventually.of_forall
            intro s hs
            rw [_root_.Set.uIoc_of_le ht.1] at hs
            exact ⟨hs.1.le, hs.2.trans ht.2⟩)
  have hholder : (∫ s, ‖deriv b s‖ ∂μ) ≤
      Real.sqrt (∫ s, ‖deriv b s‖ ^ 2 ∂μ) := by
    have h := _root_.MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
      (f := fun _ : ℝ => (1 : ℝ)) (g := fun s => ‖deriv b s‖)
      (by simpa using (_root_.MeasureTheory.memLp_const (p := 2) (μ := μ) (1 : ℝ)))
      (by simpa using hdb.norm)
    simpa only [_root_.NormOneClass.norm_one, norm_norm, one_mul, one_pow, _root_.MeasureTheory.integral_const, Measure.real, μ,
      Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
      ENNReal.toReal_one, smul_eq_mul, Real.one_rpow, Real.rpow_two,
      ← Real.sqrt_eq_rpow, Real.sqrt_one] using h
  have hnonneg : 0 ≤ ∫ s, ‖deriv b s‖ ^ 2 ∂μ := _root_.MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  calc
    ‖b t - b 0‖ ^ 2 ≤ (Real.sqrt (∫ s, ‖deriv b s‖ ^ 2 ∂μ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans hholder) 2
    _ = _ := Real.sq_sqrt hnonneg

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.norm_sub_start_sq_le_integral_deriv_sq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.norm_sub_start_sq_le_integral_deriv_sq target :: scope.openDecls } }

private theorem integral_norm_sub_start_sq_le_integral_deriv_sq
    {b : ℝ → F} {C : ℝ≥0} (hb : LipschitzWith C b) :
    (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖b t - b 0‖ ^ 2) ≤
      ∫ s in _root_.Set.Icc (0 : ℝ) 1, ‖deriv b s‖ ^ 2 := by
  have hv : _root_.MeasureTheory.IntegrableOn (fun t => ‖b t - b 0‖ ^ 2) (_root_.Set.Icc (0 : ℝ) 1) :=
    ((hb.continuous.sub continuous_const).norm.pow 2).integrableOn_Icc
  have h := _root_.MeasureTheory.setIntegral_mono_on hv
    (_root_.MeasureTheory.integrableOn_const (by simp : volume (Icc (0 : ℝ) 1) ≠ ∞)) measurableSet_Icc
    (fun t ht => norm_sub_start_sq_le_integral_deriv_sq hb ht)
  simpa only [_root_.MeasureTheory.setIntegral_const, Measure.real, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one, ENNReal.toReal_one, one_smul] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.integral_norm_sub_start_sq_le_integral_deriv_sq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.integral_norm_sub_start_sq_le_integral_deriv_sq target :: scope.openDecls } }

private theorem exists_unit_circle_parameter {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ t ∈ _root_.Set.Icc (0 : ℝ) 1, circleMap 0 1 (2 * Real.pi * t - Real.pi) = z := by
  have hmem : z ∈ _root_.Set.range (circleMap 0 1) := by
    rw [range_circleMap, Metric.mem_sphere, dist_zero_right]
    simpa using hz
  rw [← (periodic_circleMap 0 1).image_Ioc Real.two_pi_pos (-Real.pi)] at hmem
  obtain ⟨θ, hθ, hθz⟩ := hmem
  refine ⟨(θ + Real.pi) / (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
  · exact div_nonneg (by linarith [hθ.1]) (by positivity)
  · exact (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr (by linarith [hθ.2])
  · have heq : 2 * Real.pi * ((θ + Real.pi) / (2 * Real.pi)) - Real.pi = θ := by
      field_simp
      ring
    rwa [heq]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.exists_unit_circle_parameter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.exists_unit_circle_parameter target :: scope.openDecls } }

theorem norm_sq_le_boundary_energy_of_circle_anchor
    {u : ℂ → F} {C : ℝ≥0} (hu : LipschitzWith C u) (p : F)
    (hanchor : u (circleMap 0 1 (-Real.pi)) = p)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖u z - p‖ ^ 2 ≤ ∫ t in _root_.Set.Icc (0 : ℝ) 1,
      ‖deriv (fun s => u (circleMap 0 1 (2 * Real.pi * s - Real.pi))) t‖ ^ 2 := by
  let b : ℝ → F := fun t => u (circleMap 0 1 (2 * Real.pi * t - Real.pi))
  have hb : LipschitzWith (C * ⟨2 * Real.pi, by positivity⟩) b :=
    hu.comp lipschitz_circle_parameter
  have hb0 : b 0 = p := by simpa only [b, _root_.MulZeroClass.mul_zero, zero_sub] using hanchor
  obtain ⟨t, ht, htz⟩ := exists_unit_circle_parameter hz
  have he := norm_sub_start_sq_le_integral_deriv_sq hb ht
  rw [hb0] at he
  simpa only [b, htz] using he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.norm_sq_le_boundary_energy_of_circle_anchor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.norm_sq_le_boundary_energy_of_circle_anchor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.norm_sq_le_boundary_energy_of_circle_anchor ``Submission.DifferentialGeometry.Analysis.norm_sq_le_boundary_energy_of_circle_anchor

theorem integral_norm_sq_le_boundary_energy_of_circle_anchor
    {u : ℂ → F} {C : ℝ≥0} (hu : LipschitzWith C u) (p : F)
    (hanchor : u (circleMap 0 1 (-Real.pi)) = p) :
    (∫ t in _root_.Set.Icc (0 : ℝ) 1,
      ‖u (circleMap 0 1 (2 * Real.pi * t - Real.pi)) - p‖ ^ 2) ≤
      ∫ t in _root_.Set.Icc (0 : ℝ) 1,
        ‖deriv (fun s => u (circleMap 0 1 (2 * Real.pi * s - Real.pi))) t‖ ^ 2 := by
  let b : ℝ → F := fun t => u (circleMap 0 1 (2 * Real.pi * t - Real.pi))
  have hb : LipschitzWith (C * ⟨2 * Real.pi, by positivity⟩) b :=
    hu.comp lipschitz_circle_parameter
  have hb0 : b 0 = p := by simpa only [b, _root_.MulZeroClass.mul_zero, zero_sub] using hanchor
  have he := integral_norm_sub_start_sq_le_integral_deriv_sq hb
  rw [hb0] at he
  exact he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_norm_sq_le_boundary_energy_of_circle_anchor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_norm_sq_le_boundary_energy_of_circle_anchor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_norm_sq_le_boundary_energy_of_circle_anchor ``Submission.DifferentialGeometry.Analysis.integral_norm_sq_le_boundary_energy_of_circle_anchor

end DifferentialGeometry.Analysis

end

end
