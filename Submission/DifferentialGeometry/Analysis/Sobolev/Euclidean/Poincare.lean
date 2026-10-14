import Submission.DifferentialGeometry.External.DeGiorgi.WeakFormulation.CoefficientOperator
import Submission.DifferentialGeometry.External.DeGiorgi.SobolevPoincare
import Submission.DifferentialGeometry.Analysis.Integration.LpNorm
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Submission.DifferentialGeometry.External.DeGiorgi.UnitBallApproximationCore.Rescaling
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Filter _root_.Set _root_.Submission.DeGiorgi
open scoped _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_poincare_constant
    {Ω : Set E} (hd : 2 ≤ d) (hΩ : IsOpen Ω)
    (hΩ_bdd : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : E → ℝ}, MemW01p 2 f Ω →
      ∀ hw : MemW1pWitness 2 f Ω,
        ‖hw.memLp.toLp f‖ ≤ C * ‖gradLpOfWitness hw‖ := by
  let _ : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hP⟩ := smoothCompactSupport_L2_bound_on_bounded_ge_two hd hΩ_bdd
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro f hf hw
  obtain ⟨_, hw₀, φ, hφs, hφc, hφΩ, hφf, hφg⟩ := hf
  let ht (n : ℕ) : IsSmoothTestOn Ω (φ n) := ⟨hφs n, hφc n, hφΩ n⟩
  let hφw (n : ℕ) := smoothTestWitness hΩ (ht n)
  have hF : _root_.Filter.Tendsto (fun n => smoothFunToLp hΩ (ht n)) _root_.Filter.atTop
      (𝓝 (hw.memLp.toLp f)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (f_ℒp := fun n => (hφw n).memLp)
      (f_lim_ℒp := hw.memLp)).mpr hφf
  have hG : _root_.Filter.Tendsto (fun n => gradLpOfWitness (hφw n)) _root_.Filter.atTop
      (𝓝 (gradLpOfWitness hw₀)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (f_ℒp := fun n =>
      (hφw n).weakGrad_memLp) (f_lim_ℒp := hw₀.weakGrad_memLp)).mpr
    exact tendsto_eLpNorm_vector_of_componentwise
      (fun n i => ((hφw n).weakGrad_component_memLp i).sub
        (hw₀.weakGrad_component_memLp i))
      (fun i => by simpa only [hφw, smoothTestWitness, smoothGradField,
        PiLp.toLp_apply] using hφg i)
  have hGeq : gradLpOfWitness hw₀ = gradLpOfWitness hw :=
    MemLp.toLp_congr hw₀.weakGrad_memLp hw.weakGrad_memLp
      (MemW1pWitness.ae_eq hΩ hw₀ hw)
  have hbound (n : ℕ) :
      ‖smoothFunToLp hΩ (ht n)‖ ≤ C.toReal * ‖gradLpOfWitness (hφw n)‖ := by
    have hgrad : _root_.MeasureTheory.MemLp (smoothGradNorm (φ n)) 2 (volume.restrict Ω) := by
      exact MemLp.ae_eq (Eventually.of_forall fun x => by
        change ‖smoothGradField (φ n) x‖ = smoothGradNorm (φ n) x
        exact norm_smoothGradField_eq_smoothGradNorm) (hφw n).weakGrad_memLp.norm
    have hPn := hP (hφs n) (hφc n) (hφΩ n)
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hC.ne hgrad.eLpNorm_lt_top.ne) hPn
    have hnorm : _root_.MeasureTheory.eLpNorm (smoothGradNorm (φ n)) 2 (volume.restrict Ω) =
        eLpNorm (hφw n).weakGrad 2 (volume.restrict Ω) := by
      change _root_.MeasureTheory.eLpNorm (fun x => ‖(hφw n).weakGrad x‖) 2 (volume.restrict Ω) = _
      exact _root_.MeasureTheory.eLpNorm_norm _
    rw [hnorm, ENNReal.toReal_mul] at hreal
    simpa only [smoothFunToLp, gradLpOfWitness, Lp.norm_toLp] using hreal
  rw [hGeq] at hG
  exact le_of_tendsto_of_tendsto' hF.norm (hG.norm.const_mul C.toReal) hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_poincare_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_poincare_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_poincare_constant ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_poincare_constant

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "B" => Metric.ball (0 : E) 1
local notation "μ" => volume.restrict B

theorem integral_sub_average_sq_le_weakGrad
    {u : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u B) :
    (∫ x in B, (u x - ⨍ y in B, u y) ^ 2) ≤
      (DeGiorgi.CPoincVal d) ^ 2 * ∫ x in B, ‖hu.weakGrad x‖ ^ 2 := by
  let : _root_.MeasureTheory.IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr ((_root_.MeasureTheory.measure_mono Metric.ball_subset_closedBall).trans_lt
      (_root_.ProperSpace.isCompact_closedBall (0 : E) 1).measure_lt_top).ne
  let hu2 : DeGiorgi.MemW1pWitness (ENNReal.ofReal (2 : ℝ)) u B := {
    memLp := by simpa using hu.memLp
    weakGrad := hu.weakGrad
    weakGrad_component_memLp := fun i => by simpa using hu.weakGrad_component_memLp i
    isWeakGrad := hu.isWeakGrad }
  have h := DeGiorgi.poincare_unitBall_W1p_public (p := (2 : ℝ)) (by norm_num) hu2
  have hgrad : _root_.MeasureTheory.MemLp (fun x => ‖hu.weakGrad x‖) 2 μ := hu.weakGrad_memLp.norm
  have huL : _root_.MeasureTheory.MemLp (fun x => u x - ⨍ y in B, u y) 2 μ :=
    hu.memLp.sub (_root_.MeasureTheory.memLp_const _)
  norm_num only [ENNReal.ofReal_ofNat] at h
  change _root_.MeasureTheory.eLpNorm (fun x => u x - ⨍ y in B, u y) 2 μ ≤
    ENNReal.ofReal (DeGiorgi.CPoincVal d) * _root_.MeasureTheory.eLpNorm (fun x => ‖hu.weakGrad x‖) 2 μ at h
  have hc : 0 ≤ DeGiorgi.CPoincVal d := (DeGiorgi.C_poinc_val_pos (NeZero.pos d)).le
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgrad.eLpNorm_lt_top.ne) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at hr
  have hs := (sq_le_sq₀ ENNReal.toReal_nonneg (mul_nonneg hc ENNReal.toReal_nonneg)).mpr hr
  rw [Analysis.Integration.integral_sq_eq_l2 huL,
    Analysis.Integration.integral_sq_eq_l2 hgrad]
  nlinarith [hs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sub_average_sq_le_weakGrad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sub_average_sq_le_weakGrad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sub_average_sq_le_weakGrad ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sub_average_sq_le_weakGrad

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.Pointwise

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem integral_rescale_ball {x₀ : E} {R : ℝ} (hR : 0 < R) (f : E → ℝ) :
    (∫ z in Metric.ball (0 : E) 1, f (x₀ + R • z)) =
      (R ^ d)⁻¹ * ∫ x in Metric.ball x₀ R, f x := by
  have hscale := Measure.setIntegral_comp_smul_of_pos _root_.MeasureTheory.MeasureSpace.volume (fun x => f (x₀ + x))
    (Metric.ball (0 : E) 1) hR
  rw [show R • Metric.ball (0 : E) 1 = Metric.ball (0 : E) R from by
    rw [smul_unitBall hR.ne']
    simp [Real.norm_of_nonneg hR.le]] at hscale
  rw [show Module.finrank ℝ E = d from finrank_euclideanSpace_fin] at hscale
  rw [hscale, smul_eq_mul]
  congr 1
  rw [show Metric.ball x₀ R = (x₀ + ·) '' Metric.ball (0 : E) R from by simp]
  exact ((_root_.MeasureTheory.measurePreserving_add_left _root_.MeasureTheory.MeasureSpace.volume x₀).setIntegral_image_emb
    (MeasurableEquiv.addLeft x₀).measurableEmbedding f (Metric.ball (0 : E) R)).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_rescale_ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_rescale_ball target :: scope.openDecls } }

private theorem average_rescale_ball {x₀ : E} {R : ℝ} (hR : 0 < R) (f : E → ℝ) :
    (⨍ z in Metric.ball (0 : E) 1, f (x₀ + R • z)) =
      ⨍ y in Metric.ball x₀ R, f y := by
  have hvol : volume.real (Metric.ball x₀ R) =
      volume.real (Metric.ball (0 : E) 1) * R ^ d := by
    simp only [Measure.real]
    rw [Measure.addHaar_ball_of_pos _root_.MeasureTheory.MeasureSpace.volume x₀ hR, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hR.le d)]
    ring
  rw [_root_.MeasureTheory.setAverage_eq, _root_.MeasureTheory.setAverage_eq, integral_rescale_ball hR, hvol]
  simp only [smul_eq_mul, mul_inv_rev]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.average_rescale_ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.average_rescale_ball target :: scope.openDecls } }

variable [NeZero d]

theorem integral_sub_average_sq_le_radius_sq_mul_weakGrad
    {u : E → ℝ} {c : E} {R : ℝ} (hR : 0 < R)
    (hu : DeGiorgi.MemW1pWitness 2 u (Metric.ball c R)) :
    (∫ x in Metric.ball c R, (u x - ⨍ y in Metric.ball c R, u y) ^ 2) ≤
      (DeGiorgi.CPoincVal d) ^ 2 * R ^ 2 *
        ∫ x in Metric.ball c R, ‖hu.weakGrad x‖ ^ 2 := by
  have hp := integral_sub_average_sq_le_weakGrad (hu.rescaleToUnitBall hR)
  rw [average_rescale_ball hR] at hp
  rw [integral_rescale_ball (x₀ := c) hR
    (fun x => (u x - ⨍ y in Metric.ball c R, u y) ^ 2)] at hp
  have hgrad : (∫ z in Metric.ball (0 : E) 1,
        ‖(hu.rescaleToUnitBall hR).weakGrad z‖ ^ 2) =
      R ^ 2 * ((R ^ d)⁻¹ * ∫ x in Metric.ball c R, ‖hu.weakGrad x‖ ^ 2) := by
    change (∫ z in Metric.ball (0 : E) 1, ‖R • hu.weakGrad (c + R • z)‖ ^ 2) = _
    simp_rw [norm_smul, Real.norm_of_nonneg hR.le, mul_pow]
    rw [_root_.MeasureTheory.integral_const_mul, integral_rescale_ball (x₀ := c) hR (fun x => ‖hu.weakGrad x‖ ^ 2)]
  rw [hgrad] at hp
  have hpos : 0 < (R ^ d)⁻¹ := inv_pos.mpr (pow_pos hR d)
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sub_average_sq_le_radius_sq_mul_weakGrad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sub_average_sq_le_radius_sq_mul_weakGrad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sub_average_sq_le_radius_sq_mul_weakGrad ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_sub_average_sq_le_radius_sq_mul_weakGrad

theorem integral_norm_sub_average_sq_le_radius_sq_mul_weakGrad
    {ι : Type*} [Fintype ι]
    {u : E → EuclideanSpace ℝ ι} {c : E} {R : ℝ} (hR : 0 < R)
    (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) (Metric.ball c R)) :
    (∫ x in Metric.ball c R, ‖u x - ⨍ y in Metric.ball c R, u y‖ ^ 2) ≤
      (DeGiorgi.CPoincVal d) ^ 2 * R ^ 2 *
        ∑ i, ∫ x in Metric.ball c R, ‖(hu i).weakGrad x‖ ^ 2 := by
  classical
  let μR := volume.restrict (Metric.ball c R)
  let : _root_.MeasureTheory.IsFiniteMeasure μR := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hm : _root_.MeasureTheory.MemLp u 2 μR := MemLp.of_eval_piLp fun i => (hu i).memLp
  have hi : _root_.MeasureTheory.Integrable u μR := hm.integrable (by norm_num)
  have hmavg : ∀ i, (⨍ y in Metric.ball c R, u y) i =
      ⨍ y in Metric.ball c R, u y i := by
    intro i
    rw [_root_.MeasureTheory.setAverage_eq, _root_.MeasureTheory.setAverage_eq]
    change (volume.real (Metric.ball c R))⁻¹ * (∫ y in Metric.ball c R, u y) i = _
    have he := (EuclideanSpace.proj i).integral_comp_comm hi
    change (∫ y in Metric.ball c R, u y i) = (∫ y in Metric.ball c R, u y) i at he
    rw [he, smul_eq_mul]
  have hcoord (i : ι) : _root_.MeasureTheory.Integrable (fun x =>
      (u x i - ⨍ y in Metric.ball c R, u y i) ^ 2) μR :=
    ((hu i).memLp.sub (_root_.MeasureTheory.memLp_const _)).integrable_sq
  have heq : (∫ x in Metric.ball c R, ‖u x - ⨍ y in Metric.ball c R, u y‖ ^ 2) =
      ∑ i, ∫ x in Metric.ball c R, (u x i - ⨍ y in Metric.ball c R, u y i) ^ 2 := by
    simp_rw [EuclideanSpace.norm_sq_eq, PiLp.sub_apply, hmavg, Real.norm_eq_abs, sq_abs]
    exact _root_.MeasureTheory.integral_finsetSum _ fun i _ => hcoord i
  rw [heq, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => integral_sub_average_sq_le_radius_sq_mul_weakGrad hR (hu i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_norm_sub_average_sq_le_radius_sq_mul_weakGrad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_norm_sub_average_sq_le_radius_sq_mul_weakGrad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_norm_sub_average_sq_le_radius_sq_mul_weakGrad ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_norm_sub_average_sq_le_radius_sq_mul_weakGrad

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
