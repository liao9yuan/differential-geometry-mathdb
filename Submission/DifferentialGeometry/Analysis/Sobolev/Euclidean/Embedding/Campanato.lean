import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Poincare
import Submission.DifferentialGeometry.External.DeGiorgi.Oscillation.Campanato
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem exists_campanato_bound_of_weak_gradient_energy
    {Ω : Set E} {u : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    {x₀ : E} {R α C : ℝ} (hball : Metric.ball x₀ R ⊆ Ω) (hC : 0 ≤ C)
    (henergy : ∀ b : DeGiorgi.CampanatoBall x₀ R,
      (∫ x in Metric.ball b.center b.radius, ‖hu.weakGrad x‖ ^ 2) ≤
        C * b.radius ^ (2 * α)) :
    ∃ Ccamp : ℝ, 0 ≤ Ccamp ∧ DeGiorgi.HasCampanatoBound u x₀ R α Ccamp := by
  have hp : 0 ≤ DeGiorgi.CPoincVal 2 :=
    (DeGiorgi.C_poinc_val_pos (by norm_num : 0 < (2 : ℕ))).le
  refine ⟨DeGiorgi.CPoincVal 2 * Real.sqrt (C / Real.pi),
    mul_nonneg hp (Real.sqrt_nonneg _), ?_⟩
  intro b
  let r : ℝ := b.radius
  let B : Set E := Metric.ball b.center r
  let μ : _root_.MeasureTheory.Measure E := volume.restrict B
  have hr : 0 < r := b.radius_pos
  have hBΩ : B ⊆ Ω := b.subset_ball.trans hball
  let huB : DeGiorgi.MemW1pWitness 2 u B := hu.restrict Metric.isOpen_ball hBΩ
  let : _root_.MeasureTheory.IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have huLp : _root_.MeasureTheory.MemLp u 2 μ := huB.memLp
  have huInt : _root_.MeasureTheory.IntegrableOn u B := huLp.integrable (by norm_num)
  refine ⟨huInt, ?_⟩
  let m : ℝ := ⨍ y in B, u y
  let J : ℝ := ∫ x in B, |u x - m|
  let Q : ℝ := ∫ x in B, (u x - m) ^ 2
  let t : ℝ := r ^ α
  have ht : 0 < t := Real.rpow_pos_of_pos hr α
  have hosc : _root_.MeasureTheory.MemLp (fun x => u x - m) 2 μ := huLp.sub (_root_.MeasureTheory.memLp_const m)
  have hsq : _root_.MeasureTheory.IntegrableOn (fun x => (u x - m) ^ 2) B := hosc.integrable_sq
  have hIone : (∫ x in B, (1 : ℝ)) = volume.real B := by simp
  have hcs : J ^ 2 ≤ volume.real B * Q := by
    have hh := DeGiorgi.weighted_power_mean_setIntegral
      (μ := _root_.MeasureTheory.MeasureSpace.volume) (s := B) (show MeasurableSet B from Metric.isOpen_ball.measurableSet)
      (p := (2 : ℝ)) (by norm_num)
      (f := fun x => |u x - m|) (w := fun _ => (1 : ℝ))
      (fun x => abs_nonneg _) (fun _ => zero_le_one)
      (by simpa only [Real.norm_eq_abs] using hosc.norm.aemeasurable)
      (show _root_.MeasureTheory.IntegrableOn (fun _ : E => (1 : ℝ)) B from _root_.MeasureTheory.integrable_const 1)
      (by simpa only [Real.rpow_two, mul_one, sq_abs] using hsq)
    simp only [mul_one, Real.rpow_two, sq_abs,
      show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, hIone] at hh
    exact hh
  have hvolume : volume.real B = Real.pi * r ^ 2 := by
    simp only [B, Measure.real, EuclideanSpace.volume_ball_fin_two,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le,
      ENNReal.toReal_ofReal Real.pi_pos.le]
    ring
  have hrpow : r ^ (2 * α) = t ^ 2 := by
    dsimp only [t]
    rw [mul_comm (2 : ℝ) α, Real.rpow_mul hr.le, Real.rpow_two]
  have hvar := integral_sub_average_sq_le_radius_sq_mul_weakGrad hr huB
  change Q ≤ (DeGiorgi.CPoincVal 2) ^ 2 * r ^ 2 *
    ∫ x in B, ‖hu.weakGrad x‖ ^ 2 at hvar
  have hE : (∫ x in B, ‖hu.weakGrad x‖ ^ 2) ≤ C * t ^ 2 := by
    have h := henergy b
    change (∫ x in B, ‖hu.weakGrad x‖ ^ 2) ≤ C * r ^ (2 * α) at h
    rwa [hrpow] at h
  have hQ : Q ≤ (DeGiorgi.CPoincVal 2) ^ 2 * r ^ 2 * C * t ^ 2 := by
    calc
      Q ≤ (DeGiorgi.CPoincVal 2) ^ 2 * r ^ 2 *
          ∫ x in B, ‖hu.weakGrad x‖ ^ 2 := hvar
      _ ≤ (DeGiorgi.CPoincVal 2) ^ 2 * r ^ 2 * (C * t ^ 2) :=
        mul_le_mul_of_nonneg_left hE (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = _ := by ring
  have hJnonneg : 0 ≤ J := _root_.MeasureTheory.integral_nonneg fun x => abs_nonneg _
  have hJsq : J ^ 2 ≤
      (DeGiorgi.CPoincVal 2 * Real.sqrt (C / Real.pi) * t * (Real.pi * r ^ 2)) ^ 2 := by
    calc
      J ^ 2 ≤ (Real.pi * r ^ 2) * Q := by simpa only [hvolume] using hcs
      _ ≤ (Real.pi * r ^ 2) *
          ((DeGiorgi.CPoincVal 2) ^ 2 * r ^ 2 * C * t ^ 2) :=
        mul_le_mul_of_nonneg_left hQ (mul_nonneg Real.pi_pos.le (sq_nonneg _))
      _ = _ := by
        simp only [mul_pow, Real.sq_sqrt (div_nonneg hC Real.pi_pos.le)]
        field_simp [Real.pi_pos.ne']
  have hJ : J ≤ DeGiorgi.CPoincVal 2 * Real.sqrt (C / Real.pi) * t *
      (Real.pi * r ^ 2) :=
    (sq_le_sq₀ hJnonneg (by positivity)).mp hJsq
  change r⁻¹ ^ α * (⨍ x in B, |u x - m|) ≤
    DeGiorgi.CPoincVal 2 * Real.sqrt (C / Real.pi)
  rw [_root_.MeasureTheory.setAverage_eq, hvolume, smul_eq_mul]
  change r⁻¹ ^ α * ((Real.pi * r ^ 2)⁻¹ * J) ≤ _
  calc
    _ ≤ r⁻¹ ^ α * ((Real.pi * r ^ 2)⁻¹ *
        (DeGiorgi.CPoincVal 2 * Real.sqrt (C / Real.pi) * t * (Real.pi * r ^ 2))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hJ (by positivity))
        (Real.rpow_nonneg (inv_nonneg.mpr hr.le) α)
    _ = DeGiorgi.CPoincVal 2 * Real.sqrt (C / Real.pi) := by
      rw [Real.inv_rpow hr.le α]
      dsimp only [t]
      field_simp [hr.ne', Real.pi_pos.ne', (Real.rpow_pos_of_pos hr α).ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_campanato_bound_of_weak_gradient_energy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_campanato_bound_of_weak_gradient_energy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_campanato_bound_of_weak_gradient_energy ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_campanato_bound_of_weak_gradient_energy

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_holder_representative_of_component_campanato_bounds
    {w : V → F} {x₀ : V} {R α : ℝ}
    (hR : 0 < R) (hα : 0 < α) (hα1 : α ≤ 1)
    (hcamp : ∀ i : ι, ∃ C : ℝ, DeGiorgi.HasCampanatoBound (fun x => w x i) x₀ R α C) :
    ∃ (v : V → F) (C : ℝ), 0 ≤ C ∧
      (v =ᵐ[volume.restrict (Metric.ball x₀ R)] w) ∧
      ∀ x ∈ Metric.ball x₀ (R / 2), ∀ y ∈ Metric.ball x₀ (R / 2),
        ‖v x - v y‖ ≤ C * ‖x - y‖ ^ α := by
  classical
  choose Ci hCi using hcamp
  choose vi hviAE hviH using fun i =>
    DeGiorgi.campanato_implies_holder hα hα1 hR (hCi i)
  let v : V → F := fun x => WithLp.toLp 2 fun i => vi i x
  let H := fun i => _root_.Max.max (DeGiorgi.CCampanatoHolder 2 α * Ci i) 0
  let C := Real.sqrt (∑ i : ι, H i ^ 2)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  refine ⟨v, C, hC, ?_, ?_⟩
  · filter_upwards [ae_all_iff.mpr hviAE] with x hx
    ext i
    exact hx i
  · intro x hx y hy
    have hbound (i : ι) : |vi i x - vi i y| ≤ H i * ‖x - y‖ ^ α :=
      (hviH i x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (norm_nonneg _) _))
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC
      (Real.rpow_nonneg (norm_nonneg _) _))).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i : ι, (vi i x - vi i y) ^ 2) ≤ (C * ‖x - y‖ ^ α) ^ 2
    calc
      (∑ i : ι, (vi i x - vi i y) ^ 2) ≤ ∑ i : ι, (H i * ‖x - y‖ ^ α) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (le_max_right _ _)
          (Real.rpow_nonneg (norm_nonneg _) _))).mpr (hbound i)
        simpa only [sq_abs] using hh
      _ = (C * ‖x - y‖ ^ α) ^ 2 := by
        simp only [mul_pow]
        rw [← Finset.sum_mul]
        dsimp only [C]
        rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (H i))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_holder_representative_of_component_campanato_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_holder_representative_of_component_campanato_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_holder_representative_of_component_campanato_bounds ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_holder_representative_of_component_campanato_bounds

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
