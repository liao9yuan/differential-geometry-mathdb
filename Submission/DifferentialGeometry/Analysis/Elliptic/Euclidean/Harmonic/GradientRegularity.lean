import Submission.DifferentialGeometry.Analysis.Elliptic.Euclidean.Harmonic.Comparison
import Submission.DifferentialGeometry.Analysis.Integration.Integral.MeanSquareDeviation
import Submission.DifferentialGeometry.Analysis.Asymptotics.PowerDecay
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.CampanatoGradient
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Classical
import Mathlib.Analysis.Calculus.ContDiff.WithLp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Filter _root_.Submission.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric
open _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_gradient_excess_power_bound_of_harmonic_error_power_bound
    {z : V → F} {R σ A q : ℝ} (hσ : 0 < σ) (hσR : 2 * σ ≤ R)
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hq4 : q < 4)
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (_root_.Metric.ball (0 : V) R))
    (happrox : ∀ c ∈ _root_.Metric.ball (0 : V) σ, ∀ r : ℝ, 0 < r → r ≤ σ →
      ∃ (h : V → F) (hh : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => h x i) (_root_.Metric.ball c r)),
        (∀ i (φ : V → ℝ), DeGiorgi.IsSmoothTestOn (_root_.Metric.ball c r) φ →
          (∫ x in _root_.Metric.ball c r, _root_.Inner.inner ℝ ((hh i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) ∧
        (∑ i, ∫ x in _root_.Metric.ball c r, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2) ≤ A * r ^ q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c ∈ _root_.Metric.ball (0 : V) σ, ∀ r : ℝ, 0 < r → r ≤ σ →
      (∑ i, ∫ x in _root_.Metric.ball c r,
        ‖(hz i).weakGrad x - ⨍ y in _root_.Metric.ball c r, (hz i).weakGrad y‖ ^ 2) ≤ K * r ^ q := by
  let M := ∑ i, ∫ x in _root_.Metric.ball (0 : V) R, ‖(hz i).weakGrad x‖ ^ 2
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => _root_.MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  obtain ⟨K, hK, hpower⟩ := exists_uniform_radius_power_bound_of_decay
    (M := M) (p := 4) (q := q) hσ (by norm_num : (0 : ℝ) < 1 / 8)
    (by norm_num : (0 : ℝ) ≤ 16384) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16386) hA) hM hq hq4
  refine ⟨K, hK, ?_⟩
  intro c hc r hr hrσ
  have hball : _root_.Metric.ball c σ ⊆ _root_.Metric.ball (0 : V) R := by
    intro x hx
    have hxc := mem_ball.mp hx
    have hc0 := mem_ball_zero_iff.mp hc
    have hn : ‖x‖ ≤ _root_.Dist.dist x c + ‖c‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (x - c) c
    exact mem_ball_zero_iff.mpr (by linarith)
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (_root_.Metric.ball c σ)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let Ex (s : ℝ) := ∑ i, ∫ x in _root_.Metric.ball c s,
    ‖(hz i).weakGrad x - ⨍ y in _root_.Metric.ball c s, (hz i).weakGrad y‖ ^ 2
  have hLp (i : ι) : _root_.MeasureTheory.MemLp (hz i).weakGrad 2 (volume.restrict (_root_.Metric.ball c σ)) :=
    (hz i).weakGrad_memLp.mono_measure (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume hball)
  have hmono : MonotoneOn Ex (_root_.Set.Ioc (0 : ℝ) σ) := by
    intro a ha b hb hab
    exact Finset.sum_le_sum fun i _ =>
      monotoneOn_integral_norm_sub_average_sq_ball (hLp i) ha hb hab
  have hEx : 0 ≤ Ex σ := Finset.sum_nonneg fun i _ => _root_.MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hExM : Ex σ ≤ M := by
    apply Finset.sum_le_sum
    intro i hi
    have h := integral_norm_sub_average_sq_le_integral_norm_sub_sq (hLp i) (0 : V)
    simp only [sub_zero] at h
    exact h.trans (_root_.MeasureTheory.setIntegral_mono_set (hz i).weakGrad_memLp.norm.integrable_sq
      (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hball))
  apply hpower Ex hmono hEx hExM _ r ⟨hr, hrσ⟩
  intro a ha s hs hsa
  have haR : _root_.Metric.ball c a ⊆ _root_.Metric.ball (0 : V) R := (_root_.Metric.ball_subset_ball ha.2).trans hball
  let hza (i : ι) := (hz i).restrict _root_.Metric.isOpen_ball haR
  obtain ⟨h, hh, hEuler, herr⟩ := happrox c hc a ha.1 ha.2
  have hexcess := integral_weakGrad_sub_average_sq_le_of_harmonic_comparison
    ha.1 hs.le (by linarith : s ≤ a / 8) hza hh hEuler
  have hratio : 0 ≤ s / a ∧ s / a ≤ 1 :=
    ⟨div_nonneg hs.le ha.1.le, (div_le_one ha.1).mpr (by linarith)⟩
  have hcoef : 2 + 16384 * (s / a) ^ 4 ≤ 16386 := by
    have hp := pow_le_one₀ hratio.1 hratio.2 (n := 4)
    linarith
  have hD0 : 0 ≤ ∑ i, ∫ x in _root_.Metric.ball c a, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => _root_.MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have herror : (2 + 16384 * (s / a) ^ 4) *
      (∑ i, ∫ x in _root_.Metric.ball c a, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2) ≤
      (16386 * A) * a ^ q := by
    exact ((mul_le_mul_of_nonneg_right hcoef hD0).trans
      (mul_le_mul_of_nonneg_left herr (by norm_num))).trans_eq (by ring)
  simpa only [Ex, hza, DeGiorgi.MemW1pWitness.restrict, Real.rpow_ofNat] using
    hexcess.trans (add_le_add le_rfl herror)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_gradient_excess_power_bound_of_harmonic_error_power_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_gradient_excess_power_bound_of_harmonic_error_power_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_gradient_excess_power_bound_of_harmonic_error_power_bound ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_gradient_excess_power_bound_of_harmonic_error_power_bound

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Filter _root_.Submission.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric
open scoped _root_.Topology _root_.ENNReal _root_.ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_contDiffOn_one_of_harmonic_error_power_bound
    {z : V → F} {R σ A q : ℝ} (hσ : 0 < σ) (hσR : 2 * σ ≤ R)
    (hA : 0 ≤ A) (hq2 : 2 < q) (hq4 : q < 4)
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (_root_.Metric.ball (0 : V) R))
    (hzc : ContinuousOn z (_root_.Metric.ball (0 : V) R))
    (happrox : ∀ c ∈ _root_.Metric.ball (0 : V) σ, ∀ r : ℝ, 0 < r → r ≤ σ →
      ∃ (h : V → F) (hh : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => h x i) (_root_.Metric.ball c r)),
        (∀ i (φ : V → ℝ), DeGiorgi.IsSmoothTestOn (_root_.Metric.ball c r) φ →
          (∫ x in _root_.Metric.ball c r, _root_.Inner.inner ℝ ((hh i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) ∧
        (∑ i, ∫ x in _root_.Metric.ball c r, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2) ≤ A * r ^ q) :
    ContDiffOn ℝ 1 z (_root_.Metric.ball (0 : V) (σ / 2)) ∧
      ∃ (G : ι → V → V) (C : ι → ℝ),
        (∀ i, 0 ≤ C i) ∧
        (∀ i, G i =ᵐ[volume.restrict (_root_.Metric.ball (0 : V) (σ / 2))] (hz i).weakGrad) ∧
        (∀ i, ∀ x ∈ _root_.Metric.ball (0 : V) (σ / 2),
          HasFDerivAt (fun y => z y i) (innerSL ℝ (G i x)) x) ∧
        ∀ i, ∀ x ∈ _root_.Metric.ball (0 : V) (σ / 2), ∀ y ∈ _root_.Metric.ball (0 : V) (σ / 2),
          ‖G i x - G i y‖ ≤ C i * ‖x - y‖ ^ ((q - 2) / 2) := by
  obtain ⟨K, hK, hpower⟩ := exists_gradient_excess_power_bound_of_harmonic_error_power_bound
    hσ hσR hA (by linarith : 0 ≤ q) hq4 hz happrox
  have hσR' : σ ≤ R := by linarith
  have hball : _root_.Metric.ball (0 : V) σ ⊆ _root_.Metric.ball (0 : V) R := _root_.Metric.ball_subset_ball hσR'
  have hα : 0 < (q - 2) / 2 := by linarith
  have hα1 : (q - 2) / 2 ≤ 1 := by linarith
  obtain ⟨G, C, hC, hGae, hGc, hHolder⟩ := exists_holder_representative_of_gradient_excess_bound
    hσ hα hα1 hK
    (fun i => (hz i).weakGrad_memLp.mono_measure (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume hball))
    (by
      intro b
      have hb := hpower b.center (b.subset_ball (_root_.Metric.mem_ball_self b.radius_pos))
        b.radius b.radius_pos b.radius_le
      have he : 2 + 2 * ((q - 2) / 2) = q := by ring
      simpa only [he] using hb)
  have hhalf : _root_.Metric.ball (0 : V) (σ / 2) ⊆ _root_.Metric.ball (0 : V) σ := _root_.Metric.ball_subset_ball (by linarith)
  have hhalfR : _root_.Metric.ball (0 : V) (σ / 2) ⊆ _root_.Metric.ball (0 : V) R := hhalf.trans hball
  let hzh (i : ι) := (hz i).restrict _root_.Metric.isOpen_ball hhalfR
  have hG (i : ι) : G i =ᵐ[volume.restrict (_root_.Metric.ball (0 : V) (σ / 2))] (hzh i).weakGrad :=
    _root_.MeasureTheory.ae_restrict_of_ae_restrict_of_subset hhalf (hGae i)
  have hzi (i : ι) : ContinuousOn (fun x => z x i) (_root_.Metric.ball (0 : V) (σ / 2)) :=
    (PiLp.continuous_apply 2 _ i).comp_continuousOn (hzc.mono hhalfR)
  have hdiff (i : ι) : ContDiffOn ℝ 1 (fun x => z x i) (_root_.Metric.ball (0 : V) (σ / 2)) :=
    (hzh i).contDiffOn_one_of_continuousOn_weakGrad _root_.Metric.isOpen_ball (hzi i) (hGc i) (hG i)
  refine ⟨PiLp.contDiff_toLp.comp_contDiffOn (contDiffOn_pi.mpr hdiff), G, C, hC, hG, ?_, hHolder⟩
  intro i x hx
  exact (hzh i).hasFDerivAt_of_continuousOn_weakGrad _root_.Metric.isOpen_ball (hzi i) (hGc i) (hG i) hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_contDiffOn_one_of_harmonic_error_power_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_contDiffOn_one_of_harmonic_error_power_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_contDiffOn_one_of_harmonic_error_power_bound ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_contDiffOn_one_of_harmonic_error_power_bound

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end
