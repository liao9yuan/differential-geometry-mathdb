import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MetricEnergy.HolderRegularity
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.MetricEnergy.HarmonicComparison
import Submission.DifferentialGeometry.Analysis.Elliptic.Euclidean.Harmonic.GradientRegularity
import Submission.DifferentialGeometry.Analysis.Convex.CoordinateBox

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Filter _root_.Submission.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric
open scoped _root_.Topology _root_.ENNReal _root_.NNReal _root_.ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {m : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ (Fin m)

theorem exists_contDiffOn_one_of_continuous_metric_minimizer
    {z : V → F} {R a : ℝ} (hR : 0 < R) (ha : 0 < a)
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (_root_.Metric.ball (0 : V) R))
    (hzc : ContinuousOn z (_root_.Metric.ball (0 : V) R)) (hz0 : z 0 = 0)
    (B : F → F →L[ℝ] F →L[ℝ] ℝ) {L : ℝ≥0}
    (hBLip : LipschitzOnWith L B (_root_.Metric.closedBall (0 : F) a))
    (hsym : ∀ y ∈ _root_.Metric.closedBall (0 : F) a, ∀ v w, B y v w = B y w v)
    {lam : ℝ} (hlam : 0 < lam)
    (hcoerce : ∀ y ∈ _root_.Metric.closedBall (0 : F) a, ∀ v, lam * ‖v‖ ^ 2 ≤ B y v v)
    (hmin : ∀ (c : V) (s : ℝ), 0 < s → ‖c‖ + s < R →
      ∀ (q : V → F) (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (_root_.Metric.ball c s)),
      (∀ i, DeGiorgi.MemW01p 2 (fun x => q x i - z x i) (_root_.Metric.ball c s)) →
      (∀ᵐ x ∂volume.restrict (_root_.Metric.ball c s), q x ∈ _root_.Metric.closedBall (0 : F) a) →
      (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in _root_.Metric.ball c s, B (z x)
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
        (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in _root_.Metric.ball c s, B (q x)
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j)))) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ContDiffOn ℝ 1 z (_root_.Metric.ball (0 : V) r) ∧
      ∃ (G : Fin m → V → V) (C : Fin m → ℝ),
        (∀ i, 0 ≤ C i) ∧
        (∀ i, G i =ᵐ[volume.restrict (_root_.Metric.ball (0 : V) r)] (hz i).weakGrad) ∧
        (∀ i, ∀ x ∈ _root_.Metric.ball (0 : V) r, HasFDerivAt (fun y => z y i) (innerSL ℝ (G i x)) x) ∧
        ∀ i, ∀ x ∈ _root_.Metric.ball (0 : V) r, ∀ y ∈ _root_.Metric.ball (0 : V) r,
          ‖G i x - G i y‖ ≤ C i * ‖x - y‖ ^ ((1 : ℝ) / 8) := by
  have h0 : (0 : F) ∈ _root_.Metric.closedBall 0 a := _root_.Metric.mem_closedBall_self ha.le
  obtain ⟨σ₀, K, H, hσ₀, hσ₀R, hK, hH, hpower, hHolder⟩ :=
    exists_energy_and_holder_bounds_of_continuous_metric_minimizer hR ha hz hzc hz0 B
      hBLip.continuousOn (hsym 0 h0) hlam (hcoerce 0 h0) hmin
  obtain ⟨τ, hτ, hbox⟩ :=
    DifferentialGeometry.Analysis.exists_pos_coordinate_box_subset_of_mem_nhds_zero
      (_root_.Metric.closedBall_mem_nhds (0 : F) ha)
  obtain ⟨r₀, hr₀, hrange⟩ := DifferentialGeometry.Analysis.exists_source_ball_mapsTo_coordinate_box
    (hzc.continuousAt (_root_.Metric.ball_mem_nhds _ hR)) hz0 hτ
  let σ := _root_.Min.min (r₀ / 3) (σ₀ / 5)
  have hσ : 0 < σ := lt_min (by positivity) (by positivity)
  have hσr₀ : σ ≤ r₀ / 3 := min_le_left _ _
  have hσσ₀ : σ ≤ σ₀ / 5 := min_le_right _ _
  have hσR : 2 * σ ≤ R := by linarith
  let C₀ := 2 * (L : ℝ) * (m + 1) * H / lam
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  let A := C₀ * K
  have hA : 0 ≤ A := mul_nonneg hC₀ hK
  have happ : ∀ c ∈ _root_.Metric.ball (0 : V) σ, ∀ r : ℝ, 0 < r → r ≤ σ →
      ∃ (h : V → F) (hh : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => h x i) (_root_.Metric.ball c r)),
        (∀ i (φ : V → ℝ), DeGiorgi.IsSmoothTestOn (_root_.Metric.ball c r) φ →
          (∫ x in _root_.Metric.ball c r, _root_.Inner.inner ℝ ((hh i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) ∧
        (∑ i, ∫ x in _root_.Metric.ball c r, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2) ≤
          A * r ^ ((9 : ℝ) / 4) := by
    intro c hc r hr hrσ
    have hc0 : ‖c‖ < σ := mem_ball_zero_iff.mp hc
    have hball : _root_.Metric.ball c r ⊆ _root_.Metric.ball (0 : V) R := by
      intro x hx
      have hn : ‖x‖ ≤ _root_.Dist.dist x c + ‖c‖ := by
        simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (x - c) c
      exact mem_ball_zero_iff.mpr (by have hd := mem_ball.mp hx; linarith)
    have hball₀ : _root_.Metric.ball c r ⊆ _root_.Metric.closedBall (0 : V) r₀ := by
      intro x hx
      have hn : ‖x‖ ≤ _root_.Dist.dist x c + ‖c‖ := by
        simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (x - c) c
      exact mem_closedBall_zero_iff.mpr (by have hd := mem_ball.mp hx; linarith)
    have hballH : _root_.Metric.ball c r ⊆ _root_.Metric.ball (0 : V) (σ₀ / 2) := by
      intro x hx
      have hn : ‖x‖ ≤ _root_.Dist.dist x c + ‖c‖ := by
        simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (x - c) c
      exact mem_ball_zero_iff.mpr (by have hd := mem_ball.mp hx; linarith)
    have hcH : c ∈ _root_.Metric.ball (0 : V) (σ₀ / 2) := mem_ball_zero_iff.mpr (by linarith)
    let hzr (i : Fin m) := (hz i).restrict _root_.Metric.isOpen_ball hball
    have hzC : ∀ᵐ x ∂volume.restrict (_root_.Metric.ball c r), ∀ i, |z x i| ≤ τ := by
      filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_ball] with x hx
      exact hrange x (hball₀ hx)
    have hzcC : ∀ i, |z c i| ≤ τ := hrange c (hball₀ (_root_.Metric.mem_ball_self hr))
    obtain ⟨h, hh, hEuler, herr⟩ := exists_holder_harmonic_comparison_of_metric_minimality hr
      (by norm_num : (0 : ℝ) ≤ 3 / 4) hH hzr (fun _ => τ) hzC B
      (hBLip.mono hbox) hzcC (hsym _ (hbox hzcC)) hlam (hcoerce _ (hbox hzcC))
      (fun x hx => hHolder x (hballH hx) c hcH)
      (fun q hq hqz hqC => hmin c r hr (by linarith) q hq hqz
        (hqC.mono fun x hx => hbox hx))
    have hEp : (∑ i, ∫ x in _root_.Metric.ball c r, ‖(hz i).weakGrad x‖ ^ 2) ≤ K * r ^ ((3 : ℝ) / 2) :=
      hpower c (mem_ball_zero_iff.mpr (by linarith)) r hr (by linarith)
    have herr' : (∑ i, ∫ x in _root_.Metric.ball c r, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2) ≤
        C₀ * r ^ ((3 : ℝ) / 4) * ∑ i, ∫ x in _root_.Metric.ball c r, ‖(hz i).weakGrad x‖ ^ 2 := by
      simpa only [hzr, DeGiorgi.MemW1pWitness.restrict, Fintype.card_fin, C₀] using herr
    refine ⟨h, hh, hEuler, herr'.trans ?_⟩
    have hp := mul_le_mul_of_nonneg_left hEp
      (mul_nonneg hC₀ (Real.rpow_nonneg hr.le ((3 : ℝ) / 4)))
    have heq : C₀ * r ^ ((3 : ℝ) / 4) * (K * r ^ ((3 : ℝ) / 2)) = A * r ^ ((9 : ℝ) / 4) := by
      rw [show (9 : ℝ) / 4 = 3 / 4 + 3 / 2 by norm_num, Real.rpow_add hr]
      dsimp only [A]
      ring
    exact hp.trans_eq heq
  obtain ⟨hC1, G, C, hC, hG, hD, hHolderG⟩ := exists_contDiffOn_one_of_harmonic_error_power_bound
    hσ hσR hA (by norm_num : (2 : ℝ) < 9 / 4) (by norm_num : (9 / 4 : ℝ) < 4) hz hzc happ
  refine ⟨σ / 2, half_pos hσ, by linarith, hC1, G, C, hC, hG, hD, ?_⟩
  norm_num only [show (((9 : ℝ) / 4) - 2) / 2 = 1 / 8 by norm_num] at hHolderG
  exact hHolderG

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_contDiffOn_one_of_continuous_metric_minimizer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_contDiffOn_one_of_continuous_metric_minimizer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_contDiffOn_one_of_continuous_metric_minimizer ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_contDiffOn_one_of_continuous_metric_minimizer

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end
