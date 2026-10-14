import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Affine
import Submission.DifferentialGeometry.Analysis.Integration.PlaneScaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem sum_integral_weak_metric_compAddSmul
    {Ω : Set (EuclideanSpace ℝ (Fin 2))}
    {w : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ ι}
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) Ω)
    (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (b : EuclideanSpace ℝ (Fin 2)) {a : ℝ} (ha : a ≠ 0)
    (S : Set (EuclideanSpace ℝ (Fin 2))) :
    (∑ j : Fin 2, ∫ x in (fun y => b + a • y) ⁻¹' S,
      A (w (b + a • x))
        (WithLp.toLp 2 (fun i => ((hw i).compAddSmul b ha).weakGrad x j))
        (WithLp.toLp 2 (fun i => ((hw i).compAddSmul b ha).weakGrad x j))) =
    ∑ j : Fin 2, ∫ x in S, A (w x)
      (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hw i).weakGrad x j)) := by
  apply Finset.sum_congr rfl
  intro j hj
  simp_rw [DeGiorgi.weakGrad_column_compAddSmul]
  convert integral_sq_mul_comp_add_smul_plane (fun x => A (w x)
    (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
    (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) b ha S using 1
  apply _root_.MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.sum_integral_weak_metric_compAddSmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.sum_integral_weak_metric_compAddSmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.sum_integral_weak_metric_compAddSmul ``Submission.DifferentialGeometry.Analysis.sum_integral_weak_metric_compAddSmul

omit [Fintype ι] in
theorem integral_sum_weak_metric_compAddSmul
    {Ω : Set (EuclideanSpace ℝ (Fin 2))}
    {w : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ ι}
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) Ω)
    (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (b : EuclideanSpace ℝ (Fin 2)) {a : ℝ} (ha : a ≠ 0)
    (S : Set (EuclideanSpace ℝ (Fin 2))) :
    (∫ x in (fun y => b + a • y) ⁻¹' S,
      ∑ j : Fin 2, A (w (b + a • x))
        (WithLp.toLp 2 (fun i => ((hw i).compAddSmul b ha).weakGrad x j))
        (WithLp.toLp 2 (fun i => ((hw i).compAddSmul b ha).weakGrad x j))) =
    ∫ x in S, ∑ j : Fin 2, A (w x)
      (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hw i).weakGrad x j)) := by
  simp_rw [DeGiorgi.weakGrad_column_compAddSmul]
  convert integral_sq_mul_comp_add_smul_plane (fun x => ∑ j : Fin 2, A (w x)
    (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
    (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) b ha S using 1
  apply _root_.MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_sum_weak_metric_compAddSmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_sum_weak_metric_compAddSmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_sum_weak_metric_compAddSmul ``Submission.DifferentialGeometry.Analysis.integral_sum_weak_metric_compAddSmul

end DifferentialGeometry.Analysis

end

noncomputable section
open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis

variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

omit [Fintype ι] in
theorem weak_replacement_minimality_comp_add_smul_center
    {Ω : Set V} {w : V → F}
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) Ω)
    {K : Set F} (A : F → F →L[ℝ] F →L[ℝ] ℝ)
    (b : V) {R c : ℝ} (hc : 0 < c)
    (hmin : ∀ (q : V → F)
      (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (Metric.ball b c)),
      (∀ᵐ x ∂volume.restrict (Metric.ball b c), q x ∈ K) →
      (q =ᵐ[volume.restrict (Metric.ball b c \ Metric.closedBall b R)] w) →
      (∑ j : Fin 2, ∫ x in Metric.closedBall b R, A (w x)
        (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) ≤
      ∑ j : Fin 2, ∫ x in Metric.closedBall b R, A (q x)
        (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hq i).weakGrad x j)))
    (q : V → F)
    (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (Metric.ball 0 1))
    (hqK : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1), q x ∈ K)
    (hqw : q =ᵐ[volume.restrict (Metric.ball (0 : V) 1 \ Metric.closedBall 0 (R / c))]
      (fun x => w (b + c • x))) :
    (∑ j : Fin 2, ∫ x in Metric.closedBall (0 : V) (R / c), A (w (b + c • x))
      (WithLp.toLp 2 (fun i => ((hw i).compAddSmul b hc.ne').weakGrad x j))
      (WithLp.toLp 2 (fun i => ((hw i).compAddSmul b hc.ne').weakGrad x j))) ≤
    ∑ j : Fin 2, ∫ x in Metric.closedBall (0 : V) (R / c), A (q x)
      (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hq i).weakGrad x j)) := by
  have hcne : c ≠ 0 := hc.ne'
  let qb : V → F := fun x => q (-c⁻¹ • b + c⁻¹ • x)
  have hcenter : -c⁻¹ • b + c⁻¹ • b = (0 : V) := by simp only [neg_smul, neg_add_cancel]
  have hpre : (fun x : V => -c⁻¹ • b + c⁻¹ • x) ⁻¹' Metric.ball 0 1 = Metric.ball b c := by
    rw [← hcenter, preimage_add_smul_ball_plane _ b (inv_pos.mpr hc)]
    simp only [div_inv_eq_mul, one_mul]
  have hsub : Metric.ball b c ⊆
      (fun x : V => -c⁻¹ • b + c⁻¹ • x) ⁻¹' Metric.ball 0 1 := by rw [hpre]
  let hqb (i : ι) : DeGiorgi.MemW1pWitness 2 (fun x => qb x i) (Metric.ball b c) :=
    DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball hsub
      ((hq i).compAddSmul (-c⁻¹ • b) (inv_ne_zero hcne))
  have hqbK : ∀ᵐ x ∂volume.restrict (Metric.ball b c), qb x ∈ K := by
    have ht := (quasiMeasurePreserving_add_smul_restrict _root_.MeasureTheory.MeasureSpace.volume (-c⁻¹ • b)
      (inv_ne_zero hcne) (Metric.ball (0 : V) 1)).ae hqK
    rwa [hpre] at ht
  have hpreC : (fun x : V => -c⁻¹ • b + c⁻¹ • x) ⁻¹'
      (Metric.ball 0 1 \ Metric.closedBall 0 (R / c)) =
      Metric.ball b c \ Metric.closedBall b R := by
    rw [_root_.Set.preimage_sdiff, hpre, ← hcenter,
      preimage_add_smul_closedBall_plane _ b (inv_pos.mpr hc)]
    rw [div_inv_eq_mul, div_mul_cancel₀ R hcne]
  have hqbw : qb =ᵐ[volume.restrict (Metric.ball b c \ Metric.closedBall b R)] w := by
    have ht := (quasiMeasurePreserving_add_smul_restrict _root_.MeasureTheory.MeasureSpace.volume (-c⁻¹ • b)
      (inv_ne_zero hcne) (Metric.ball (0 : V) 1 \ Metric.closedBall 0 (R / c))).ae hqw
    rw [hpreC] at ht
    filter_upwards [ht] with x hx
    have hcanc : b + c • (-c⁻¹ • b + c⁻¹ • x) = x := by
      simp only [neg_smul, smul_add, smul_neg, smul_smul, mul_inv_cancel₀ hcne, one_smul]
      abel
    simpa only [qb, hcanc] using hx
  have hcomp := hmin
    qb hqb hqbK hqbw
  have hew := sum_integral_weak_metric_compAddSmul hw A b hcne (Metric.closedBall b R)
  have heq := sum_integral_weak_metric_compAddSmul hq A (-c⁻¹ • b) (inv_ne_zero hcne)
    (Metric.closedBall (0 : V) (R / c))
  have hpreW : (fun x : V => b + c • x) ⁻¹' Metric.closedBall b R =
      Metric.closedBall (0 : V) (R / c) := by
    simpa only [smul_zero, add_zero] using preimage_add_smul_closedBall_plane b 0 hc R
  rw [hpreW] at hew
  have hpreQ : (fun x : V => -c⁻¹ • b + c⁻¹ • x) ⁻¹'
      Metric.closedBall (0 : V) (R / c) = Metric.closedBall b R := by
    rw [← hcenter, preimage_add_smul_closedBall_plane _ b (inv_pos.mpr hc),
      div_inv_eq_mul, div_mul_cancel₀ R hcne]
  rw [hpreQ] at heq
  have heq' : (∑ j : Fin 2, ∫ x in Metric.closedBall b R, A (qb x)
      (WithLp.toLp 2 (fun i => (hqb i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hqb i).weakGrad x j))) =
      ∑ j : Fin 2, ∫ x in Metric.closedBall (0 : V) (R / c), A (q x)
        (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hq i).weakGrad x j)) := by
    simpa only [hqb, DeGiorgi.MemW1pWitness.restrict, qb, zero_add] using heq
  exact hew.trans_le (hcomp.trans_eq heq')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.weak_replacement_minimality_comp_add_smul_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.weak_replacement_minimality_comp_add_smul_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.weak_replacement_minimality_comp_add_smul_center ``Submission.DifferentialGeometry.Analysis.weak_replacement_minimality_comp_add_smul_center

end DifferentialGeometry.Analysis

end

end

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter _root_.Metric
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis

theorem preimage_affine_ball_self
    (b : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) :
    (fun x : EuclideanSpace ℝ (Fin 2) => b + r • x) ⁻¹' _root_.Metric.ball b r = _root_.Metric.ball 0 1 := by
  ext x
  simp only [_root_.Set.mem_preimage, _root_.Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
    norm_smul, Real.norm_eq_abs, abs_of_pos hr, sub_zero]
  rw [mul_lt_iff_lt_one_right hr]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.preimage_affine_ball_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.preimage_affine_ball_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.preimage_affine_ball_self ``Submission.DifferentialGeometry.Analysis.preimage_affine_ball_self

theorem integral_quadratic_weakGrad_compAddSmul_ball
    {m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin 2))}
    {w : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m)}
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) Ω)
    (A : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (b : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) (j : Fin 2) :
    (∫ x in _root_.Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
      A (b + r • x)
        (WithLp.toLp 2 (fun i => ((hw i).compAddSmul b hr.ne').weakGrad x j))
        (WithLp.toLp 2 (fun i => ((hw i).compAddSmul b hr.ne').weakGrad x j))) =
      ∫ x in _root_.Metric.ball b r,
        A x (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j)) := by
  have h := integral_quadratic_comp_add_smul_plane A
    (fun x => WithLp.toLp 2 (fun i => (hw i).weakGrad x j)) b hr.ne' (_root_.Metric.ball b r)
  rw [preimage_affine_ball_self b hr] at h
  simpa only [DeGiorgi.weakGrad_column_compAddSmul] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_quadratic_weakGrad_compAddSmul_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_quadratic_weakGrad_compAddSmul_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_quadratic_weakGrad_compAddSmul_ball ``Submission.DifferentialGeometry.Analysis.integral_quadratic_weakGrad_compAddSmul_ball

end DifferentialGeometry.Analysis

end

end
