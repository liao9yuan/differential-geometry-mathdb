import Submission.DifferentialGeometry.Analysis.Integration.Lp.Product
import Submission.DifferentialGeometry.Analysis.Integration.Lp.ZeroExtension
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.Sobolev
import Mathlib.MeasureTheory.Function.Holder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Metric
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

def cutoffDiffQuotLp {Ω : Set E} (hΩ : MeasurableSet Ω)
    {η : E → ℝ} (hη : _root_.MeasureTheory.MemLp η ∞ _root_.MeasureTheory.MeasureSpace.volume) (k : Fin d) (h : ℝ) :
    Lp ℝ 2 (volume.restrict Ω) →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) :=
  let T := (Lp.compMeasurePreservingₗᵢ ℝ (fun x : E => x + h • EuclideanSpace.single k 1)
    (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume _)).toContinuousLinearMap
  let D := h⁻¹ • (T - ContinuousLinearMap.id ℝ (_root_.MeasureTheory.Lp ℝ 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)))
  ((ContinuousLinearMap.mul ℝ ℝ).holderL _root_.MeasureTheory.MeasureSpace.volume ∞ 2 2 (hη.toLp η)).comp
    (D.comp (Lp.zeroExtendₗᵢ (𝕜 := ℝ) hΩ).toContinuousLinearMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.cutoffDiffQuotLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.cutoffDiffQuotLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.cutoffDiffQuotLp ``Submission.DifferentialGeometry.Analysis.Sobolev.cutoffDiffQuotLp

theorem cutoffDiffQuotLp_coeFn {Ω : Set E} (hΩ : MeasurableSet Ω)
    {η : E → ℝ} (hη : _root_.MeasureTheory.MemLp η ∞ _root_.MeasureTheory.MeasureSpace.volume) (k : Fin d) (h : ℝ)
    (hroom : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω) (u : _root_.MeasureTheory.Lp ℝ 2 (volume.restrict Ω)) :
    cutoffDiffQuotLp hΩ hη k h u =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] fun x => η x * diffQuot k h u x := by
  let U := Lp.zeroExtend hΩ u
  let T := Lp.compMeasurePreserving (fun x : E => x + h • EuclideanSpace.single k 1)
    (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume _) U
  let Q := h⁻¹ • (T - U)
  have htranslate : T =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] fun x => U (x + h • EuclideanSpace.single k 1) :=
    Lp.coeFn_compMeasurePreserving U (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume _)
  have hU := Lp.coeFn_zeroExtend hΩ u
  have hshift := (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume (h • EuclideanSpace.single k (1 : ℝ))).quasiMeasurePreserving.ae hU
  have hQ : Q =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] fun x => h⁻¹ * (Ω.indicator u (x + h • EuclideanSpace.single k 1) - Ω.indicator u x) := by
    filter_upwards [Lp.coeFn_smul h⁻¹ (T - U), Lp.coeFn_sub T U, htranslate, hU, hshift]
      with x hs hsub ht hu hh
    rw [hs, Pi.smul_apply, hsub, Pi.sub_apply, ht, hu, hh, smul_eq_mul]
  have hholder := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) (hη.toLp η) Q
  change (cutoffDiffQuotLp hΩ hη k h u) =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] _
  filter_upwards [hholder, hQ, hη.coeFn_toLp] with x hm hq hηx
  change (ContinuousLinearMap.mul ℝ ℝ).holder 2 (hη.toLp η) Q x = _
  rw [hm, ContinuousLinearMap.mul_apply', hηx, hq]
  by_cases hh : h = 0
  · simp [hh]
  by_cases hx : η x = 0
  · simp only [hx, _root_.MulZeroClass.zero_mul]
  have hxs : x ∈ tsupport η := subset_tsupport η hx
  have hxΩ : x ∈ Ω := hroom (_root_.Metric.self_subset_cthickening _ hxs)
  have hsΩ : x + h • EuclideanSpace.single k (1 : ℝ) ∈ Ω := by
    apply hroom
    apply _root_.Metric.closedBall_subset_cthickening hxs |h|
    rw [_root_.Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp only [PiLp.norm_single, _root_.NormOneClass.norm_one, mul_one, Real.norm_eq_abs, le_refl]
  rw [_root_.Set.indicator_of_mem hxΩ, _root_.Set.indicator_of_mem hsΩ, diffQuot_apply_of_ne k hh]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.cutoffDiffQuotLp_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.cutoffDiffQuotLp_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.cutoffDiffQuotLp_coeFn ``Submission.DifferentialGeometry.Analysis.Sobolev.cutoffDiffQuotLp_coeFn


theorem integral_sq_cutoffDiffQuotLp {Ω : Set E} (hΩ : MeasurableSet Ω)
    {η : E → ℝ} (hη : _root_.MeasureTheory.MemLp η ∞ _root_.MeasureTheory.MeasureSpace.volume) (k : Fin d) (h : ℝ)
    (hroom : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω) (u : _root_.MeasureTheory.Lp ℝ 2 (volume.restrict Ω)) :
    (∫ x, (η x * diffQuot k h u x) ^ 2) = ‖cutoffDiffQuotLp hΩ hη k h u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [cutoffDiffQuotLp_coeFn hΩ hη k h hroom u] with x hx
  simp only [Real.inner_apply, hx, pow_two]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.integral_sq_cutoffDiffQuotLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.integral_sq_cutoffDiffQuotLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.integral_sq_cutoffDiffQuotLp ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_sq_cutoffDiffQuotLp

theorem integrable_integral_sq_cutoff_diffQuot_comp
    {Z Y : Type*} [MeasurableSpace Z] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {μ : _root_.MeasureTheory.Measure Z} {Ω : Set E} (hΩ : MeasurableSet Ω)
    {η : E → ℝ} (hη : _root_.MeasureTheory.MemLp η ∞ _root_.MeasureTheory.MeasureSpace.volume) (k : Fin d) (h : ℝ)
    (hroom : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω)
    (A : Y →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (volume.restrict Ω)) {u : Z → Y} (hu : _root_.MeasureTheory.MemLp u 2 μ) :
    Integrable (fun t => ∫ x, (η x * diffQuot k h (A (u t)) x) ^ 2) μ := by
  let hc := (cutoffDiffQuotLp hΩ hη k h).comp A
  have hmem := hu.continuousLinearMap_comp hc
  have hi := hmem.norm.integrable_sq
  apply hi.congr
  filter_upwards [] with t
  change ‖cutoffDiffQuotLp hΩ hη k h (A (u t))‖ ^ 2 = _
  exact (integral_sq_cutoffDiffQuotLp hΩ hη k h hroom (A (u t))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.integrable_integral_sq_cutoff_diffQuot_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.integrable_integral_sq_cutoff_diffQuot_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.integrable_integral_sq_cutoff_diffQuot_comp ``Submission.DifferentialGeometry.Analysis.Sobolev.integrable_integral_sq_cutoff_diffQuot_comp


theorem cutoff_diffQuot_congr_ae_local {Ω : Set E} (hΩ : MeasurableSet Ω)
    (k : Fin d) (h : ℝ) (η : E → ℝ)
    (hroom : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω) {u v : E → ℝ}
    (huv : u =ᵐ[volume.restrict Ω] v) :
    (fun x => η x * diffQuot k h u x) =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] fun x => η x * diffQuot k h v x := by
  have hind : Ω.indicator u =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] Ω.indicator v := by
    rw [_root_.Filter.EventuallyEq, _root_.MeasureTheory.ae_restrict_iff' hΩ] at huv
    filter_upwards [huv] with x hx
    by_cases hxΩ : x ∈ Ω
    · simp only [_root_.Set.indicator_of_mem hxΩ, hx hxΩ]
    · simp only [_root_.Set.indicator_of_notMem hxΩ]
  have hs := (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume
    (h • EuclideanSpace.single k (1 : ℝ))).quasiMeasurePreserving.ae_eq hind
  filter_upwards [hind, hs] with x hx hsx
  by_cases hηx : η x = 0
  · simp only [hηx, _root_.MulZeroClass.zero_mul]
  have hxs : x ∈ tsupport η := subset_tsupport η hηx
  have hxΩ : x ∈ Ω := hroom (_root_.Metric.self_subset_cthickening _ hxs)
  have hsΩ : x + h • EuclideanSpace.single k (1 : ℝ) ∈ Ω := by
    apply hroom
    apply _root_.Metric.closedBall_subset_cthickening hxs |h|
    rw [_root_.Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp only [PiLp.norm_single, _root_.NormOneClass.norm_one, mul_one, Real.norm_eq_abs, le_refl]
  simp only [_root_.Set.indicator_of_mem hxΩ] at hx
  change Ω.indicator u (x + h • EuclideanSpace.single k 1) =
    Ω.indicator v (x + h • EuclideanSpace.single k 1) at hsx
  simp only [_root_.Set.indicator_of_mem hsΩ] at hsx
  simp only [diffQuot, hx, hsx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.cutoff_diffQuot_congr_ae_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.cutoff_diffQuot_congr_ae_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.cutoff_diffQuot_congr_ae_local ``Submission.DifferentialGeometry.Analysis.Sobolev.cutoff_diffQuot_congr_ae_local

theorem integral_sq_cutoff_diffQuot_uncurry_compLpL
    {Z Y : Type*} [MeasurableSpace Z] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {μ : _root_.MeasureTheory.Measure Z} {Ω : Set E} (hΩ : MeasurableSet Ω)
    (A : Y →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (volume.restrict Ω)) (u : _root_.MeasureTheory.Lp Y 2 μ)
    (η : E → ℝ) (k : Fin d) (h : ℝ)
    (hroom : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    (∫ t, (∫ x, (η x * diffQuot k h
      (fun y => Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
        (A.compLpL 2 μ u) (t, y)) x)^2) ∂μ) =
      ∫ t, (∫ x, (η x * diffQuot k h (A (u t)) x)^2) ∂μ := by
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [Lp.uncurry_compLpL_coeFn (𝕜 := ℝ) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) A u]
    with t ht
  exact _root_.MeasureTheory.integral_congr_ae ((cutoff_diffQuot_congr_ae_local hΩ k h η hroom ht).fun_comp (· ^ 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.integral_sq_cutoff_diffQuot_uncurry_compLpL then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.integral_sq_cutoff_diffQuot_uncurry_compLpL"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.integral_sq_cutoff_diffQuot_uncurry_compLpL ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_sq_cutoff_diffQuot_uncurry_compLpL

end DifferentialGeometry.Analysis.Sobolev
