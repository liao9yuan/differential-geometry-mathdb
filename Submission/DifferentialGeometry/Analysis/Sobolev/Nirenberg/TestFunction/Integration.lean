import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.Sobolev
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.CrossTermBoundsNonSmooth.CrossBoundsNonSmooth

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Metric
open scoped _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem memLp_sq_mul_diffQuot
    {η v : E → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (hv : _root_.MeasureTheory.MemLp v 2 _root_.MeasureTheory.MeasureSpace.volume) (k : Fin d) (h : ℝ) :
    MemLp (fun x => η x ^ 2 * diffQuot k h v x) 2 volume := by
  have hηsq : _root_.MeasureTheory.MemLp (fun x => η x ^ 2) ∞ volume := by
    apply (hη.pow 2).memLp_of_hasCompactSupport
    simpa only [pow_two] using (hηc.mul_right : HasCompactSupport (fun x => η x * η x))
  exact (memLp_diffQuot_two k h hv).mul' hηsq

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.memLp_sq_mul_diffQuot
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.memLp_sq_mul_diffQuot target :: scope.openDecls } }

theorem integral_mul_nirenbergTestFunction_eq
    {w v η : E → ℝ} (hw : _root_.MeasureTheory.MemLp w 2 _root_.MeasureTheory.MeasureSpace.volume) (hv : _root_.MeasureTheory.MemLp v 2 _root_.MeasureTheory.MeasureSpace.volume)
    (hη : Continuous η) (hηc : HasCompactSupport η) (k : Fin d) (h : ℝ) :
    (∫ x, w x * nirenbergTestFunction k h η v x) =
      -∫ x, diffQuot k h w x * (η x ^ 2 * diffQuot k h v x) := by
  by_cases hh : h = 0
  · simp [hh, nirenbergTestFunction_zero_h]
  have hid := integral_diffQuot_mul_eq_neg_integral_mul_diffQuot k hh hw
    (memLp_sq_mul_diffQuot hη hηc hv k h)
  dsimp only [nirenbergTestFunction]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_mul_nirenbergTestFunction_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_mul_nirenbergTestFunction_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_mul_nirenbergTestFunction_eq ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_mul_nirenbergTestFunction_eq

theorem integral_weight_mul_nirenbergTestFunction_eq
    {a u v η : E → ℝ} (hau : _root_.MeasureTheory.MemLp (fun x => a x * u x) 2 _root_.MeasureTheory.MeasureSpace.volume)
    (hv : _root_.MeasureTheory.MemLp v 2 _root_.MeasureTheory.MeasureSpace.volume) (hη : Continuous η) (hηc : HasCompactSupport η)
    (k : Fin d) (h : ℝ) :
    (∫ x, a x * u x * nirenbergTestFunction k h η v x) =
      -∫ x, (translate k h a x * diffQuot k h u x + diffQuot k h a x * u x) *
        (η x ^ 2 * diffQuot k h v x) := by
  rw [integral_mul_nirenbergTestFunction_eq hau hv hη hηc k h]
  simp only [NirenbergEuclidean.diffQuot_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_weight_mul_nirenbergTestFunction_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_weight_mul_nirenbergTestFunction_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_weight_mul_nirenbergTestFunction_eq ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_weight_mul_nirenbergTestFunction_eq

theorem integral_self_nirenbergTestFunction_eq_neg_integral_sq
    {u η : E → ℝ} (hu : _root_.MeasureTheory.MemLp u 2 _root_.MeasureTheory.MeasureSpace.volume)
    (hη : Continuous η) (hηc : HasCompactSupport η) (k : Fin d) (h : ℝ) :
    (∫ x, u x * nirenbergTestFunction k h η u x) =
      -∫ x, (η x * diffQuot k h u x) ^ 2 := by
  rw [integral_mul_nirenbergTestFunction_eq hu hu hη hηc k h]
  congr 1
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards with x
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_self_nirenbergTestFunction_eq_neg_integral_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_self_nirenbergTestFunction_eq_neg_integral_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_self_nirenbergTestFunction_eq_neg_integral_sq ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_self_nirenbergTestFunction_eq_neg_integral_sq

theorem integral_mul_nirenbergTestFunction_comm
    {u v η : E → ℝ} (hu : _root_.MeasureTheory.MemLp u 2 _root_.MeasureTheory.MeasureSpace.volume) (hv : _root_.MeasureTheory.MemLp v 2 _root_.MeasureTheory.MeasureSpace.volume)
    (hη : Continuous η) (hηc : HasCompactSupport η) (k : Fin d) (h : ℝ) :
    (∫ x, u x * nirenbergTestFunction k h η v x) =
      ∫ x, v x * nirenbergTestFunction k h η u x := by
  rw [integral_mul_nirenbergTestFunction_eq hu hv hη hηc k h,
    integral_mul_nirenbergTestFunction_eq hv hu hη hηc k h]
  congr 1
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards with x
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_mul_nirenbergTestFunction_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_mul_nirenbergTestFunction_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_mul_nirenbergTestFunction_comm ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_mul_nirenbergTestFunction_comm

private theorem weighted_diffQuot_coercivity_pointwise
    {a u η : E → ℝ} (k : Fin d) (h : ℝ) {lam A : ℝ} (hlam : 0 < lam)
    (hA : 0 ≤ A) (x : E)
    (ha : η x ≠ 0 → lam ≤ translate k h a x)
    (hda : η x ≠ 0 → |diffQuot k h a x| ≤ A) :
    lam / 2 * (η x * diffQuot k h u x)^2 -
        A^2 / (2 * lam) * (η x * u x)^2 ≤
      (translate k h a x * diffQuot k h u x + diffQuot k h a x * u x) *
        (η x ^ 2 * diffQuot k h u x) := by
  by_cases hη : η x = 0
  · simp [hη]
  let r := η x * diffQuot k h u x
  let s := η x * u x
  let b := diffQuot k h a x
  have hsq : b^2 * s^2 ≤ A^2 * s^2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg s)
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg b) hA).mpr (hda hη)
  have hy := DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds.two_abs_mul_le_eps_sq_add
    r (b * s) lam hlam
  have hab : -(abs r * abs (b * s)) ≤ b * s * r := by
    have ht := neg_abs_le (b * s * r)
    simpa only [abs_mul, mul_comm] using ht
  have hab' : 2 * (b * s * r) ≥ -(lam * r^2 + (1 / lam) * (b * s)^2) := by
    nlinarith
  have hcoef := mul_le_mul_of_nonneg_right (ha hη) (sq_nonneg r)
  have hinv := mul_le_mul_of_nonneg_left hsq (le_of_lt (one_div_pos.mpr hlam))
  have heq : A^2 / (2 * lam) = (1 / lam) * A^2 / 2 := by ring
  have htarget : lam / 2 * r^2 - A^2 / (2 * lam) * s^2 ≤
      translate k h a x * r^2 + b * s * r := by
    rw [heq]
    rw [mul_pow] at hab'
    nlinarith
  calc
    _ ≤ translate k h a x * r^2 + b * s * r := htarget
    _ = _ := by dsimp [r, s, b]; ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.weighted_diffQuot_coercivity_pointwise
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.weighted_diffQuot_coercivity_pointwise target :: scope.openDecls } }

theorem neg_integral_weight_mul_nirenbergTestFunction_ge
    {a u η : E → ℝ} (hu : _root_.MeasureTheory.MemLp u 2 _root_.MeasureTheory.MeasureSpace.volume)
    (hau : _root_.MeasureTheory.MemLp (fun x => a x * u x) 2 _root_.MeasureTheory.MeasureSpace.volume)
    (hη : Continuous η) (hηc : HasCompactSupport η)
    (k : Fin d) (h : ℝ) {lam A : ℝ} (hlam : 0 < lam) (hA : 0 ≤ A)
    (ha : ∀ x, η x ≠ 0 → lam ≤ translate k h a x)
    (hda : ∀ x, η x ≠ 0 → |diffQuot k h a x| ≤ A) :
    lam / 2 * (∫ x, (η x * diffQuot k h u x)^2) -
        A^2 / (2 * lam) * (∫ x, (η x * u x)^2) ≤
      -(∫ x, a x * u x * nirenbergTestFunction k h η u x) := by
  have hηlp : _root_.MeasureTheory.MemLp η ∞ volume := hη.memLp_of_hasCompactSupport hηc
  have hηu : _root_.MeasureTheory.MemLp (fun x => η x * u x) 2 volume := hu.mul' hηlp
  have hηdq : _root_.MeasureTheory.MemLp (fun x => η x * diffQuot k h u x) 2 volume :=
    (memLp_diffQuot_two k h hu).mul' hηlp
  have hηuSq : _root_.MeasureTheory.Integrable (fun x => (η x * u x)^2) volume := by
    exact (hηu.integrable_mul hηu).congr (Filter.Eventually.of_forall fun x => by simp [pow_two])
  have hηdqSq : _root_.MeasureTheory.Integrable (fun x => (η x * diffQuot k h u x)^2) volume := by
    exact (hηdq.integrable_mul hηdq).congr (Filter.Eventually.of_forall fun x => by simp [pow_two])
  have hR : _root_.MeasureTheory.Integrable (fun x =>
      (translate k h a x * diffQuot k h u x + diffQuot k h a x * u x) *
        (η x ^ 2 * diffQuot k h u x)) volume := by
    have ht := (memLp_diffQuot_two k h hau).integrable_mul (memLp_sq_mul_diffQuot hη hηc hu k h)
    exact ht.congr (Filter.Eventually.of_forall fun x => by simp [NirenbergEuclidean.diffQuot_mul])
  rw [integral_weight_mul_nirenbergTestFunction_eq hau hu hη hηc k h, neg_neg]
  calc
    _ = ∫ x, (lam / 2 * (η x * diffQuot k h u x)^2 -
      A^2 / (2 * lam) * (η x * u x)^2) := by
      rw [_root_.MeasureTheory.integral_sub (hηdqSq.const_mul _) (hηuSq.const_mul _), _root_.MeasureTheory.integral_const_mul,
        _root_.MeasureTheory.integral_const_mul]
    _ ≤ _ := _root_.MeasureTheory.integral_mono
      ((hηdqSq.const_mul _).sub (hηuSq.const_mul _)) hR
      (fun x => weighted_diffQuot_coercivity_pointwise k h hlam hA x (ha x) (hda x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.neg_integral_weight_mul_nirenbergTestFunction_ge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.neg_integral_weight_mul_nirenbergTestFunction_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.neg_integral_weight_mul_nirenbergTestFunction_ge ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.neg_integral_weight_mul_nirenbergTestFunction_ge

private theorem diffQuot_indicator_eq_on_cutoff
    {Ω : Set E} {η u : E → ℝ} (k : Fin d) (h : ℝ)
    (hηs : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω) {x : E} (hx : η x ≠ 0) :
    diffQuot k h (Ω.indicator u) x = diffQuot k h u x := by
  by_cases hh : h = 0
  · simp [hh]
  have hxs : x ∈ tsupport η := subset_tsupport η hx
  have hbase : x ∈ Ω := hηs (_root_.Metric.self_subset_cthickening _ hxs)
  have hshift : x + h • EuclideanSpace.single k (1 : ℝ) ∈ Ω := by
    apply hηs
    apply _root_.Metric.closedBall_subset_cthickening hxs |h|
    rw [_root_.Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    simp only [PiLp.norm_single, _root_.NormOneClass.norm_one, mul_one, Real.norm_eq_abs, le_refl]
  simp only [diffQuot_apply_of_ne k hh, _root_.Set.indicator_of_mem hbase, _root_.Set.indicator_of_mem hshift]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.diffQuot_indicator_eq_on_cutoff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.diffQuot_indicator_eq_on_cutoff target :: scope.openDecls } }

private theorem nirenbergTestFunction_indicator_eq
    {Ω : Set E} {η u : E → ℝ} (k : Fin d) (h : ℝ)
    (hηs : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    nirenbergTestFunction k h η (Ω.indicator u) = nirenbergTestFunction k h η u := by
  apply nirenbergTestFunction_congr_of_eqOn_cthickening
  intro x hx
  exact _root_.Set.indicator_of_mem (hηs hx) _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_indicator_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_indicator_eq target :: scope.openDecls } }

theorem integral_mul_nirenbergTestFunction_eq_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) {w v η : E → ℝ}
    (hw : _root_.MeasureTheory.MemLp w 2 (volume.restrict Ω)) (hv : _root_.MeasureTheory.MemLp v 2 (volume.restrict Ω))
    (hη : Continuous η) (hηc : HasCompactSupport η) (k : Fin d) (h : ℝ)
    (hηs : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    (∫ x in Ω, w x * nirenbergTestFunction k h η v x) =
      -∫ x, diffQuot k h w x * (η x ^ 2 * diffQuot k h v x) := by
  have hw0 : _root_.MeasureTheory.MemLp (Ω.indicator w) 2 volume := (_root_.MeasureTheory.memLp_indicator_iff_restrict hΩ).mpr hw
  have hv0 : _root_.MeasureTheory.MemLp (Ω.indicator v) 2 volume := (_root_.MeasureTheory.memLp_indicator_iff_restrict hΩ).mpr hv
  have hid := integral_mul_nirenbergTestFunction_eq hw0 hv0 hη hηc k h
  rw [nirenbergTestFunction_indicator_eq k h hηs] at hid
  have hleft : (∫ x, Ω.indicator w x * nirenbergTestFunction k h η v x) =
      ∫ x in Ω, w x * nirenbergTestFunction k h η v x := by
    rw [← _root_.MeasureTheory.integral_indicator hΩ]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Ω <;> simp [hx]
  rw [hleft] at hid
  rw [hid]
  congr 1
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards with x
  by_cases hx : η x = 0
  · simp [hx]
  · rw [diffQuot_indicator_eq_on_cutoff k h hηs hx,
      diffQuot_indicator_eq_on_cutoff k h hηs hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_mul_nirenbergTestFunction_eq_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_mul_nirenbergTestFunction_eq_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_mul_nirenbergTestFunction_eq_local ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_mul_nirenbergTestFunction_eq_local

theorem integral_weight_mul_nirenbergTestFunction_eq_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) {a u v η : E → ℝ}
    (hau : _root_.MeasureTheory.MemLp (fun x => a x * u x) 2 (volume.restrict Ω))
    (hv : _root_.MeasureTheory.MemLp v 2 (volume.restrict Ω))
    (hη : Continuous η) (hηc : HasCompactSupport η) (k : Fin d) (h : ℝ)
    (hηs : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    (∫ x in Ω, a x * u x * nirenbergTestFunction k h η v x) =
      -∫ x, (translate k h a x * diffQuot k h u x + diffQuot k h a x * u x) *
        (η x ^ 2 * diffQuot k h v x) := by
  rw [integral_mul_nirenbergTestFunction_eq_local hΩ hau hv hη hηc k h hηs]
  simp only [NirenbergEuclidean.diffQuot_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_weight_mul_nirenbergTestFunction_eq_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_weight_mul_nirenbergTestFunction_eq_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_weight_mul_nirenbergTestFunction_eq_local ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_weight_mul_nirenbergTestFunction_eq_local

theorem integral_self_nirenbergTestFunction_eq_neg_integral_sq_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) {u η : E → ℝ}
    (hu : _root_.MeasureTheory.MemLp u 2 (volume.restrict Ω))
    (hη : Continuous η) (hηc : HasCompactSupport η) (k : Fin d) (h : ℝ)
    (hηs : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    (∫ x in Ω, u x * nirenbergTestFunction k h η u x) =
      -∫ x, (η x * diffQuot k h u x) ^ 2 := by
  rw [integral_mul_nirenbergTestFunction_eq_local hΩ hu hu hη hηc k h hηs]
  congr 1
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards with x
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_self_nirenbergTestFunction_eq_neg_integral_sq_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_self_nirenbergTestFunction_eq_neg_integral_sq_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_self_nirenbergTestFunction_eq_neg_integral_sq_local ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_self_nirenbergTestFunction_eq_neg_integral_sq_local

theorem integral_mul_nirenbergTestFunction_comm_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) {u v η : E → ℝ}
    (hu : _root_.MeasureTheory.MemLp u 2 (volume.restrict Ω)) (hv : _root_.MeasureTheory.MemLp v 2 (volume.restrict Ω))
    (hη : Continuous η) (hηc : HasCompactSupport η) (k : Fin d) (h : ℝ)
    (hηs : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    (∫ x in Ω, u x * nirenbergTestFunction k h η v x) =
      ∫ x in Ω, v x * nirenbergTestFunction k h η u x := by
  rw [integral_mul_nirenbergTestFunction_eq_local hΩ hu hv hη hηc k h hηs,
    integral_mul_nirenbergTestFunction_eq_local hΩ hv hu hη hηc k h hηs]
  congr 1
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards with x
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_mul_nirenbergTestFunction_comm_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_mul_nirenbergTestFunction_comm_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_mul_nirenbergTestFunction_comm_local ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.integral_mul_nirenbergTestFunction_comm_local

theorem neg_integral_weight_mul_nirenbergTestFunction_ge_local
    {Ω : Set E} (hΩ : MeasurableSet Ω) {a u η : E → ℝ}
    (hu : _root_.MeasureTheory.MemLp u 2 (volume.restrict Ω))
    (hau : _root_.MeasureTheory.MemLp (fun x => a x * u x) 2 (volume.restrict Ω))
    (hη : Continuous η) (hηc : HasCompactSupport η) (k : Fin d) (h : ℝ)
    (hηs : _root_.Metric.cthickening |h| (tsupport η) ⊆ Ω)
    {lam A : ℝ} (hlam : 0 < lam) (hA : 0 ≤ A)
    (ha : ∀ x, η x ≠ 0 → lam ≤ translate k h a x)
    (hda : ∀ x, η x ≠ 0 → |diffQuot k h a x| ≤ A) :
    lam / 2 * (∫ x, (η x * diffQuot k h u x)^2) -
        A^2 / (2 * lam) * (∫ x, (η x * u x)^2) ≤
      -(∫ x in Ω, a x * u x * nirenbergTestFunction k h η u x) := by
  have hu0 : _root_.MeasureTheory.MemLp (Ω.indicator u) 2 volume := (_root_.MeasureTheory.memLp_indicator_iff_restrict hΩ).mpr hu
  have hau0 : _root_.MeasureTheory.MemLp (fun x => a x * Ω.indicator u x) 2 volume := by
    have ht : _root_.MeasureTheory.MemLp (Ω.indicator (fun x => a x * u x)) 2 volume :=
      (_root_.MeasureTheory.memLp_indicator_iff_restrict hΩ).mpr hau
    apply ht.ae_eq
    filter_upwards with x
    by_cases hx : x ∈ Ω <;> simp [hx]
  have ht := neg_integral_weight_mul_nirenbergTestFunction_ge hu0 hau0 hη hηc k h hlam hA ha hda
  have hDq : (fun x => (η x * diffQuot k h (Ω.indicator u) x)^2) =
      fun x => (η x * diffQuot k h u x)^2 := by
    funext x
    by_cases hx : η x = 0
    · simp [hx]
    · rw [diffQuot_indicator_eq_on_cutoff k h hηs hx]
  have hU : (fun x => (η x * Ω.indicator u x)^2) = fun x => (η x * u x)^2 := by
    funext x
    by_cases hx : η x = 0
    · simp [hx]
    · have hbase : x ∈ Ω := hηs (_root_.Metric.self_subset_cthickening _ (subset_tsupport η hx))
      rw [_root_.Set.indicator_of_mem hbase]
  rw [hDq, hU, nirenbergTestFunction_indicator_eq k h hηs] at ht
  have hleft : (∫ x, a x * Ω.indicator u x * nirenbergTestFunction k h η u x) =
      ∫ x in Ω, a x * u x * nirenbergTestFunction k h η u x := by
    rw [← _root_.MeasureTheory.integral_indicator hΩ]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Ω <;> simp [hx]
  rwa [hleft] at ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.neg_integral_weight_mul_nirenbergTestFunction_ge_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.neg_integral_weight_mul_nirenbergTestFunction_ge_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.neg_integral_weight_mul_nirenbergTestFunction_ge_local ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.neg_integral_weight_mul_nirenbergTestFunction_ge_local

end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
