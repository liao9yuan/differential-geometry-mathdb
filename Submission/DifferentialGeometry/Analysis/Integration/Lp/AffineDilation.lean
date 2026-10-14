import Submission.DifferentialGeometry.Analysis.Integration.Measure.Affine
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Affine
import Submission.DifferentialGeometry.Analysis.Integration.LpNorm
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.NNReal _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

variable {d : ℕ}
open _root_.MeasureTheory in
local notation "E" => EuclideanSpace ℝ (Fin d)

open _root_.MeasureTheory in
private theorem map_affine_le_volume_of_one_le (b : E) {r : ℝ} (hr : 1 ≤ r) :
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).map (fun x => b + r • x) ≤ volume := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  rw [Measure.map_add_smul_addHaar _root_.MeasureTheory.MeasureSpace.volume b hr0.ne']
  have hcoef : ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr0.le _))]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hr)
  calc
    _ ≤ (1 : ℝ≥0∞) • (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) := by gcongr
    _ = _ := one_smul _ _

run_cmd do
  let target := ``Submission.MeasureTheory.map_affine_le_volume_of_one_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.map_affine_le_volume_of_one_le target :: scope.openDecls } }

open _root_.MeasureTheory in
theorem eLpNorm_comp_add_smul_le_of_one_le
    {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} {f : E → F}
    (hf : _root_.MeasureTheory.MemLp f p _root_.MeasureTheory.MeasureSpace.volume) (b : E) {r : ℝ} (hr : 1 ≤ r) :
    eLpNorm (fun x => f (b + r • x)) p _root_.MeasureTheory.MeasureSpace.volume ≤ _root_.MeasureTheory.eLpNorm f p volume := by
  have hm := map_affine_le_volume_of_one_le b hr
  have hfm := hf.mono_measure hm
  change _root_.MeasureTheory.eLpNorm (f ∘ fun x => b + r • x) p _root_.MeasureTheory.MeasureSpace.volume ≤ _
  rw [← _root_.MeasureTheory.eLpNorm_map_measure hfm.aestronglyMeasurable
    ((_root_.MeasurableAdd.measurable_const_add b).comp (_root_.MeasurableConstSMul.measurable_const_smul r)).aemeasurable]
  exact _root_.MeasureTheory.eLpNorm_mono_measure f hm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.eLpNorm_comp_add_smul_le_of_one_le then
    throwError "Refusing to shadow existing declaration MeasureTheory.eLpNorm_comp_add_smul_le_of_one_le"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.eLpNorm_comp_add_smul_le_of_one_le ``Submission.MeasureTheory.eLpNorm_comp_add_smul_le_of_one_le

open _root_.MeasureTheory in
theorem tendsto_eLpNorm_comp_add_smul_sub_on_ball
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : _root_.MeasureTheory.MemLp f 2 _root_.MeasureTheory.MeasureSpace.volume) (c : E) (R : ℝ)
    {rn : ℕ → ℝ} (hrn : ∀ n, 1 ≤ rn n) (hrlim : _root_.Filter.Tendsto rn _root_.Filter.atTop (𝓝 1)) :
    _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => f ((1 - rn n) • c + rn n • x) - f x) 2
      (volume.restrict (Metric.ball c R))) _root_.Filter.atTop (𝓝 0) := by
  let μ := volume.restrict (Metric.ball c R)
  let _ : _root_.MeasureTheory.IsFiniteMeasure μ := _root_.MeasureTheory.isFiniteMeasure_restrict.mpr _root_.MeasureTheory.measure_ball_lt_top.ne
  let S (n : ℕ) (x : E) := (1 - rn n) • c + rn n • x
  have hSc (n : ℕ) : Continuous (S n) := by dsimp only [S]; fun_prop
  have hSlim (x : E) : _root_.Filter.Tendsto (fun n => S n x) _root_.Filter.atTop (𝓝 x) := by
    simpa only [S, sub_self, zero_smul, one_smul, zero_add] using
      (((tendsto_const_nhds (x := (1 : ℝ))).sub hrlim).smul_const c).add (hrlim.smul_const x)
  have hfm (n : ℕ) : _root_.MeasureTheory.MemLp (fun x => f (S n x)) 2 volume := by
    have h := hf.mono_measure (map_affine_le_volume_of_one_le ((1 - rn n) • c) (hrn n))
    exact h.comp_of_map (hSc n).measurable.aemeasurable
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  by_cases hεtop : ε = ∞
  · simp only [hεtop, le_top, _root_.Filter.eventually_true]
  let δ : ℝ := ε.toReal / 3
  have hδ : 0 < δ := div_pos (ENNReal.toReal_pos hε.ne' hεtop) (by norm_num)
  obtain ⟨g, hfg, hgm⟩ := hf.exists_boundedContinuous_eLpNorm_sub_le
    (by norm_num) (ENNReal.ofReal_pos.mpr hδ).ne'
  have hmidInt : _root_.Filter.Tendsto (fun n => ∫ x, ‖g (S n x) - g x‖ ^ 2 ∂μ) _root_.Filter.atTop (𝓝 0) := by
    have h := _root_.MeasureTheory.tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x => ‖g (S n x) - g x‖ ^ 2) (f := fun _ : E => (0 : ℝ))
      (fun _ : E => (2 * ‖g‖) ^ 2)
      (fun n => (((g.continuous.comp (hSc n)).sub g.continuous).norm.pow 2).aestronglyMeasurable)
      (_root_.MeasureTheory.integrable_const _) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · simpa only [_root_.MeasureTheory.integral_zero] using h
    · rw [norm_pow, norm_norm]
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (norm_sub_le _ _).trans (by
          change ‖g (S n x)‖ + ‖g x‖ ≤ 2 * ‖g‖
          linarith [g.norm_coe_le_norm (S n x), g.norm_coe_le_norm x])
    · simpa only [Function.comp_apply, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using
        (((g.continuous.tendsto x).comp (hSlim x)).sub (tendsto_const_nhds (x := g x))).norm.pow 2
  have hmid : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => g (S n x) - g x) 2 μ) _root_.Filter.atTop (𝓝 0) := by
    have hlim := (ENNReal.continuous_ofReal.tendsto (Real.sqrt 0)).comp
      (Real.continuous_sqrt.tendsto 0 |>.comp hmidInt)
    simp only [Real.sqrt_zero, ENNReal.ofReal_zero] at hlim
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    intro n
    have hm : _root_.MeasureTheory.MemLp (fun x => g (S n x) - g x) 2 μ := by
      apply MemLp.of_bound
        (((g.continuous.comp (hSc n)).sub g.continuous).aestronglyMeasurable) (2 * ‖g‖)
      exact Eventually.of_forall fun x =>
        (norm_sub_le _ _).trans (by
          change ‖g (S n x)‖ + ‖g x‖ ≤ 2 * ‖g‖
          linarith [g.norm_coe_le_norm (S n x), g.norm_coe_le_norm x])
    exact DifferentialGeometry.Analysis.Integration.eLpNorm_two_le_of_integral_norm_sq_le hm le_rfl
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hmid (ENNReal.ofReal δ)
    (ENNReal.ofReal_pos.mpr hδ)] with n hn
  have hfirst : _root_.MeasureTheory.eLpNorm (fun x => f (S n x) - g (S n x)) 2 μ ≤ ENNReal.ofReal δ :=
    (_root_.MeasureTheory.eLpNorm_mono_measure _ Measure.restrict_le_self).trans
      ((eLpNorm_comp_add_smul_le_of_one_le (hf.sub hgm) ((1 - rn n) • c) (hrn n)).trans hfg)
  have hlast : _root_.MeasureTheory.eLpNorm (fun x => g x - f x) 2 μ ≤ ENNReal.ofReal δ := by
    change _root_.MeasureTheory.eLpNorm ((g : E → F) - f) 2 μ ≤ _
    rw [_root_.MeasureTheory.eLpNorm_sub_comm]
    exact (_root_.MeasureTheory.eLpNorm_mono_measure _ Measure.restrict_le_self).trans hfg
  have hgmSn : _root_.MeasureTheory.MemLp (fun x => g (S n x)) 2 volume :=
    (hgm.mono_measure (map_affine_le_volume_of_one_le ((1 - rn n) • c) (hrn n))).comp_of_map
      (hSc n).measurable.aemeasurable
  have htri := _root_.MeasureTheory.eLpNorm_add_le
    (((hfm n).sub hgmSn).restrict (Metric.ball c R)).aestronglyMeasurable
    ((hgmSn.sub hgm).restrict (Metric.ball c R)).aestronglyMeasurable (by norm_num : 1 ≤ (2 : ℝ≥0∞))
  have htri' := _root_.MeasureTheory.eLpNorm_add_le
    ((((hfm n).sub hgmSn).add (hgmSn.sub hgm)).restrict (Metric.ball c R)).aestronglyMeasurable
    ((hgm.sub hf).restrict (Metric.ball c R)).aestronglyMeasurable (by norm_num : 1 ≤ (2 : ℝ≥0∞))
  have hbound : _root_.MeasureTheory.eLpNorm (fun x => f (S n x) - f x) 2 μ ≤
      ENNReal.ofReal δ + ENNReal.ofReal δ + ENNReal.ofReal δ := by
    calc
      _ = _root_.MeasureTheory.eLpNorm ((fun x => f (S n x) - g (S n x)) +
          (fun x => g (S n x) - g x) + (fun x => g x - f x)) 2 μ := by
        congr 1
        funext x
        simp only [Pi.add_apply, sub_add_sub_cancel]
      _ ≤ _ := htri'.trans (add_le_add (htri.trans (add_le_add hfirst hn)) hlast)
  apply hbound.trans
  rw [← ENNReal.ofReal_add hδ.le hδ.le, ← ENNReal.ofReal_add (by positivity) hδ.le,
    ← ENNReal.ofReal_toReal hεtop]
  apply ENNReal.ofReal_le_ofReal
  dsimp only [δ]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_eLpNorm_comp_add_smul_sub_on_ball then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_eLpNorm_comp_add_smul_sub_on_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_eLpNorm_comp_add_smul_sub_on_ball ``Submission.MeasureTheory.tendsto_eLpNorm_comp_add_smul_sub_on_ball

end MeasureTheory

end

end
