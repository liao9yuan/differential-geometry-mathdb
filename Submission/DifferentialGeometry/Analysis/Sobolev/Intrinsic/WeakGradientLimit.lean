import Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakGradientUnique
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.PositiveDefiniteBilinearQuadraticLowerBound
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.LpSpace.Complete

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.instBorelSpace_differentialGeometry target :: scope.openDecls } }

private lemma norm_le_mul_sqrt_inner (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : TangentSpace I x,
      ‖v‖ ≤ C * Real.sqrt (g.inner x v v) := by
  obtain ⟨c, hc, hbound⟩ := posDef_bilin_quadratic_lower_bound (g.inner x) (g.pos x)
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  refine ⟨(Real.sqrt c)⁻¹, inv_pos.mpr hsqrt, fun v => ?_⟩
  have h := Real.sqrt_le_sqrt (hbound v)
  rw [Real.sqrt_mul hc.le, Real.sqrt_sq_eq_abs, abs_norm] at h
  calc
    ‖v‖ ≤ Real.sqrt (g.inner x v v) / Real.sqrt c :=
      (le_div_iff₀ hsqrt).2 (by simpa only [mul_comm] using h)
    _ = (Real.sqrt c)⁻¹ * Real.sqrt (g.inner x v v) := by ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.norm_le_mul_sqrt_inner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.norm_le_mul_sqrt_inner target :: scope.openDecls } }


theorem exists_ae_tendsto_of_summable_metric_steps [CompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (V : ℕ → ∀ x : M, TangentSpace I x)
    (hV : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (fun x => Real.sqrt
      (g.inner x (V (n + 1) x - V n x) (V (n + 1) x - V n x)))
      (riemannianVolumeMeasure I M g))
    (hsum : (∑' n, _root_.MeasureTheory.eLpNorm (fun x => Real.sqrt
      (g.inner x (V (n + 1) x - V n x) (V (n + 1) x - V n x))) 2
      (riemannianVolumeMeasure I M g)) ≠ ⊤) :
    ∃ G : ∀ x : M, TangentSpace I x,
      ∀ᵐ x ∂riemannianVolumeMeasure I M g, _root_.Filter.Tendsto (fun n => V n x) _root_.Filter.atTop (𝓝 (G x)) := by
  have hseries := _root_.MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1 : ℝ≥0∞) ≤ 2) hV hsum
  have hpoint : ∀ᵐ x ∂riemannianVolumeMeasure I M g,
      ∃ v : TangentSpace I x, _root_.Filter.Tendsto (fun n => V n x) _root_.Filter.atTop (𝓝 v) := by
    filter_upwards [hseries] with x hx
    have hx' : Summable (fun n => Real.sqrt
        (g.inner x (V (n + 1) x - V n x) (V (n + 1) x - V n x))) := by
      simpa only [Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hx
    obtain ⟨C, hC, hbound⟩ := norm_le_mul_sqrt_inner g x
    have hnorm : Summable (fun n => _root_.Dist.dist (V n x) (V (n + 1) x)) :=
      Summable.of_nonneg_of_le (fun _ => dist_nonneg)
        (fun n => by simpa only [dist_eq_norm, norm_sub_rev] using hbound (V (n + 1) x - V n x))
        (hx'.mul_left C)
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hnorm)
  classical
  let G : ∀ x : M, TangentSpace I x := fun x =>
    if hx : ∃ v : TangentSpace I x, _root_.Filter.Tendsto (fun n => V n x) _root_.Filter.atTop (𝓝 v) then hx.choose else 0
  refine ⟨G, ?_⟩
  filter_upwards [hpoint] with x hx
  simpa only [G, dif_pos hx] using hx.choose_spec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.exists_ae_tendsto_of_summable_metric_steps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.exists_ae_tendsto_of_summable_metric_steps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.exists_ae_tendsto_of_summable_metric_steps ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.exists_ae_tendsto_of_summable_metric_steps


theorem eLpNorm_metric_sub_limit_le [CompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) {V : ℕ → ∀ x : M, TangentSpace I x}
    {G W : ∀ x : M, TangentSpace I x}
    (hV : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (fun x => Real.sqrt
      (g.inner x (W x - V n x) (W x - V n x))) (riemannianVolumeMeasure I M g))
    (hlim : ∀ᵐ x ∂riemannianVolumeMeasure I M g,
      _root_.Filter.Tendsto (fun n => V n x) _root_.Filter.atTop (𝓝 (G x)))
    {C : ℝ≥0∞} (hbound : ∀ᶠ n in _root_.Filter.atTop, _root_.MeasureTheory.eLpNorm (fun x => Real.sqrt
      (g.inner x (W x - V n x) (W x - V n x))) 2 (riemannianVolumeMeasure I M g) ≤ C) :
    _root_.MeasureTheory.eLpNorm (fun x => Real.sqrt (g.inner x (W x - G x) (W x - G x))) 2
      (riemannianVolumeMeasure I M g) ≤ C := by
  apply Lp.eLpNorm_le_of_ae_tendsto hbound hV
  filter_upwards [hlim] with x hx
  have hcont : Continuous (fun v : TangentSpace I x =>
      Real.sqrt (g.inner x (W x - v) (W x - v))) :=
    Real.continuous_sqrt.comp
      (((g.inner x).continuous.comp (continuous_const.sub continuous_id)).clm_apply
        (continuous_const.sub continuous_id))
  exact (hcont.tendsto _).comp hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.eLpNorm_metric_sub_limit_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.eLpNorm_metric_sub_limit_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.eLpNorm_metric_sub_limit_le ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.eLpNorm_metric_sub_limit_le


theorem exists_metricL2_limit_of_summable_steps [CompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (V : ℕ → ∀ x : M, TangentSpace I x)
    (hV : ∀ n m, _root_.MeasureTheory.AEStronglyMeasurable (fun x => Real.sqrt
      (g.inner x (V n x - V m x) (V n x - V m x))) (riemannianVolumeMeasure I M g))
    (hsum : (∑' n, _root_.MeasureTheory.eLpNorm (fun x => Real.sqrt
      (g.inner x (V (n + 1) x - V n x) (V (n + 1) x - V n x))) 2
      (riemannianVolumeMeasure I M g)) ≠ ⊤)
    {r : ℕ → ℝ≥0∞} (hr : _root_.Filter.Tendsto r _root_.Filter.atTop (𝓝 0))
    (hbound : ∀ n, ∀ᶠ m in _root_.Filter.atTop, _root_.MeasureTheory.eLpNorm (fun x => Real.sqrt
      (g.inner x (V n x - V m x) (V n x - V m x))) 2
      (riemannianVolumeMeasure I M g) ≤ r n) :
    ∃ G : ∀ x : M, TangentSpace I x,
      (∀ᵐ x ∂riemannianVolumeMeasure I M g, _root_.Filter.Tendsto (fun n => V n x) _root_.Filter.atTop (𝓝 (G x))) ∧
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => Real.sqrt
        (g.inner x (V n x - G x) (V n x - G x))) 2 (riemannianVolumeMeasure I M g))
        atTop (𝓝 0) := by
  obtain ⟨G, hlim⟩ := exists_ae_tendsto_of_summable_metric_steps g V
    (fun n => hV (n + 1) n) hsum
  refine ⟨G, hlim, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr (fun _ => bot_le)
  intro n
  exact eLpNorm_metric_sub_limit_le g (hV n) hlim (hbound n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.exists_metricL2_limit_of_summable_steps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.exists_metricL2_limit_of_summable_steps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.exists_metricL2_limit_of_summable_steps ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.exists_metricL2_limit_of_summable_steps

end DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
