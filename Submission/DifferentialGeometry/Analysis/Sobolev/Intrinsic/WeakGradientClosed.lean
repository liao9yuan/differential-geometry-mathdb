import Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakGradientLimit
import Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakProduct
import Submission.DifferentialGeometry.Analysis.Integration.L2Convergence

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
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

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

private lemma abs_sqrt_inner_sub_le (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    |Real.sqrt (g.inner x v v) - Real.sqrt (g.inner x w w)| ≤
      Real.sqrt (g.inner x (v - w) (v - w)) := by
  have hsym : Real.sqrt (g.inner x (w - v) (w - v)) =
      Real.sqrt (g.inner x (v - w) (v - w)) := by
    have heq : w - v = (-1 : ℝ) • (v - w) := by simp
    rw [heq, Geometry.Riemannian.sqrt_inner_smul]
    norm_num
  have hv := Geometry.Riemannian.sqrt_inner_add_le g x (v - w) w
  have hw := Geometry.Riemannian.sqrt_inner_add_le g x (w - v) v
  rw [sub_add_cancel] at hv hw
  rw [hsym] at hw
  exact abs_le.mpr ⟨by linarith, by linarith⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.abs_sqrt_inner_sub_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.abs_sqrt_inner_sub_le target :: scope.openDecls } }

omit [Module.Finite ℝ E] in
private lemma continuous_fiber_metric_norm (g : SmoothRiemannianMetric I M) (x : M) :
    Continuous (fun v : TangentSpace I x => Real.sqrt (g.inner x v v)) :=
  Real.continuous_sqrt.comp ((g.inner x).continuous.clm_apply continuous_id)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.continuous_fiber_metric_norm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.continuous_fiber_metric_norm target :: scope.openDecls } }

variable [CompactSpace M] [T2Space M]


theorem tendsto_eLpNorm_metric_norm_sub_of_metricL2_tendsto
    (g : SmoothRiemannianMetric I M) {V : ℕ → ∀ x : M, TangentSpace I x}
    {G : ∀ x : M, TangentSpace I x}
    (hmetric : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => Real.sqrt
      (g.inner x (V n x - G x) (V n x - G x))) 2
      (riemannianVolumeMeasure I M g)) _root_.Filter.atTop (𝓝 0)) :
    _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => Real.sqrt (g.inner x (V n x) (V n x)) -
      Real.sqrt (g.inner x (G x) (G x))) 2 (riemannianVolumeMeasure I M g)) _root_.Filter.atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmetric (fun _ => bot_le)
  intro n
  apply _root_.MeasureTheory.eLpNorm_mono_ae
  filter_upwards with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using
    abs_sqrt_inner_sub_le g x (V n x) (G x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.tendsto_eLpNorm_metric_norm_sub_of_metricL2_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.tendsto_eLpNorm_metric_norm_sub_of_metricL2_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.tendsto_eLpNorm_metric_norm_sub_of_metricL2_tendsto ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.tendsto_eLpNorm_metric_norm_sub_of_metricL2_tendsto


theorem memLp_metric_norm_of_smooth_limit (g : SmoothRiemannianMetric I M)
    (V : ℕ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {G : ∀ x : M, TangentSpace I x}
    (hpoint : ∀ᵐ x ∂riemannianVolumeMeasure I M g,
      _root_.Filter.Tendsto (fun n => V n x) _root_.Filter.atTop (𝓝 (G x)))
    (hmetric : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => Real.sqrt
      (g.inner x (V n x - G x) (V n x - G x))) 2
      (riemannianVolumeMeasure I M g)) _root_.Filter.atTop (𝓝 0)) :
    _root_.MeasureTheory.MemLp (fun x => Real.sqrt (g.inner x (G x) (G x))) 2
      (riemannianVolumeMeasure I M g) := by
  let μ := riemannianVolumeMeasure I M g
  let : _root_.MeasureTheory.IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hV (n : ℕ) : Continuous (fun x => Real.sqrt (g.inner x (V n x) (V n x))) :=
    Real.continuous_sqrt.comp (TangentBundle.continuous_g_inner_of_smooth_sections g (V n) (V n))
  have hmeas : _root_.MeasureTheory.AEStronglyMeasurable (fun x => Real.sqrt (g.inner x (G x) (G x))) μ := by
    apply aestronglyMeasurable_of_tendsto_ae _root_.Filter.atTop (fun n => (hV n).aestronglyMeasurable)
    filter_upwards [hpoint] with x hx
    exact ((continuous_fiber_metric_norm g x).tendsto _).comp hx
  apply Lp.memLp_of_cauchy_tendsto (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (fun n => (hV n).memLp_of_hasCompactSupport (isClosed_tsupport _).isCompact) _ hmeas
  exact tendsto_eLpNorm_metric_norm_sub_of_metricL2_tendsto g hmetric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.memLp_metric_norm_of_smooth_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.memLp_metric_norm_of_smooth_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.memLp_metric_norm_of_smooth_limit ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.memLp_metric_norm_of_smooth_limit


theorem HasWeakRiemannianGradLp.of_metricL2_limit [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {f : ℕ → M → ℝ} {u : M → ℝ}
    (V : ℕ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {G : ∀ x : M, TangentSpace I x}
    (hf : ∀ n, _root_.MeasureTheory.MemLp (f n) 2 (riemannianVolumeMeasure I M g))
    (hu : _root_.MeasureTheory.MemLp u 2 (riemannianVolumeMeasure I M g))
    (hweak : ∀ n, HasWeakRiemannianGradLp g (f n) (fun x => V n x))
    (hpoint : ∀ᵐ x ∂riemannianVolumeMeasure I M g,
      _root_.Filter.Tendsto (fun n => V n x) _root_.Filter.atTop (𝓝 (G x)))
    (hscalar : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => f n x - u x) 2
      (riemannianVolumeMeasure I M g)) _root_.Filter.atTop (𝓝 0))
    (hmetric : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => Real.sqrt
      (g.inner x (V n x - G x) (V n x - G x))) 2
      (riemannianVolumeMeasure I M g)) _root_.Filter.atTop (𝓝 0)) :
    HasWeakRiemannianGradLp g u G := by
  let μ := riemannianVolumeMeasure I M g
  let : _root_.MeasureTheory.IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hpair (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
      AEStronglyMeasurable (fun x => g.inner x (G x) (X x)) μ := by
    apply aestronglyMeasurable_of_tendsto_ae _root_.Filter.atTop (fun n => (hweak n).1 X)
    filter_upwards [hpoint] with x hx
    exact (((g.inner x).continuous.clm_apply continuous_const).tendsto (G x)).comp hx
  refine ⟨hpair, fun X hX => ?_⟩
  have hXcont : Continuous (fun x => Real.sqrt (g.inner x (X x) (X x))) :=
    Real.continuous_sqrt.comp (TangentBundle.continuous_g_inner_of_smooth_sections g X X)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hXcont.continuousOn
  have hpair2 : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm
      (fun x => g.inner x (V n x) (X x) - g.inner x (G x) (X x)) 2 μ) _root_.Filter.atTop (𝓝 0) := by
    have hboundlim : _root_.Filter.Tendsto (fun n => ENNReal.ofReal C * _root_.MeasureTheory.eLpNorm (fun x => Real.sqrt
        (g.inner x (V n x - G x) (V n x - G x))) 2 μ) _root_.Filter.atTop (𝓝 0) := by
      simpa only [_root_.MulZeroClass.mul_zero] using ENNReal.Tendsto.const_mul hmetric (Or.inr ENNReal.ofReal_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hboundlim
      (fun _ => bot_le)
    intro n
    apply _root_.MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have heq : g.inner x (V n x) (X x) - g.inner x (G x) (X x) =
        g.inner x (V n x - G x) (X x) := by rw [map_sub, sub_apply]
    rw [heq]
    calc
      |g.inner x (V n x - G x) (X x)| ≤
          Real.sqrt (g.inner x (V n x - G x) (V n x - G x)) *
            Real.sqrt (g.inner x (X x) (X x)) :=
        EquivalenceReverse.abs_g_inner_le_sqrt_mul_sqrt g x (V n x - G x) (X x)
      _ ≤ Real.sqrt (g.inner x (V n x - G x) (V n x - G x)) * C := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        simpa only [Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hC x (_root_.Set.mem_univ x)
      _ = C * Real.sqrt (g.inner x (V n x - G x) (V n x - G x)) := mul_comm _ _
  have hpair1 := Integration.tendsto_eLpNorm_one_of_two
    (fun n => ((hweak n).1 X).sub (hpair X)) hpair2
  have hleft : _root_.Filter.Tendsto (fun n => ∫ x, g.inner x (V n x) (X x) ∂μ) _root_.Filter.atTop
      (𝓝 (∫ x, g.inner x (G x) (X x) ∂μ)) :=
    _root_.MeasureTheory.tendsto_integral_of_L1' _ (hpair X) (Eventually.of_forall fun n =>
      (TangentBundle.continuous_g_inner_of_smooth_sections g (V n) X).integrable_of_hasCompactSupport
        (isClosed_tsupport _).isCompact) hpair1
  have hdiv : _root_.MeasureTheory.MemLp (divergenceG g X) 2 μ :=
    (divergence_g_contMDiff g X).continuous.memLp_of_hasCompactSupport
      (isClosed_tsupport _).isCompact
  have hright := (Integration.tendsto_integral_mul_of_eLpNorm_two hf hu hdiv hscalar).neg
  have heq : (fun n => ∫ x, g.inner x (V n x) (X x) ∂μ) =
      (fun n => -(∫ x, f n x * divergenceG g X x ∂μ)) :=
    funext fun n => (hweak n).pairing_eq X hX
  rw [← heq] at hright
  exact tendsto_nhds_unique hleft hright

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.of_metricL2_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.of_metricL2_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.of_metricL2_limit ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.of_metricL2_limit


theorem tendsto_integral_metric_energy_of_smooth_limit (g : SmoothRiemannianMetric I M)
    (V : ℕ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {G : ∀ x : M, TangentSpace I x}
    (hpoint : ∀ᵐ x ∂riemannianVolumeMeasure I M g,
      _root_.Filter.Tendsto (fun n => V n x) _root_.Filter.atTop (𝓝 (G x)))
    (hmetric : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => Real.sqrt
      (g.inner x (V n x - G x) (V n x - G x))) 2
      (riemannianVolumeMeasure I M g)) _root_.Filter.atTop (𝓝 0)) :
    _root_.Filter.Tendsto (fun n => ∫ x, g.inner x (V n x) (V n x) ∂riemannianVolumeMeasure I M g)
      atTop (𝓝 (∫ x, g.inner x (G x) (G x) ∂riemannianVolumeMeasure I M g)) := by
  let μ := riemannianVolumeMeasure I M g
  let : _root_.MeasureTheory.IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hV (n : ℕ) : _root_.MeasureTheory.MemLp (fun x => Real.sqrt (g.inner x (V n x) (V n x))) 2 μ :=
    (Real.continuous_sqrt.comp (TangentBundle.continuous_g_inner_of_smooth_sections g (V n) (V n))).memLp_of_hasCompactSupport
      (isClosed_tsupport _).isCompact
  have hG := memLp_metric_norm_of_smooth_limit g V hpoint hmetric
  have hnorm := tendsto_eLpNorm_metric_norm_sub_of_metricL2_tendsto g hmetric
  have hnonneg (x : M) (v : TangentSpace I x) : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  simpa only [Real.sq_sqrt (hnonneg _ _)] using
    Integration.tendsto_integral_sq_of_eLpNorm_two hV hG hnorm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.tendsto_integral_metric_energy_of_smooth_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.tendsto_integral_metric_energy_of_smooth_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.tendsto_integral_metric_energy_of_smooth_limit ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.tendsto_integral_metric_energy_of_smooth_limit

end DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
