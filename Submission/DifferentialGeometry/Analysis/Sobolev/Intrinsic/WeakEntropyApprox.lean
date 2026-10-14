import Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakSmoothDensity
import Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic.SmoothSobolevBound
import Submission.DifferentialGeometry.Analysis.Integration.EntropyUniform
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

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
open _root_.Submission.DifferentialGeometry.Geometry.Operator

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

variable [CompactSpace M] [T2Space M] [I.Boundaryless]


theorem HasWeakRiemannianGradLp.exists_smooth_entropy_integrals_approx
    {g : SmoothRiemannianMetric I M} (hdim : 2 ≤ Module.finrank ℝ E)
    {u : M → ℝ} {G : ∀ x : M, TangentSpace I x}
    (hG : HasWeakRiemannianGradLp g u G)
    (hu : _root_.MeasureTheory.MemLp u 2 (riemannianVolumeMeasure I M g))
    (hGn : _root_.MeasureTheory.MemLp (fun x => Real.sqrt (g.inner x (G x) (G x))) 2
      (riemannianVolumeMeasure I M g))
    {R : M → ℝ} (hR : Continuous R) :
    ∃ f : ℕ → M → ℝ, (∀ n, ContMDiff I 𝓘(ℝ) ∞ (f n)) ∧
      _root_.Filter.Tendsto (fun n => ∫ x, f n x ^ 2 ∂riemannianVolumeMeasure I M g) _root_.Filter.atTop
        (𝓝 (∫ x, u x ^ 2 ∂riemannianVolumeMeasure I M g)) ∧
      _root_.Filter.Tendsto (fun n => ∫ x, g.inner x (gradFun g (f n) x) (gradFun g (f n) x)
        ∂riemannianVolumeMeasure I M g) _root_.Filter.atTop
        (𝓝 (∫ x, g.inner x (G x) (G x) ∂riemannianVolumeMeasure I M g)) ∧
      _root_.Filter.Tendsto (fun n => ∫ x, R x * f n x ^ 2 ∂riemannianVolumeMeasure I M g) _root_.Filter.atTop
        (𝓝 (∫ x, R x * u x ^ 2 ∂riemannianVolumeMeasure I M g)) ∧
      _root_.Filter.Tendsto (fun n => ∫ x, f n x ^ 2 * Real.log (f n x ^ 2)
        ∂riemannianVolumeMeasure I M g) _root_.Filter.atTop
        (𝓝 (∫ x, u x ^ 2 * Real.log (u x ^ 2) ∂riemannianVolumeMeasure I M g)) := by
  let μ := riemannianVolumeMeasure I M g
  let : _root_.MeasureTheory.IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  obtain ⟨f, hf, hscalar, hpointG, hmetric⟩ := hG.exists_smooth_metricL2_approx hu hGn
  have hfn (n : ℕ) : _root_.MeasureTheory.MemLp (f n) 2 μ := (MemW1pIntrinsicLp_of_contMDiff g 2 (hf n)).1
  have hgrad (n : ℕ) : _root_.MeasureTheory.MemLp (fun x => Real.sqrt
      (g.inner x (gradFun g (f n) x) (gradFun g (f n) x))) 2 μ :=
    Equivalence.memLp_g_norm_gradFun_smooth g 2 (hf n)
  obtain ⟨Cv, hCv, hvbound⟩ := Integration.exists_eLpNorm_bound_of_tendsto_two hfn hu hscalar
  have hnorm := tendsto_eLpNorm_metric_norm_sub_of_metricL2_tendsto g hmetric
  obtain ⟨Cg, hCg, hgbound⟩ := Integration.exists_eLpNorm_bound_of_tendsto_two hgrad hGn hnorm
  obtain ⟨q, hq, C, hC, hSobolev⟩ := exists_eLpNorm_gt_two_bound_smooth g hdim
  let B : ℝ≥0∞ := C * (Cv + Cg)
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top hC (ENNReal.add_ne_top.mpr ⟨hCv, hCg⟩)
  have hqbound (n : ℕ) : _root_.MeasureTheory.eLpNorm (f n) (ENNReal.ofReal q) μ ≤ B :=
    (hSobolev (hf n)).trans (mul_le_mul_right (add_le_add (hvbound n) (hgbound n)) C)
  have hInMeasure := _root_.MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (fun n => (hf n).continuous.aestronglyMeasurable) hu.aestronglyMeasurable hscalar
  obtain ⟨s, hs, hpoint⟩ := hInMeasure.exists_seq_tendsto_ae
  have huq : _root_.MeasureTheory.MemLp u (ENNReal.ofReal q) μ := by
    refine ⟨hu.aestronglyMeasurable, ?_⟩
    exact (Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall fun n => hqbound (s n))
      (fun n => (hf (s n)).continuous.aestronglyMeasurable) hpoint).trans_lt hB.lt_top
  have hentropy := Integration.tendsto_integral_sq_mul_log_sq_of_eLpNorm_bdd hq
    (fun n => (hf (s n)).continuous.aestronglyMeasurable) huq hB
    (fun n => hqbound (s n)) hpoint
  have hmass := Integration.tendsto_integral_sq_of_eLpNorm_two hfn hu hscalar
  have hRtop : _root_.MeasureTheory.MemLp R ⊤ μ := hR.memLp_top_of_hasCompactSupport (isClosed_tsupport _).isCompact μ
  have hweighted := Integration.tendsto_integral_weighted_sq_of_eLpNorm_two hfn hu hRtop hscalar
  let V (n : ℕ) : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := gradG g ⟨f n, hf n⟩
  have hV (n : ℕ) (x : M) : V n x = gradFun g (f n) x := grad_g_apply g ⟨f n, hf n⟩ x
  have hpointV : ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun n => V n x) _root_.Filter.atTop (𝓝 (G x)) := by
    simpa only [hV] using hpointG
  have hmetricV : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => Real.sqrt
      (g.inner x (V n x - G x) (V n x - G x))) 2 μ) _root_.Filter.atTop (𝓝 0) := by
    simpa only [hV] using hmetric
  have henergy : _root_.Filter.Tendsto (fun n => ∫ x, g.inner x (gradFun g (f n) x) (gradFun g (f n) x) ∂μ)
      atTop (𝓝 (∫ x, g.inner x (G x) (G x) ∂μ)) := by
    simpa only [hV] using tendsto_integral_metric_energy_of_smooth_limit g V hpointV hmetricV
  exact ⟨fun n => f (s n), fun n => hf (s n), hmass.comp hs.tendsto_atTop,
    henergy.comp hs.tendsto_atTop, hweighted.comp hs.tendsto_atTop, hentropy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.exists_smooth_entropy_integrals_approx then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.exists_smooth_entropy_integrals_approx"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.exists_smooth_entropy_integrals_approx ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.HasWeakRiemannianGradLp.exists_smooth_entropy_integrals_approx

end DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
