import Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic.Equivalence.IntrinsicToChart.ComponentNormBound

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


theorem eLpNorm_subcritical_le_metricL2_smooth [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hpdim : p < (Module.finrank ℝ E : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ) ∞ u →
      _root_.MeasureTheory.eLpNorm u (ENNReal.ofReal
        ((Module.finrank ℝ E : ℝ) * p / ((Module.finrank ℝ E : ℝ) - p)))
          (riemannianVolumeMeasure I M g) ≤ C *
        (_root_.MeasureTheory.eLpNorm u 2 (riemannianVolumeMeasure I M g) +
          _root_.MeasureTheory.eLpNorm (fun x => Real.sqrt (g.inner x (gradFun g u x) (gradFun g u x))) 2
            (riemannianVolumeMeasure I M g)) := by
  let μ := riemannianVolumeMeasure I M g
  let : _root_.MeasureTheory.IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hpE2 : ENNReal.ofReal p ≤ (2 : ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp2
  let a : ℝ := 1 / (ENNReal.ofReal p).toReal - 1 / (2 : ℝ≥0∞).toReal
  have ha : 0 ≤ a := by
    dsimp only [a]
    rw [ENNReal.toReal_ofReal hp0.le, ENNReal.toReal_ofNat]
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hp0 hp2)
  let V : ℝ≥0∞ := μ _root_.Set.univ ^ a
  have hV : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ha (_root_.MeasureTheory.measure_ne_top μ _root_.Set.univ)
  obtain ⟨Cs, _hCs, hSobolev⟩ := Chart.sobolev_closed g hp hpdim
  obtain ⟨Cr, _hCr, hReverse⟩ :=
    EquivalenceReverse.wkpNormChart_le_const_mul_intrinsicLpComponents_smooth_uniform
      g hpE ENNReal.ofReal_ne_top
  refine ⟨ENNReal.ofReal Cs * ENNReal.ofReal Cr * V,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hV,
    fun {u} hu => ?_⟩
  have hchart := Equivalence.MemWkpChart_of_contMDiff hpE hu
  have hscalar : _root_.MeasureTheory.eLpNorm u (ENNReal.ofReal p) μ ≤ _root_.MeasureTheory.eLpNorm u 2 μ * V :=
    _root_.MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpE2 hu.continuous.aestronglyMeasurable
  have hgradient : _root_.MeasureTheory.eLpNorm (fun x => Real.sqrt (g.inner x (gradFun g u x) (gradFun g u x)))
      (ENNReal.ofReal p) μ ≤
      eLpNorm (fun x => Real.sqrt (g.inner x (gradFun g u x) (gradFun g u x))) 2 μ * V :=
    _root_.MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpE2
      (Equivalence.continuous_g_norm_gradFun g hu).aestronglyMeasurable
  calc
    _ ≤ ENNReal.ofReal Cs * Chart.wkpNormChart (I := I) 1 (ENNReal.ofReal p) u :=
      hSobolev hu.continuous.measurable hchart
    _ ≤ ENNReal.ofReal Cs * (ENNReal.ofReal Cr *
        (_root_.MeasureTheory.eLpNorm u (ENNReal.ofReal p) μ + _root_.MeasureTheory.eLpNorm (fun x => Real.sqrt
          (g.inner x (gradFun g u x) (gradFun g u x))) (ENNReal.ofReal p) μ)) := by
      gcongr
      exact hReverse hu
    _ ≤ ENNReal.ofReal Cs * (ENNReal.ofReal Cr *
        (_root_.MeasureTheory.eLpNorm u 2 μ * V + _root_.MeasureTheory.eLpNorm (fun x => Real.sqrt
          (g.inner x (gradFun g u x) (gradFun g u x))) 2 μ * V)) :=
      mul_le_mul_right (mul_le_mul_right (add_le_add hscalar hgradient) _) _
    _ = _ := by rw [← add_mul]; ac_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.eLpNorm_subcritical_le_metricL2_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.eLpNorm_subcritical_le_metricL2_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.eLpNorm_subcritical_le_metricL2_smooth ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.eLpNorm_subcritical_le_metricL2_smooth


theorem exists_eLpNorm_gt_two_bound_smooth
    (g : SmoothRiemannianMetric I M) (hdim : 2 ≤ Module.finrank ℝ E) :
    ∃ q : ℝ, 2 < q ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ) ∞ u →
        _root_.MeasureTheory.eLpNorm u (ENNReal.ofReal q) (riemannianVolumeMeasure I M g) ≤ C *
          (_root_.MeasureTheory.eLpNorm u 2 (riemannianVolumeMeasure I M g) +
            _root_.MeasureTheory.eLpNorm (fun x => Real.sqrt (g.inner x (gradFun g u x) (gradFun g u x))) 2
              (riemannianVolumeMeasure I M g)) := by
  let n : ℝ := Module.finrank ℝ E
  have hn : 2 ≤ n := by
    change (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ)
    exact_mod_cast hdim
  let p : ℝ := 2 * n / (n + 1)
  have hden : 0 < n + 1 := by linarith
  have hp : 1 ≤ p := (le_div_iff₀ hden).2 (by nlinarith)
  have hp2 : p ≤ 2 := (div_le_iff₀ hden).2 (by nlinarith)
  have hpdim : p < n := (div_lt_iff₀ hden).2 (by nlinarith)
  have hq : 2 < n * p / (n - p) := by
    apply (lt_div_iff₀ (sub_pos.mpr hpdim)).2
    have hpgt : 2 * n / (n + 2) < p := by
      dsimp only [p]
      apply (div_lt_div_iff₀ (by linarith) hden).2
      nlinarith
    have := (div_lt_iff₀ (by linarith : 0 < n + 2)).1 hpgt
    nlinarith
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  obtain ⟨C, hC, hbound⟩ := eLpNorm_subcritical_le_metricL2_smooth g hp hp2 hpdim
  exact ⟨_, hq, C, hC, hbound⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.exists_eLpNorm_gt_two_bound_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.exists_eLpNorm_gt_two_bound_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.exists_eLpNorm_gt_two_bound_smooth ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.exists_eLpNorm_gt_two_bound_smooth

end DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
