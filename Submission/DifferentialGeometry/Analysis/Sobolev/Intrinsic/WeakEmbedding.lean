import Submission.DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakChartSobolev
import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Embedding.Subcritical
import Submission.DifferentialGeometry.Analysis.Integration.EntropyLp

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

variable [CompactSpace M] [T2Space M] [I.Boundaryless]


theorem MemW1pIntrinsicLp.memLp_subcritical [NeZero (Module.finrank ℝ E)]
    {g : SmoothRiemannianMetric I M} {p : ℝ} (hp : 1 ≤ p)
    (hpdim : p < (Module.finrank ℝ E : ℝ)) {u : M → ℝ}
    (hu : MemW1pIntrinsicLp g (ENNReal.ofReal p) u) :
    _root_.MeasureTheory.MemLp u (ENNReal.ofReal
      ((Module.finrank ℝ E : ℝ) * p / ((Module.finrank ℝ E : ℝ) - p)))
      (riemannianVolumeMeasure I M g) := by
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  obtain ⟨hu, G, hG, hGn⟩ := hu
  let v : M → ℝ := hu.aestronglyMeasurable.mk u
  have huv : u =ᵐ[riemannianVolumeMeasure I M g] v := hu.aestronglyMeasurable.ae_eq_mk
  have hvmeas : Measurable v := hu.aestronglyMeasurable.measurable_mk
  have hv : MemW1pIntrinsicLp g (ENNReal.ofReal p) v :=
    ⟨hu.ae_eq huv, G, hG.congr_fun_ae huv, hGn⟩
  have hchart := hv.memWkpChart hpE
  obtain ⟨C, _hC, hbound⟩ := Chart.sobolev_closed g hp hpdim
  have hvLp : _root_.MeasureTheory.MemLp v (ENNReal.ofReal
      ((Module.finrank ℝ E : ℝ) * p / ((Module.finrank ℝ E : ℝ) - p)))
      (riemannianVolumeMeasure I M g) := by
    refine ⟨hvmeas.aestronglyMeasurable, ?_⟩
    exact (hbound hvmeas hchart).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Chart.wkpNormChart_lt_top_of_memWkpChart hpE hchart))
  exact hvLp.ae_eq huv.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp.memLp_subcritical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp.memLp_subcritical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp.memLp_subcritical ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp.memLp_subcritical


theorem MemW1pIntrinsicLp.exists_memLp_gt_two
    {g : SmoothRiemannianMetric I M} (hdim : 2 ≤ Module.finrank ℝ E)
    {u : M → ℝ} (hu : MemW1pIntrinsicLp g 2 u) :
    ∃ q : ℝ, 2 < q ∧ _root_.MeasureTheory.MemLp u (ENNReal.ofReal q) (riemannianVolumeMeasure I M g) := by
  let n : ℝ := Module.finrank ℝ E
  have hn : 2 ≤ n := by
    change (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ)
    exact_mod_cast hdim
  let p : ℝ := 2 * n / (n + 1)
  have hden : 0 < n + 1 := by linarith
  have hp : 1 ≤ p := (le_div_iff₀ hden).2 (by nlinarith)
  have hp2 : p ≤ 2 := (div_le_iff₀ hden).2 (by nlinarith)
  have hpdim : p < n := (div_lt_iff₀ hden).2 (by nlinarith)
  have hnd : 0 < n - p := sub_pos.mpr hpdim
  have hq : 2 < n * p / (n - p) := by
    apply (lt_div_iff₀ hnd).2
    have hpgt : 2 * n / (n + 2) < p := by
      dsimp only [p]
      apply (div_lt_div_iff₀ (by linarith) hden).2
      nlinarith
    have := (div_lt_iff₀ (by linarith : 0 < n + 2)).1 hpgt
    nlinarith
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hpE : ENNReal.ofReal p ≤ (2 : ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp2
  obtain ⟨hu, G, hG, hGn⟩ := hu
  have hup : MemW1pIntrinsicLp g (ENNReal.ofReal p) u :=
    ⟨hu.mono_exponent hpE, G, hG, hGn.mono_exponent hpE⟩
  exact ⟨_, hq, hup.memLp_subcritical hp hpdim⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp.exists_memLp_gt_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp.exists_memLp_gt_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp.exists_memLp_gt_two ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp.exists_memLp_gt_two


theorem MemW1pIntrinsicLp.integrable_sq_mul_log_sq
    {g : SmoothRiemannianMetric I M} (hdim : 2 ≤ Module.finrank ℝ E)
    {u : M → ℝ} (hu : MemW1pIntrinsicLp g 2 u) :
    Integrable (fun x => u x ^ 2 * Real.log (u x ^ 2)) (riemannianVolumeMeasure I M g) := by
  let : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  obtain ⟨q, hq, huq⟩ := hu.exists_memLp_gt_two hdim
  exact Integration.integrable_sq_mul_log_sq_of_memLp hq huq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp.integrable_sq_mul_log_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp.integrable_sq_mul_log_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp.integrable_sq_mul_log_sq ``Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicLp.MemW1pIntrinsicLp.integrable_sq_mul_log_sq

end DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
