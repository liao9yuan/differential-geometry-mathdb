import Submission.DifferentialGeometry.Analysis.Integration.Measure.VolumeDensity
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Mathlib.MeasureTheory.Integral.Prod

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.Integral.Measure
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem integrable_riemannianVolumeMeasure_iff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (q h : SmoothRiemannianMetric I M) (f : M → F) :
    Integrable f (riemannianVolumeMeasure (I := I) (M := M) h) ↔
      Integrable (fun x => riemannianVolumeDensity q h x • f x) (riemannianVolumeMeasure (I := I) (M := M) q) := by
  rw [riemannianVolumeMeasure_eq_withDensity q h]
  have hρ := (riemannianVolumeDensity_contMDiff q h).continuous.measurable.ennreal_ofReal
  have ht : ∀ᵐ x ∂riemannianVolumeMeasure (I := I) (M := M) q,
      ENNReal.ofReal (riemannianVolumeDensity q h x) < ⊤ := Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [_root_.MeasureTheory.integrable_withDensity_iff_integrable_smul' hρ ht]
  simp only [ENNReal.toReal_ofReal (riemannianVolumeDensity_pos q h _).le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integrable_riemannianVolumeMeasure_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integrable_riemannianVolumeMeasure_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integrable_riemannianVolumeMeasure_iff ``Submission.DifferentialGeometry.Integral.Measure.integrable_riemannianVolumeMeasure_iff

theorem integrable_prod_volumeDensity_smul_iff
    {P F : Type*} [MeasurableSpace P] (μ : MeasureTheory.Measure P)
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (q : SmoothRiemannianMetric I M) (g : P → SmoothRiemannianMetric I M)
    (f : P × M → F)
    (hf : _root_.MeasureTheory.AEStronglyMeasurable (fun p => riemannianVolumeDensity q (g p.1) p.2 • f p)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q))) :
    _root_.MeasureTheory.Integrable (fun p => riemannianVolumeDensity q (g p.1) p.2 • f p)
        (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q)) ↔
      (∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (fun x => f (t, x)) (riemannianVolumeMeasure (I := I) (M := M) (g t))) ∧
        Integrable (fun t => ∫ x, ‖f (t, x)‖ ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) μ := by
  let _ := riemannianVolumeMeasure_sigmaFinite q
  have hnorm (t : P) :
      (∫ x, ‖riemannianVolumeDensity q (g t) x • f (t, x)‖
        ∂riemannianVolumeMeasure (I := I) (M := M) q) =
      ∫ x, ‖f (t, x)‖ ∂riemannianVolumeMeasure (I := I) (M := M) (g t) := by
    rw [integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul q (g t)]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (riemannianVolumeDensity_pos q (g t) x), smul_eq_mul]
  rw [_root_.MeasureTheory.integrable_prod_iff hf]
  have hfiber (t : P) := integrable_riemannianVolumeMeasure_iff q (g t) (fun x => f (t, x))
  simp_rw [← hfiber, hnorm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integrable_prod_volumeDensity_smul_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integrable_prod_volumeDensity_smul_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integrable_prod_volumeDensity_smul_iff ``Submission.DifferentialGeometry.Integral.Measure.integrable_prod_volumeDensity_smul_iff

theorem integrable_prod_volumeDensity_smul_of_lintegral_norm_le
    {P F : Type*} [MeasurableSpace P] (μ : MeasureTheory.Measure P) [_root_.MeasureTheory.IsFiniteMeasure μ]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (q : SmoothRiemannianMetric I M) (g : P → SmoothRiemannianMetric I M)
    (f : P × M → F)
    (hf : _root_.MeasureTheory.AEStronglyMeasurable (fun p => riemannianVolumeDensity q (g p.1) p.2 • f p)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q)))
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hmass : ∀ᵐ t ∂μ, (∫⁻ x, ENNReal.ofReal ‖f (t, x)‖
      ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) ≤ C) :
    _root_.MeasureTheory.Integrable (fun p => riemannianVolumeDensity q (g p.1) p.2 • f p)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q)) := by
  let _ := riemannianVolumeMeasure_sigmaFinite q
  refine ⟨hf, ?_⟩
  rw [_root_.MeasureTheory.hasFiniteIntegral_iff_norm, _root_.MeasureTheory.lintegral_prod _ hf.norm.aemeasurable.ennreal_ofReal]
  have heq (t : P) :
      (∫⁻ x, ENNReal.ofReal ‖riemannianVolumeDensity q (g t) x • f (t, x)‖
        ∂riemannianVolumeMeasure (I := I) (M := M) q) =
      ∫⁻ x, ENNReal.ofReal ‖f (t, x)‖ ∂riemannianVolumeMeasure (I := I) (M := M) (g t) := by
    rw [riemannianVolumeMeasure_eq_withDensity q (g t),
      _root_.MeasureTheory.lintegral_withDensity_eq_lintegral_mul_non_measurable _
        (riemannianVolumeDensity_contMDiff q (g t)).continuous.measurable.ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply _root_.MeasureTheory.lintegral_congr
    intro x
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (riemannianVolumeDensity_pos q (g t) x)]
    exact ENNReal.ofReal_mul (riemannianVolumeDensity_pos q (g t) x).le
  simp_rw [heq]
  apply lt_of_le_of_lt (_root_.MeasureTheory.lintegral_mono_ae hmass)
  rw [_root_.MeasureTheory.lintegral_const]
  exact ENNReal.mul_lt_top hC.lt_top (_root_.MeasureTheory.measure_lt_top μ Set.univ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integrable_prod_volumeDensity_smul_of_lintegral_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integrable_prod_volumeDensity_smul_of_lintegral_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integrable_prod_volumeDensity_smul_of_lintegral_norm_le ``Submission.DifferentialGeometry.Integral.Measure.integrable_prod_volumeDensity_smul_of_lintegral_norm_le

theorem integral_prod_volumeDensity_smul
    {P F : Type*} [MeasurableSpace P] (μ : MeasureTheory.Measure P) [_root_.MeasureTheory.SFinite μ]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (q : SmoothRiemannianMetric I M) (g : P → SmoothRiemannianMetric I M)
    (f : P × M → F)
    (hf : _root_.MeasureTheory.Integrable (fun p => riemannianVolumeDensity q (g p.1) p.2 • f p)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q))) :
    (∫ p, riemannianVolumeDensity q (g p.1) p.2 • f p
      ∂μ.prod (riemannianVolumeMeasure (I := I) (M := M) q)) =
      ∫ t, ∫ x, f (t, x) ∂riemannianVolumeMeasure (I := I) (M := M) (g t) ∂μ := by
  let _ := riemannianVolumeMeasure_sigmaFinite q
  rw [_root_.MeasureTheory.integral_prod _ hf]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  exact (integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul q (g t) (fun x => f (t, x))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integral_prod_volumeDensity_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integral_prod_volumeDensity_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integral_prod_volumeDensity_smul ``Submission.DifferentialGeometry.Integral.Measure.integral_prod_volumeDensity_smul

theorem integrable_integral_riemannianVolumeMeasure
    {P F : Type*} [MeasurableSpace P] (μ : MeasureTheory.Measure P)
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (q : SmoothRiemannianMetric I M) (g : P → SmoothRiemannianMetric I M)
    (f : P × M → F)
    (hf : _root_.MeasureTheory.Integrable (fun p => riemannianVolumeDensity q (g p.1) p.2 • f p)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := M) q))) :
    _root_.MeasureTheory.Integrable (fun t => ∫ x, f (t, x)
      ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) μ := by
  let _ := riemannianVolumeMeasure_sigmaFinite q
  exact hf.integral_prod_left.congr (Eventually.of_forall fun t =>
    (integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul q (g t) (fun x => f (t, x))).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integrable_integral_riemannianVolumeMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integrable_integral_riemannianVolumeMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integrable_integral_riemannianVolumeMeasure ``Submission.DifferentialGeometry.Integral.Measure.integrable_integral_riemannianVolumeMeasure

end DifferentialGeometry.Integral.Measure
