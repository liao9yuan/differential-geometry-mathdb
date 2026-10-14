import Submission.DifferentialGeometry.Analysis.Integration.Measure.Parametric.AreaFormula
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

theorem map_withDensity_paramDensity
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U) (hinj : _root_.Set.InjOn f K) :
    Measure.map f ((modelHaar (E := E)).restrict K |>.withDensity
      (fun x => ENNReal.ofReal (paramDensity (I := I) g f x))) =
      (riemannianVolumeMeasure (I := I) (M := M) g).restrict (f '' K) := by
  have hfm := (hf.continuousOn.mono hKU).aemeasurable (μ := modelHaar (E := E)) hK
  have hfw := hfm.mono' (_root_.MeasureTheory.withDensity_absolutelyContinuous
    ((modelHaar (E := E)).restrict K)
    (fun x => ENNReal.ofReal (paramDensity (I := I) g f x)))
  refine Measure.ext fun A hA => ?_
  have hpre : MeasurableSet (f ⁻¹' A ∩ K) := by
    have hm : Measurable (fun x : K => f x) :=
      (hf.continuousOn.mono hKU).domRestrict.measurable
    convert (MeasurableEmbedding.subtype_coe hK).measurableSet_image'
      (hA.preimage hm) using 1
    ext x
    simp only [_root_.Set.mem_image, _root_.Set.mem_preimage, _root_.Set.mem_inter_iff, Subtype.exists, exists_and_right,
      exists_eq_right]
    constructor
    · rintro ⟨ha, hk⟩
      exact ⟨hk, ha⟩
    · rintro ⟨hk, ha⟩
      exact ⟨ha, hk⟩
  rw [Measure.map_apply_of_aemeasurable hfw hA, Measure.restrict_apply hA,
    _root_.MeasureTheory.withDensity_apply', Measure.restrict_restrict' hK]
  rw [show A ∩ f '' K = f '' (f ⁻¹' A ∩ K) from
    (Set.image_preimage_inter f K A).symm]
  exact (riemannianVolumeMeasure_image_eq (I := I) g hU hpre
    (inter_subset_right.trans hKU) hf (hinj.mono _root_.Set.inter_subset_right)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.map_withDensity_paramDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.map_withDensity_paramDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.map_withDensity_paramDensity ``Submission.DifferentialGeometry.Integral.Measure.map_withDensity_paramDensity

theorem lintegral_image_eq_lintegral_paramDensity_mul
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U) (hinj : _root_.Set.InjOn f K)
    (φ : M → ℝ≥0∞)
    (hφ : AEMeasurable φ ((riemannianVolumeMeasure (I := I) (M := M) g).restrict (f '' K))) :
    (∫⁻ y in f '' K, φ y ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫⁻ x in K, ENNReal.ofReal (paramDensity (I := I) g f x) * φ (f x)
        ∂(modelHaar (E := E)) := by
  have hfm := (hf.continuousOn.mono hKU).aemeasurable (μ := modelHaar (E := E)) hK
  have hfw := hfm.mono' (_root_.MeasureTheory.withDensity_absolutelyContinuous
    ((modelHaar (E := E)).restrict K)
    (fun x => ENNReal.ofReal (paramDensity (I := I) g f x)))
  have hJ := ((continuousOn_paramDensity g hU hf).mono hKU).aemeasurable
    (μ := modelHaar (E := E)) hK |>.ennreal_ofReal
  rw [← map_withDensity_paramDensity g hU hK hKU hf hinj] at hφ ⊢
  rw [_root_.MeasureTheory.lintegral_map' hφ hfw]
  exact _root_.MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀' hJ (hφ.comp_aemeasurable hfw)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.lintegral_image_eq_lintegral_paramDensity_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.lintegral_image_eq_lintegral_paramDensity_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.lintegral_image_eq_lintegral_paramDensity_mul ``Submission.DifferentialGeometry.Integral.Measure.lintegral_image_eq_lintegral_paramDensity_mul

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem integrableOn_image_iff_paramDensity_smul
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U) (hinj : _root_.Set.InjOn f K)
    (φ : M → F)
    (hφ : _root_.MeasureTheory.AEStronglyMeasurable φ
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict (f '' K))) :
    IntegrableOn φ (f '' K) (riemannianVolumeMeasure (I := I) (M := M) g) ↔
      IntegrableOn (fun x => paramDensity (I := I) g f x • φ (f x))
        K (modelHaar (E := E)) := by
  have hfm := (hf.continuousOn.mono hKU).aemeasurable (μ := modelHaar (E := E)) hK
  have hfw := hfm.mono' (_root_.MeasureTheory.withDensity_absolutelyContinuous
    ((modelHaar (E := E)).restrict K)
    (fun x => ENNReal.ofReal (paramDensity (I := I) g f x)))
  have hJ := ((continuousOn_paramDensity g hU hf).mono hKU).aemeasurable
    (μ := modelHaar (E := E)) hK |>.ennreal_ofReal
  simp only [_root_.MeasureTheory.IntegrableOn]
  rw [← map_withDensity_paramDensity g hU hK hKU hf hinj] at hφ ⊢
  rw [_root_.MeasureTheory.integrable_map_measure hφ hfw,
    _root_.MeasureTheory.integrable_withDensity_iff_integrable_smul₀' hJ
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [Function.comp_apply, paramDensity,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integrableOn_image_iff_paramDensity_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integrableOn_image_iff_paramDensity_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integrableOn_image_iff_paramDensity_smul ``Submission.DifferentialGeometry.Integral.Measure.integrableOn_image_iff_paramDensity_smul

theorem integral_image_eq_integral_paramDensity_smul
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U) (hinj : _root_.Set.InjOn f K)
    (φ : M → F)
    (hφ : _root_.MeasureTheory.AEStronglyMeasurable φ
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict (f '' K))) :
    (∫ y in f '' K, φ y ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x in K, paramDensity (I := I) g f x • φ (f x)
        ∂(modelHaar (E := E)) := by
  have hfm := (hf.continuousOn.mono hKU).aemeasurable (μ := modelHaar (E := E)) hK
  have hfw := hfm.mono' (_root_.MeasureTheory.withDensity_absolutelyContinuous
    ((modelHaar (E := E)).restrict K)
    (fun x => ENNReal.ofReal (paramDensity (I := I) g f x)))
  have hJ := ((continuousOn_paramDensity g hU hf).mono hKU).aemeasurable
    (μ := modelHaar (E := E)) hK |>.ennreal_ofReal
  rw [← map_withDensity_paramDensity g hU hK hKU hf hinj] at hφ ⊢
  rw [_root_.MeasureTheory.integral_map hfw hφ, integral_withDensity_eq_integral_toReal_smul₀ hJ
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply _root_.MeasureTheory.integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (show 0 ≤ paramDensity (I := I) g f x from
      Real.sqrt_nonneg _)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integral_image_eq_integral_paramDensity_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integral_image_eq_integral_paramDensity_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integral_image_eq_integral_paramDensity_smul ``Submission.DifferentialGeometry.Integral.Measure.integral_image_eq_integral_paramDensity_smul

end DifferentialGeometry.Integral.Measure
