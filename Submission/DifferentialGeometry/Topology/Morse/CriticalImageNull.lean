import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.Function _root_.MeasureTheory _root_.MeasureTheory.Measure
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Morse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I 1 M]
  {f : M → E}


theorem addHaar_critical_image_chart_eq_zero (μ : _root_.MeasureTheory.Measure E) [_root_.MeasureTheory.Measure.IsAddHaarMeasure μ]
    (hf : MDifferentiable I 𝓘(ℝ, E) f) (x : M) :
    μ (f '' {y : M | y ∈ (extChartAt I x).source ∧
      ¬ _root_.Function.Surjective (mfderiv I 𝓘(ℝ, E) f y)}) = 0 := by
  let c := extChartAt I x
  let s := {z : E | z ∈ c.target ∧ ¬ _root_.Function.Surjective (mfderiv I 𝓘(ℝ, E) f (c.symm z))}
  let d : E → E →L[ℝ] E := fun z : E => (mfderiv I 𝓘(ℝ, E) f (c.symm z)).comp
    (mfderiv 𝓘(ℝ, E) I c.symm z)
  have hd (z : E) (hz : z ∈ s) : HasFDerivAt (f ∘ c.symm) (d z) z := by
    have hc : MDifferentiableAt 𝓘(ℝ, E) I c.symm z :=
      ((contMDiffOn_extChartAt_symm (I := I) (n := 1) x).contMDiffAt
        ((isOpen_extChartAt_target x).mem_nhds hz.1)).mdifferentiableAt one_ne_zero
    exact hasMFDerivAt_iff_hasFDerivAt.mp ((hf _).hasMFDerivAt.comp z hc.hasMFDerivAt)
  have hz (z : E) (hz : z ∈ s) : (d z).det = 0 := by
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot]
    intro hk
    have hi : _root_.Function.Injective (d z) := LinearMap.ker_eq_bot.mp hk
    have hh : _root_.Function.Surjective (d z) := (d z).toLinearMap.injective_iff_surjective.mp hi
    apply hz.2
    exact Surjective.of_comp (show _root_.Function.Surjective ((mfderiv I 𝓘(ℝ, E) f (c.symm z)) ∘
      (mfderiv 𝓘(ℝ, E) I c.symm z)) from hh)
  have hnull := _root_.MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := μ)
    (fun z hz => (hd z hz).hasFDerivWithinAt) hz
  have himage : (f ∘ c.symm) '' s = f '' {y : M | y ∈ c.source ∧
      ¬ _root_.Function.Surjective (mfderiv I 𝓘(ℝ, E) f y)} := by
    ext v
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨c.symm z, ⟨c.map_target hz.1,hz.2⟩,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      refine ⟨c y, ⟨c.map_source hy.1, ?_⟩, ?_⟩
      · change ¬ _root_.Function.Surjective (show E →L[ℝ] E from mfderiv I 𝓘(ℝ, E) f (c.symm (c y)))
        rw [c.left_inv hy.1]
        exact hy.2
      · simp only [_root_.Function.comp_apply,c.left_inv hy.1]
  rwa [himage] at hnull

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.addHaar_critical_image_chart_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.addHaar_critical_image_chart_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.addHaar_critical_image_chart_eq_zero ``Submission.DifferentialGeometry.Morse.addHaar_critical_image_chart_eq_zero


theorem addHaar_critical_image_eq_zero [SecondCountableTopology M]
    (μ : _root_.MeasureTheory.Measure E) [_root_.MeasureTheory.Measure.IsAddHaarMeasure μ] (hf : MDifferentiable I 𝓘(ℝ, E) f) :
    μ (f '' {y : M | ¬ _root_.Function.Surjective (mfderiv I 𝓘(ℝ, E) f y)}) = 0 := by
  obtain ⟨t,ht,hcover⟩ := TopologicalSpace.countable_cover_nhds
    (fun x : M => extChartAt_source_mem_nhds (I := I) x)
  have hnull : ∀ x ∈ t, μ (f '' {y : M | y ∈ (extChartAt I x).source ∧
      ¬ _root_.Function.Surjective (mfderiv I 𝓘(ℝ, E) f y)}) = 0 :=
    fun x _ => addHaar_critical_image_chart_eq_zero μ hf x
  apply _root_.MeasureTheory.measure_mono_null (t := ⋃ x ∈ t, f '' {y : M | y ∈ (extChartAt I x).source ∧
    ¬ _root_.Function.Surjective (mfderiv I 𝓘(ℝ, E) f y)}) _ ((_root_.MeasureTheory.measure_biUnion_null_iff ht).mpr hnull)
  rintro z ⟨y,hy,rfl⟩
  have hycover : y ∈ ⋃ x ∈ t, (extChartAt I x).source := hcover ▸ _root_.Set.mem_univ y
  rcases mem_iUnion₂.mp hycover with ⟨x,hxt,hyx⟩
  exact mem_iUnion₂.mpr ⟨x,hxt,⟨y,⟨hyx,hy⟩,rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.addHaar_critical_image_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.addHaar_critical_image_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.addHaar_critical_image_eq_zero ``Submission.DifferentialGeometry.Morse.addHaar_critical_image_eq_zero


theorem ae_regular_values [SecondCountableTopology M]
    (μ : _root_.MeasureTheory.Measure E) [_root_.MeasureTheory.Measure.IsAddHaarMeasure μ] (hf : MDifferentiable I 𝓘(ℝ, E) f) :
    ∀ᵐ z ∂μ, ∀ x : M, f x = z → _root_.Function.Surjective (mfderiv I 𝓘(ℝ, E) f x) := by
  have h := (_root_.MeasureTheory.measure_eq_zero_iff_ae_notMem).mp (addHaar_critical_image_eq_zero μ hf)
  filter_upwards [h] with z hz x hx
  by_contra hc
  exact hz ⟨x,hc,hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Morse.ae_regular_values then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Morse.ae_regular_values"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Morse.ae_regular_values ``Submission.DifferentialGeometry.Morse.ae_regular_values

end DifferentialGeometry.Morse
