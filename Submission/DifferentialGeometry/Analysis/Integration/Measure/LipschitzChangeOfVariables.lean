import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Lipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission









noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.NNReal _root_.Topology _root_.ENNReal _root_.MeasureTheory

open _root_.LocallyLipschitzOn in
theorem LocallyLipschitzOn.addHaar_image_eq_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    {μ : _root_.MeasureTheory.Measure E} [μ.IsAddHaarMeasure] {ν : _root_.MeasureTheory.Measure F} [ν.IsAddHaarMeasure]
    {f : E → F} {s : Set E} (hf : LocallyLipschitzOn s f)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (hs : μ s = 0) : ν (f '' s) = 0 := by
  let H : _root_.MeasureTheory.Measure E := Measure.hausdorffMeasure (Module.finrank ℝ E)
  let J : _root_.MeasureTheory.Measure F := Measure.hausdorffMeasure (Module.finrank ℝ F)
  have hH : H s = 0 := (Measure.absolutelyContinuous_isAddHaarMeasure H μ) hs
  have hlocal (x : s) : ∃ V : Set E, IsOpen V ∧ x.1 ∈ V ∧ ν (f '' (V ∩ s)) = 0 := by
    obtain ⟨K, T, hT, hK⟩ := hf x.2
    obtain ⟨W, hW, hWT⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hT
    obtain ⟨V, hVW, hV, hxV⟩ := mem_nhds_iff.mp hW
    have hLip : LipschitzOnWith K f (V ∩ s) :=
      hK.mono (fun y hy => hWT ⟨hVW hy.1, hy.2⟩)
    refine ⟨V, hV, hxV, ?_⟩
    apply Measure.absolutelyContinuous_isAddHaarMeasure ν J
    have hz : H (V ∩ s) = 0 := _root_.MeasureTheory.measure_mono_null _root_.Set.inter_subset_right hH
    have hle := hLip.hausdorffMeasure_image_le (d := (Module.finrank ℝ E : ℝ)) (by positivity)
    change Measure.hausdorffMeasure (Module.finrank ℝ E) (f '' (V ∩ s)) ≤
      (K : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ) * H (V ∩ s) at hle
    rw [hz, _root_.MulZeroClass.mul_zero, hdim] at hle
    exact le_zero_iff.mp hle
  choose V hV hxV hnull using hlocal
  obtain ⟨S, hS, hcover⟩ := (HereditarilyLindelofSpace.isLindelof s).elim_countable_subcover
    V hV (fun x hx => _root_.Set.mem_iUnion_of_mem ⟨x, hx⟩ (hxV ⟨x, hx⟩))
  have hsub : f '' s ⊆ ⋃ x ∈ S, f '' (V x ∩ s) := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hxV⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion₂.mpr ⟨z, hz, x, ⟨hxV, hx⟩, rfl⟩
  exact _root_.MeasureTheory.measure_mono_null hsub ((_root_.MeasureTheory.measure_biUnion_null_iff hS).mpr (fun x _ => hnull x))

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.LocallyLipschitzOn
  let env ← Lean.getEnv
  if env.contains `LocallyLipschitzOn.addHaar_image_eq_zero then
    throwError "Refusing to shadow existing declaration LocallyLipschitzOn.addHaar_image_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `LocallyLipschitzOn.addHaar_image_eq_zero ``Submission.LocallyLipschitzOn.addHaar_image_eq_zero

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]



theorem volume_image_eq_zero_of_lipschitz {f : E → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) {s : Set E} (hs : _root_.MeasureTheory.MeasureSpace.volume s = 0) :
    volume (f '' s) = 0 := by
  exact hf.locallyLipschitz.locallyLipschitzOn.addHaar_image_eq_zero rfl hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.volume_image_eq_zero_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.volume_image_eq_zero_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.volume_image_eq_zero_of_lipschitz ``Submission.DifferentialGeometry.Analysis.volume_image_eq_zero_of_lipschitz

theorem ae_comp_of_lipschitz_leftInverse_on {f k : E → E} {K : ℝ≥0}
    (hk : LipschitzWith K k) {s : Set E} (hki : ∀ x ∈ s, k (f x) = x)
    {P : E → Prop} (hP : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ x ∂volume, x ∈ s → P (f x) := by
  have hz := volume_image_eq_zero_of_lipschitz hk (ae_iff.mp hP)
  have ha : ∀ᵐ x ∂volume, x ∉ k '' {y | ¬ P y} := by
    apply ae_iff.mpr
    convert hz using 1
    congr 1
    ext x
    simp
  filter_upwards [ha] with x hx
  intro hxs
  by_contra hp
  exact hx ⟨f x, hp, hki x hxs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ae_comp_of_lipschitz_leftInverse_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ae_comp_of_lipschitz_leftInverse_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ae_comp_of_lipschitz_leftInverse_on ``Submission.DifferentialGeometry.Analysis.ae_comp_of_lipschitz_leftInverse_on

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem integral_image_eq_integral_abs_det_of_lipschitz {f : E → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) {s : Set E} (hs : MeasurableSet s) (hi : _root_.Set.InjOn f s)
    (g : E → F) :
    ∫ x in f '' s, g x =
      ∫ x in s, |(fderiv ℝ f x).toLinearMap.det| • g (f x) := by
  let t : Set E := s ∩ {x | DifferentiableAt ℝ f x}
  have ht : MeasurableSet t := hs.inter (measurableSet_of_differentiableAt ℝ f)
  have hts : t =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] s := by
    filter_upwards [hf.ae_differentiableAt (μ := _root_.MeasureTheory.MeasureSpace.volume)] with x hx
    apply propext
    change (x ∈ s ∧ DifferentiableAt ℝ f x) ↔ x ∈ s
    exact and_iff_left hx
  have hnull : _root_.MeasureTheory.MeasureSpace.volume (s \ t) = 0 := by
    apply _root_.MeasureTheory.measure_mono_null (show s \ t ⊆ {x | ¬ DifferentiableAt ℝ f x} from
      fun x hx hd => hx.2 ⟨hx.1, hd⟩)
    exact ae_iff.mp (hf.ae_differentiableAt (μ := _root_.MeasureTheory.MeasureSpace.volume))
  have himage : f '' t =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] f '' s := by
    have hz := volume_image_eq_zero_of_lipschitz hf hnull
    have he : _root_.MeasureTheory.MeasureSpace.volume (f '' s \ f '' t) = 0 := _root_.MeasureTheory.measure_mono_null
      (by
        rintro x ⟨⟨y, hy, rfl⟩, hxt⟩
        exact ⟨y, ⟨hy, fun hyt => hxt ⟨y, hyt, rfl⟩⟩, rfl⟩) hz
    have ha : ∀ᵐ x ∂volume, x ∉ f '' s \ f '' t := by
      apply ae_iff.mpr
      convert he using 1
      congr 1
      ext x
      simp only [_root_.Set.mem_ofPred_eq, _root_.Classical.not_not]
    filter_upwards [ha] with x hx
    apply propext
    change x ∈ f '' t ↔ x ∈ f '' s
    exact ⟨fun hxt => _root_.Set.image_mono (show t ⊆ s from _root_.Set.inter_subset_left) hxt, fun hxs =>
      not_not.mp (fun hxt => hx ⟨hxs, hxt⟩)⟩
  rw [← _root_.MeasureTheory.setIntegral_congr_set himage, ← _root_.MeasureTheory.setIntegral_congr_set hts]
  exact _root_.MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul _root_.MeasureTheory.MeasureSpace.volume ht
    (fun x hx => hx.2.hasFDerivAt.hasFDerivWithinAt) (hi.mono _root_.Set.inter_subset_left) g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_image_eq_integral_abs_det_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_image_eq_integral_abs_det_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_image_eq_integral_abs_det_of_lipschitz ``Submission.DifferentialGeometry.Analysis.integral_image_eq_integral_abs_det_of_lipschitz

end DifferentialGeometry.Analysis
