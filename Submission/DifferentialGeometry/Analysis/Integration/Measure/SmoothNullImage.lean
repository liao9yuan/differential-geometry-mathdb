import Submission.DifferentialGeometry.Analysis.Calculus.Compactness.Lipschitz
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set _root_.MeasureTheory
open scoped _root_.MeasureTheory _root_.NNReal

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem volume_image_eq_zero_of_lipschitzOn {f : E → E} {K : ℝ≥0} {s : Set E}
    (hf : LipschitzOnWith K f s) (hs : _root_.MeasureTheory.MeasureSpace.volume s = 0) : _root_.MeasureTheory.MeasureSpace.volume (f '' s) = 0 := by
  let H : _root_.MeasureTheory.Measure E := Measure.hausdorffMeasure (Module.finrank ℝ E)
  have hHv : H ≪ volume := Measure.absolutelyContinuous_isAddHaarMeasure H _root_.MeasureTheory.MeasureSpace.volume
  have hvH : _root_.MeasureTheory.MeasureSpace.volume ≪ H := Measure.absolutelyContinuous_isAddHaarMeasure _root_.MeasureTheory.MeasureSpace.volume H
  apply hvH
  have hh := hf.hausdorffMeasure_image_le (d := (Module.finrank ℝ E : ℝ)) (Nat.cast_nonneg _)
  change H (f '' s) ≤ _ at hh
  rw [show H s = 0 from hHv hs, _root_.MulZeroClass.mul_zero] at hh
  exact le_zero_iff.mp hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.volume_image_eq_zero_of_lipschitzOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.volume_image_eq_zero_of_lipschitzOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.volume_image_eq_zero_of_lipschitzOn ``Submission.DifferentialGeometry.Analysis.volume_image_eq_zero_of_lipschitzOn

theorem volume_image_compact_eq_zero_of_contDiffOn
    {f : E → E} {Ω K : Set E} (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ 1 f Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hnull : _root_.MeasureTheory.MeasureSpace.volume K = 0) : _root_.MeasureTheory.MeasureSpace.volume (f '' K) = 0 := by
  obtain ⟨L, hL⟩ := hf.exists_lipschitzOnWith_of_isCompact hΩ hK hKΩ
  exact volume_image_eq_zero_of_lipschitzOn hL hnull

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.volume_image_compact_eq_zero_of_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.volume_image_compact_eq_zero_of_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.volume_image_compact_eq_zero_of_contDiffOn ``Submission.DifferentialGeometry.Analysis.volume_image_compact_eq_zero_of_contDiffOn

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open _root_.Set _root_.MeasureTheory

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem volume_image_sphere_eq_zero_of_contDiffOn
    {W : E → E} {Ω : Set E} (hΩ : IsOpen Ω) (hW : ContDiffOn ℝ 1 W Ω)
    (c : E) (R : ℝ) (hsub : Metric.sphere c R ⊆ Ω) :
    volume (W '' Metric.sphere c R) = 0 :=
  volume_image_compact_eq_zero_of_contDiffOn hΩ hW (isCompact_sphere c R) hsub
    (Measure.addHaar_sphere _root_.MeasureTheory.MeasureSpace.volume c R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.volume_image_sphere_eq_zero_of_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.volume_image_sphere_eq_zero_of_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.volume_image_sphere_eq_zero_of_contDiffOn ``Submission.DifferentialGeometry.Analysis.volume_image_sphere_eq_zero_of_contDiffOn

theorem volume_image_subset_sphere_eq_zero_of_contDiffOn
    {W : E → E} {Ω : Set E} (hΩ : IsOpen Ω) (hW : ContDiffOn ℝ 1 W Ω)
    (c : E) (R : ℝ) (hsub : Metric.sphere c R ⊆ Ω) {S : Set E}
    (hS : S ⊆ Metric.sphere c R) : _root_.MeasureTheory.MeasureSpace.volume (W '' S) = 0 :=
  _root_.MeasureTheory.measure_mono_null (_root_.Set.image_mono hS) (volume_image_sphere_eq_zero_of_contDiffOn hΩ hW c R hsub)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.volume_image_subset_sphere_eq_zero_of_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.volume_image_subset_sphere_eq_zero_of_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.volume_image_subset_sphere_eq_zero_of_contDiffOn ``Submission.DifferentialGeometry.Analysis.volume_image_subset_sphere_eq_zero_of_contDiffOn

end DifferentialGeometry.Analysis

end

end
