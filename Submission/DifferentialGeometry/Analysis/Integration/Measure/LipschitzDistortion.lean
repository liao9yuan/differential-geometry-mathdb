import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Set

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory
open scoped _root_.ENNReal _root_.NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

open _root_.LipschitzWith in
theorem LipschitzWith.addHaar_image_le {K : ℝ≥0} {f : E → E}
    (hf : LipschitzWith K f) (s : Set E) :
    μ (f '' s) ≤ (K : ℝ≥0∞) ^ Module.finrank ℝ E * μ s := by
  let ν : _root_.MeasureTheory.Measure E := μH[Module.finrank ℝ E]
  have heq : μ = Measure.addHaarScalarFactor μ ν • ν :=
    Measure.isAddLeftInvariant_eq_smul μ ν
  have h := hf.hausdorffMeasure_image_le
    (show (0 : ℝ) ≤ Module.finrank ℝ E by positivity) s
  simp only [ENNReal.rpow_natCast] at h
  rw [heq, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def,
    ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
  exact (mul_le_mul_right h _).trans_eq (mul_left_comm _ _ _)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.LipschitzWith
  let env ← Lean.getEnv
  if env.contains `LipschitzWith.addHaar_image_le then
    throwError "Refusing to shadow existing declaration LipschitzWith.addHaar_image_le"
  Lean.modifyEnv fun env => Lean.addAlias env `LipschitzWith.addHaar_image_le ``Submission.LipschitzWith.addHaar_image_le

open _root_.AntilipschitzWith in
theorem AntilipschitzWith.addHaar_preimage_le {K : ℝ≥0} {f : E → E}
    (hf : AntilipschitzWith K f) (s : Set E) :
    μ (f ⁻¹' s) ≤ (K : ℝ≥0∞) ^ Module.finrank ℝ E * μ s := by
  let ν : _root_.MeasureTheory.Measure E := μH[Module.finrank ℝ E]
  have heq : μ = Measure.addHaarScalarFactor μ ν • ν :=
    Measure.isAddLeftInvariant_eq_smul μ ν
  have h := hf.hausdorffMeasure_preimage_le
    (show (0 : ℝ) ≤ Module.finrank ℝ E by positivity) s
  simp only [ENNReal.rpow_natCast] at h
  rw [heq, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def,
    ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
  exact (mul_le_mul_right h _).trans_eq (mul_left_comm _ _ _)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.AntilipschitzWith
  let env ← Lean.getEnv
  if env.contains `AntilipschitzWith.addHaar_preimage_le then
    throwError "Refusing to shadow existing declaration AntilipschitzWith.addHaar_preimage_le"
  Lean.modifyEnv fun env => Lean.addAlias env `AntilipschitzWith.addHaar_preimage_le ``Submission.AntilipschitzWith.addHaar_preimage_le

open _root_.AntilipschitzWith in
theorem AntilipschitzWith.map_addHaar_le {K : ℝ≥0} {f : E → E}
    (hf : AntilipschitzWith K f) (hm : Measurable f) :
    μ.map f ≤ (K : ℝ≥0∞) ^ Module.finrank ℝ E • μ := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply hm hs, Measure.smul_apply, smul_eq_mul]
  exact hf.addHaar_preimage_le μ s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AntilipschitzWith.map_addHaar_le then
    throwError "Refusing to shadow existing declaration AntilipschitzWith.map_addHaar_le"
  Lean.modifyEnv fun env => Lean.addAlias env `AntilipschitzWith.map_addHaar_le ``Submission.AntilipschitzWith.map_addHaar_le

open _root_.Homeomorph in
theorem Homeomorph.setIntegral_comp_le_of_lipschitz_symm
    (e : E ≃ₜ E) {K : ℝ≥0} (he : LipschitzWith K e.symm)
    {s : Set E} (hs : MeasurableSet s) {f : E → ℝ}
    (hf : _root_.MeasureTheory.IntegrableOn f s μ) (hpos : 0 ≤ᵐ[μ.restrict s] f) :
    (∫ x in e ⁻¹' s, f (e x) ∂μ) ≤
      (K : ℝ) ^ Module.finrank ℝ E * ∫ x in s, f x ∂μ := by
  have ha : AntilipschitzWith K e := by
    intro x y
    simpa only [e.symm_apply_apply] using he (e x) (e y)
  have hm := ha.map_addHaar_le μ e.continuous.measurable
  have hmr : (μ.map e).restrict s ≤
      ((K : ℝ≥0∞) ^ Module.finrank ℝ E) • μ.restrict s := by
    simpa only [Measure.restrict_smul] using Measure.restrict_mono (Subset.refl s) hm
  have hi := _root_.MeasureTheory.integral_mono_measure hmr
    (Measure.ae_smul_measure hpos _) (hf.smul_measure (by finiteness))
  rw [Measure.restrict_map e.continuous.measurable hs,
    e.isClosedEmbedding.measurableEmbedding.integral_map] at hi
  simpa only [_root_.MeasureTheory.integral_smul_measure, smul_eq_mul, ENNReal.toReal_pow,
    ENNReal.coe_toReal] using hi

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Homeomorph
  let env ← Lean.getEnv
  if env.contains `Homeomorph.setIntegral_comp_le_of_lipschitz_symm then
    throwError "Refusing to shadow existing declaration Homeomorph.setIntegral_comp_le_of_lipschitz_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.setIntegral_comp_le_of_lipschitz_symm ``Submission.Homeomorph.setIntegral_comp_le_of_lipschitz_symm

end
