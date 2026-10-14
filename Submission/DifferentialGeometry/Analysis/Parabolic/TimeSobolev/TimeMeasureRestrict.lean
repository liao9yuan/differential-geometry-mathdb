import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

theorem timeMeasure_restrict_Icc_eq_volume_restrict_Icc
    {T t₀ t₁ : ℝ} (hI : _root_.Set.Icc t₀ t₁ ⊆ _root_.Set.Icc (0 : ℝ) T) :
    (timeMeasure T).restrict (_root_.Set.Icc t₀ t₁) = volume.restrict (_root_.Set.Icc t₀ t₁) := by
  exact Measure.restrict_restrict_of_subset hI

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeMeasure_restrict_Icc_eq_volume_restrict_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeMeasure_restrict_Icc_eq_volume_restrict_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeMeasure_restrict_Icc_eq_volume_restrict_Icc ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeMeasure_restrict_Icc_eq_volume_restrict_Icc

theorem measurePreserving_add_right_timeMeasure_restrict
    {T t₀ t₁ : ℝ} (hI : _root_.Set.Icc t₀ t₁ ⊆ _root_.Set.Icc (0 : ℝ) T) :
    _root_.MeasureTheory.MeasurePreserving (fun s : ℝ => t₀ + s) (timeMeasure (t₁ - t₀))
      ((timeMeasure T).restrict (_root_.Set.Icc t₀ t₁)) := by
  rw [timeMeasure_restrict_Icc_eq_volume_restrict_Icc hI]
  have h := (_root_.MeasureTheory.measurePreserving_add_right _root_.MeasureTheory.MeasureSpace.volume t₀).restrict_image_emb
    (Homeomorph.addRight t₀).isClosedEmbedding.measurableEmbedding
      (_root_.Set.Icc (0 : ℝ) (t₁ - t₀))
  simpa only [timeMeasure, _root_.Set.image_add_const_Icc, zero_add, sub_add_cancel, add_comm t₀] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.measurePreserving_add_right_timeMeasure_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.measurePreserving_add_right_timeMeasure_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.measurePreserving_add_right_timeMeasure_restrict ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.measurePreserving_add_right_timeMeasure_restrict

theorem ae_add_right_timeMeasure {T a b : ℝ} (ha : 0 ≤ a) (hbT : b ≤ T)
    {P : ℝ → Prop} (hP : ∀ᵐ t ∂timeMeasure T, P t) :
    ∀ᵐ t ∂timeMeasure (b - a), P (t + a) := by
  have hI : _root_.Set.Icc a b ⊆ _root_.Set.Icc (0 : ℝ) T := fun t ht =>
    ⟨ha.trans ht.1, ht.2.trans hbT⟩
  have hrestricted : ∀ᵐ t ∂(timeMeasure T).restrict (_root_.Set.Icc a b), P t :=
    hP.filter_mono (_root_.MeasureTheory.ae_mono Measure.restrict_le_self)
  have hshift : ∀ᵐ t ∂timeMeasure (b - a), P (a + t) :=
    (measurePreserving_add_right_timeMeasure_restrict hI).quasiMeasurePreserving.ae hrestricted
  simpa only [add_comm a] using hshift

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.ae_add_right_timeMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.ae_add_right_timeMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.ae_add_right_timeMeasure ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.ae_add_right_timeMeasure


end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
