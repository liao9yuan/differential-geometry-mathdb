import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.TimeDependent
import Mathlib.Topology.Order.ProjIcc

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]

theorem timeNemy_of_contOn_Icc
    {S : Set X} {τ : ℝ} (hzero : (0 : X) ∈ S)
    {N : ℝ → S → Y}
    (hN : Continuous (fun p : Set.Icc (0 : ℝ) τ × S => N p.1 p.2)) :
    TimeNemyMeas hzero N τ := by
  intro T hT f hf
  by_cases hτ : 0 ≤ τ
  · let Nc : ℝ → S → Y := fun t u => N (Set.projIcc 0 τ hτ t) u
    have hc : Continuous (Set.projIcc 0 τ hτ) := continuous_projIcc
    have hp : Continuous (fun p : ℝ × S => (Set.projIcc 0 τ hτ p.1, p.2)) :=
      (hc.comp continuous_fst).prodMk continuous_snd
    have hNc : Continuous (fun p : ℝ × S => Nc p.1 p.2) := hN.comp hp
    have hmeas : TimeNemyMeas hzero Nc τ := timeNemy_of_cont hzero hNc
    apply (hmeas hT f hf).congr
    have ht : ∀ᵐ t ∂(TimeSobolev.timeMeasure T), t ∈ Set.Icc (0 : ℝ) T :=
      _root_.MeasureTheory.ae_restrict_mem measurableSet_Icc
    filter_upwards [ht] with t ht
    change N (Set.projIcc 0 τ hτ t) _ = N t _
    rw [Set.projIcc_of_mem hτ ⟨ht.1, ht.2.trans hT⟩]
  · rw [TimeSobolev.timeMeasure_eq_zero_of_nonpos (hT.trans (le_of_not_ge hτ))]
    exact _root_.MeasureTheory.aestronglyMeasurable_zero_measure _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.timeNemy_of_contOn_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.QuasiLinear.timeNemy_of_contOn_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.QuasiLinear.timeNemy_of_contOn_Icc ``Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.timeNemy_of_contOn_Icc

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
