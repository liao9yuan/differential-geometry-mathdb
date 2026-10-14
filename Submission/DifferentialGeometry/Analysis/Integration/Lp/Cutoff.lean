import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.ENNReal

namespace MeasureTheory
open _root_.MeasureTheory

variable {X 𝕜 E : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedRing 𝕜] [NormedAddCommGroup E]
  [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E]

open _root_.MeasureTheory _root_.MeasureTheory.MemLp in
theorem MemLp.continuous_smul_of_tsupport_subset
    {Ω : Set X} {μ : _root_.MeasureTheory.Measure X} {u : X → E} {η : X → 𝕜} {p : ℝ≥0∞}
    (hu : _root_.MeasureTheory.MemLp u p (μ.restrict Ω)) (hΩ : MeasurableSet Ω)
    (hη : Continuous η) (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω) :
    MemLp (fun x => η x • u x) p μ := by
  have hm : _root_.MeasureTheory.MemLp (fun x => η x • u x) p (μ.restrict Ω) :=
    hu.smul ((hη.memLp_top_of_hasCompactSupport hηc μ).restrict Ω)
  have hi := (_root_.MeasureTheory.memLp_indicator_iff_restrict hΩ).mpr hm
  have heq : Ω.indicator (fun x => η x • u x) = fun x => η x • u x := by
    funext x
    by_cases hx : x ∈ Ω
    · rw [_root_.Set.indicator_of_mem hx]
    · rw [_root_.Set.indicator_of_notMem hx,
        image_eq_zero_of_notMem_tsupport (fun h => hx (hηs h)), zero_smul]
  rwa [heq] at hi

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MeasureTheory.MemLp
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.MemLp.continuous_smul_of_tsupport_subset then
    throwError "Refusing to shadow existing declaration MeasureTheory.MemLp.continuous_smul_of_tsupport_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.MemLp.continuous_smul_of_tsupport_subset ``Submission.MeasureTheory.MemLp.continuous_smul_of_tsupport_subset

end MeasureTheory
