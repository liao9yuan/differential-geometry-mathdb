import Mathlib.MeasureTheory.Function.LocallyIntegrable

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set

namespace MeasureTheory
open _root_.MeasureTheory

variable {X E 𝕜 : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E]
  [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  {μ : Measure X} {Ω : Set X}

open _root_.MeasureTheory _root_.MeasureTheory.LocallyIntegrableOn in
theorem LocallyIntegrableOn.integrable_smul_left_of_hasCompactSupport
    {f : X → E} (hf : _root_.MeasureTheory.LocallyIntegrableOn f Ω μ) {g : X → 𝕜}
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ω) :
    Integrable (fun x => g x • f x) μ := by
  apply (_root_.MeasureTheory.integrableOn_iff_integrable_of_support_subset
    ((subset_tsupport (fun x => g x • f x)).trans (tsupport_smul_subset_left g f))).mp
  exact (hf.integrableOn_compact_subset hgs hgc).smul_of_top_right
    (hg.memLp_top_of_hasCompactSupport hgc (μ.restrict (tsupport g)))

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MeasureTheory.LocallyIntegrableOn
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.LocallyIntegrableOn.integrable_smul_left_of_hasCompactSupport then
    throwError "Refusing to shadow existing declaration MeasureTheory.LocallyIntegrableOn.integrable_smul_left_of_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.LocallyIntegrableOn.integrable_smul_left_of_hasCompactSupport ``Submission.MeasureTheory.LocallyIntegrableOn.integrable_smul_left_of_hasCompactSupport

open _root_.MeasureTheory _root_.MeasureTheory.LocallyIntegrableOn in
theorem LocallyIntegrableOn.integrable_smul_right_of_hasCompactSupport
    {f : X → 𝕜} (hf : _root_.MeasureTheory.LocallyIntegrableOn f Ω μ) {g : X → E}
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ω) :
    Integrable (fun x => f x • g x) μ := by
  apply (_root_.MeasureTheory.integrableOn_iff_integrable_of_support_subset
    ((subset_tsupport (fun x => f x • g x)).trans (tsupport_smul_subset_right f g))).mp
  exact (hf.integrableOn_compact_subset hgs hgc).smul_of_top_left
    (hg.memLp_top_of_hasCompactSupport hgc (μ.restrict (tsupport g)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.LocallyIntegrableOn.integrable_smul_right_of_hasCompactSupport then
    throwError "Refusing to shadow existing declaration MeasureTheory.LocallyIntegrableOn.integrable_smul_right_of_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.LocallyIntegrableOn.integrable_smul_right_of_hasCompactSupport ``Submission.MeasureTheory.LocallyIntegrableOn.integrable_smul_right_of_hasCompactSupport

end MeasureTheory
