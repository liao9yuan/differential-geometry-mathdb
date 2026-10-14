import Mathlib.Analysis.Calculus.Rademacher

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

open _root_.LocallyLipschitzOn in
theorem LocallyLipschitzOn.ae_differentiableWithinAt_of_mem
    {f : E → F} {s : Set E} (hf : LocallyLipschitzOn s f) :
    ∀ᵐ x ∂μ, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  let N : Set E := {x : E | x ∈ s ∧ ¬ DifferentiableWithinAt ℝ f s x}
  have hN : μ N = 0 := by
    apply _root_.MeasureTheory.measure_null_of_locally_null N
    intro x hx
    obtain ⟨K, t, ht, hft⟩ := hf hx.1
    obtain ⟨v, hv, hvt⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp ht
    obtain ⟨u, huv, hu_open, hxu⟩ := mem_nhds_iff.mp hv
    let w : Set E := u ∩ s
    have hfw : LipschitzOnWith K f w := by
      apply hft.mono
      intro y hy
      exact hvt ⟨huv hy.1, hy.2⟩
    have hlocal : μ (N ∩ w) = 0 := by
      rw [_root_.MeasureTheory.measure_eq_zero_iff_ae_notMem]
      filter_upwards [hfw.ae_differentiableWithinAt_of_mem (μ := μ)] with y hy
      intro hyNw
      have hyu : y ∈ u := hyNw.2.1
      have hd : DifferentiableWithinAt ℝ f s y := (hy hyNw.2).congr_nhds <| by
        exact nhdsWithin_inter_of_mem
          (mem_nhdsWithin_of_mem_nhds (hu_open.mem_nhds hyu))
      exact hyNw.1.2 hd
    refine ⟨N ∩ w, ?_, hlocal⟩
    apply Filter.mem_of_superset (inter_mem_nhdsWithin N (hu_open.mem_nhds hxu))
    intro y hy
    exact ⟨hy.1, hy.2, hy.1.1⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hN] with x hx
  intro hxs
  by_contra hxd
  exact hx ⟨hxs, hxd⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.LocallyLipschitzOn
  let env ← Lean.getEnv
  if env.contains `LocallyLipschitzOn.ae_differentiableWithinAt_of_mem then
    throwError "Refusing to shadow existing declaration LocallyLipschitzOn.ae_differentiableWithinAt_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `LocallyLipschitzOn.ae_differentiableWithinAt_of_mem ``Submission.LocallyLipschitzOn.ae_differentiableWithinAt_of_mem

open _root_.LocallyLipschitzOn in
theorem LocallyLipschitzOn.ae_differentiableAt_of_isOpen
    {f : E → F} {s : Set E} (hf : LocallyLipschitzOn s f) (hs : IsOpen s) :
    ∀ᵐ x ∂μ, x ∈ s → DifferentiableAt ℝ f x := by
  filter_upwards [hf.ae_differentiableWithinAt_of_mem (μ := μ)] with x hx
  intro hxs
  exact (hx hxs).differentiableAt (hs.mem_nhds hxs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LocallyLipschitzOn.ae_differentiableAt_of_isOpen then
    throwError "Refusing to shadow existing declaration LocallyLipschitzOn.ae_differentiableAt_of_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `LocallyLipschitzOn.ae_differentiableAt_of_isOpen ``Submission.LocallyLipschitzOn.ae_differentiableAt_of_isOpen
