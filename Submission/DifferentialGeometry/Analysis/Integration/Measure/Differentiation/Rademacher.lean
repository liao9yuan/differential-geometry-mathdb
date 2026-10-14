import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.NullSets
import Mathlib.Analysis.Calculus.Rademacher

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.NNReal

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

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

theorem local_diff_ae
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {f : E → F} {s : Set E} (hf : LocallyLipschitzOn s f) :
    ∀ᵐ x ∂(modelHaar (E := E)),
      x ∈ s → DifferentiableWithinAt ℝ f s x := by
  let N : Set E := {x : E | x ∈ s ∧ ¬ DifferentiableWithinAt ℝ f s x}
  have hN : modelHaar (E := E) N = 0 := by
    apply _root_.MeasureTheory.measure_null_of_locally_null N
    intro x hx
    obtain ⟨K, t, ht, hft⟩ := hf hx.1
    obtain ⟨v, hv, hvt⟩ :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mp ht
    obtain ⟨u, huv, hu_open, hxu⟩ := mem_nhds_iff.mp hv
    let w : Set E := u ∩ s
    have hfw : LipschitzOnWith K f w := by
      apply hft.mono
      intro y hy
      exact hvt ⟨huv hy.1, hy.2⟩
    have hlocal : modelHaar (E := E) (N ∩ w) = 0 := by
      rw [_root_.MeasureTheory.measure_eq_zero_iff_ae_notMem]
      filter_upwards [hfw.ae_differentiableWithinAt_of_mem] with y hy
      intro hyNw
      have hys : y ∈ s := hyNw.2.2
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
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.local_diff_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.local_diff_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.local_diff_ae ``Submission.DifferentialGeometry.Integral.Measure.local_diff_ae

theorem chart_nondiff_null
    [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x₀ : M) (C : ℝ≥0)
    (hf : LipschitzOnWith C (f ∘ (extChartAt I x₀).symm)
      (extChartAt I x₀).target) :
    riemannianVolumeMeasure (I := I) (M := M) g
      ((chartAt H x₀).source ∩
        {x : M | ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) f x}) = 0 := by
  let N : Set E := {y : E | ¬ DifferentiableWithinAt ℝ
    (f ∘ (extChartAt I x₀).symm) (Set.range I) y}
  have hN : modelHaar (E := E) (N ∩ (extChartAt I x₀).target) = 0 := by
    rw [_root_.MeasureTheory.measure_eq_zero_iff_ae_notMem]
    filter_upwards [hf.ae_differentiableWithinAt_of_mem] with y hy
    intro hyN
    exact hyN.1 ((hy hyN.2).congr_nhds
      (nhdsWithin_extChartAt_target_eq_of_mem hyN.2))
  have hpull := chart_model_null (I := I) (M := M) g x₀ hN
  have hset :
      (chartAt H x₀).source ∩
          {x : M | (extChartAt I x₀) x ∈ N} =
        (chartAt H x₀).source ∩
          {x : M | ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) f x} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, N]
    refine and_congr_right_iff.mpr fun hx ↦ ?_
    rw [mdifferentiableAt_iff_source_of_mem_source hx,
      mdifferentiableWithinAt_iff_differentiableWithinAt]
  rwa [hset] at hpull

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chart_nondiff_null then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chart_nondiff_null"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chart_nondiff_null ``Submission.DifferentialGeometry.Integral.Measure.chart_nondiff_null

theorem chart_local_null
    [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x₀ : M)
    (hf : LocallyLipschitzOn (extChartAt I x₀).target
      (f ∘ (extChartAt I x₀).symm)) :
    riemannianVolumeMeasure (I := I) (M := M) g
      ((chartAt H x₀).source ∩
        {x : M | ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) f x}) = 0 := by
  let N : Set E := {y : E | ¬ DifferentiableWithinAt ℝ
    (f ∘ (extChartAt I x₀).symm) (Set.range I) y}
  have hN : modelHaar (E := E) (N ∩ (extChartAt I x₀).target) = 0 := by
    rw [_root_.MeasureTheory.measure_eq_zero_iff_ae_notMem]
    filter_upwards [local_diff_ae hf] with y hy
    intro hyN
    exact hyN.1 ((hy hyN.2).congr_nhds
      (nhdsWithin_extChartAt_target_eq_of_mem hyN.2))
  have hpull := chart_model_null (I := I) (M := M) g x₀ hN
  have hset :
      (chartAt H x₀).source ∩
          {x : M | (extChartAt I x₀) x ∈ N} =
        (chartAt H x₀).source ∩
          {x : M | ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) f x} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, N]
    refine and_congr_right_iff.mpr fun hx ↦ ?_
    rw [mdifferentiableAt_iff_source_of_mem_source hx,
      mdifferentiableWithinAt_iff_differentiableWithinAt]
  rwa [hset] at hpull

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.chart_local_null then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.chart_local_null"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.chart_local_null ``Submission.DifferentialGeometry.Integral.Measure.chart_local_null

theorem nondiff_null
    [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ∀ x₀ : M, LocallyLipschitzOn (extChartAt I x₀).target
      (f ∘ (extChartAt I x₀).symm)) :
    riemannianVolumeMeasure (I := I) (M := M) g
      {x : M | ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) f x} = 0 := by
  classical
  obtain ⟨s, hs⟩ := finite_chart_cover (H := H) (M := M)
  apply null_of_chart_cover (H := H)
    (riemannianVolumeMeasure (I := I) (M := M) g)
    {x : M | ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) f x} s
  · simpa only [hs] using (Set.subset_univ
      {x : M | ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) f x})
  · intro x₀ hx₀
    rw [Set.inter_comm]
    exact chart_local_null (I := I) (M := M) g f x₀ (hf x₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.nondiff_null then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.nondiff_null"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.nondiff_null ``Submission.DifferentialGeometry.Integral.Measure.nondiff_null

end Measure
end Integral
end DifferentialGeometry
