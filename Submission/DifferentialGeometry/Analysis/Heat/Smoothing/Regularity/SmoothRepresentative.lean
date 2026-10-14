import Submission.DifferentialGeometry.Analysis.Heat.Semigroup.Defs
import Submission.DifferentialGeometry.Analysis.Heat.Semigroup.SpectralBounds
import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Embedding.Iterated
import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Embedding.IteratedSmooth
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.MeasureComparison
import Submission.DifferentialGeometry.Analysis.Sobolev.Solutions.SobolevToCinftyRep
import Mathlib.MeasureTheory.Measure.OpenPos

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

theorem smooth_representative_of_memWkpChart_forall
    (g : SmoothRiemannianMetric I M)
    (u : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (h_iterated_regularity :
      ∀ k : ℕ,
        DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
          (I := I) (M := M) (2 * k) 2
          (u : M → ℝ)) :
    ∃ u_smooth : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ u_smooth ∧
      (u : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] u_smooth := by
  classical
  have hu_coe_aesm :
      _root_.MeasureTheory.AEStronglyMeasurable
        (u : M → ℝ)
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
    Lp.aestronglyMeasurable _
  let u_meas : M → ℝ := hu_coe_aesm.mk _
  have hu_meas_strong : _root_.MeasureTheory.StronglyMeasurable u_meas :=
    hu_coe_aesm.stronglyMeasurable_mk
  have hu_meas_meas : Measurable u_meas := hu_meas_strong.measurable
  have hu_coe_ae_meas :
      (u : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] u_meas :=
    hu_coe_aesm.ae_eq_mk
  have h_S_null : (riemannianVolumeMeasure (I := I) (M := M) g)
      {x : M | (u : M → ℝ) x ≠
          u_meas x} = 0 := by
    have := hu_coe_ae_meas
    rwa [Filter.EventuallyEq, MeasureTheory.ae_iff] at this
  obtain ⟨N, hSN, hN_meas, hN_null⟩ :=
    MeasureTheory.exists_measurable_superset_of_null h_S_null
  let d : M → ℝ := N.indicator (fun _ : M => (1 : ℝ))
  have hd_meas : Measurable d :=
    measurable_const.indicator hN_meas
  have hd_ae_zero : d =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
      (fun _ : M => (0 : ℝ)) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ hN_null
    intro x hx
    by_contra hxN
    apply hx
    exact Set.indicator_of_notMem hxN _
  have h_chartPushed_d_ae_zero : ∀ α : M,
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α d =ᵐ[
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α)]
      (fun _ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => (0 : ℝ)) := by
    intro α
    have h :=
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_aeEq_of_ae_eq_riemannianMeasure
        (I := I) (M := M) g α hd_meas measurable_const hd_ae_zero
    have h_raw_zero :
        DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
            (fun _ : M => (0 : ℝ)) =
          (fun _ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => (0 : ℝ)) := by
      funext y
      classical
      unfold DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw
      split_ifs <;> rfl
    rw [h_raw_zero] at h
    exact h
  have h_chartTargetMeas : ∀ α : M, MeasurableSet
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := fun α =>
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  have h_pushed_aeEq :
      DifferentialGeometry.Analysis.Sobolev.Chart.ChartPushedAEEq
        (I := I) (M := M)
        (u : M → ℝ)
        u_meas := by
    intro α
    have h := h_chartPushed_d_ae_zero α
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (h_chartTargetMeas α)] at h
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (h_chartTargetMeas α)]
    filter_upwards [h] with y hy hy_in
    have hd_y :
        d ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 := by
      rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
        (I := I) (M := M) α d hy_in] at hy
      exact hy hy_in
    have h_notN : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∉ N := by
      intro h_mem
      apply (by norm_num : (1 : ℝ) ≠ 0)
      rw [← Set.indicator_of_mem h_mem (fun _ : M => (1 : ℝ))]
      exact hd_y
    have h_notS : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∉
        {x : M | (u : M → ℝ) x ≠
            u_meas x} := fun h => h_notN (hSN h)
    have h_eq :
        (u : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
        u_meas ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
      by_contra hne
      exact h_notS hne
    unfold DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
    rw [h_eq]
  have h_iter_meas : ∀ k : ℕ,
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) (2 * k) 2 u_meas := by
    intro k
    exact (DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_congr_chartPushed_ae
      (I := I) (M := M) (k := 2 * k) (p := 2)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_pushed_aeEq).mp
      (h_iterated_regularity k)
  obtain ⟨u_smooth, h_smooth, h_smooth_ae_meas⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.sobolev_smooth_representative_of_memWkpChart_forall
      (I := I) (M := M) g (u := u_meas) hu_meas_meas h_iter_meas
  refine ⟨u_smooth, h_smooth, ?_⟩
  exact hu_coe_ae_meas.trans h_smooth_ae_meas.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.smooth_representative_of_memWkpChart_forall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.smooth_representative_of_memWkpChart_forall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.smooth_representative_of_memWkpChart_forall ``Submission.DifferentialGeometry.Analysis.HeatEquation.smooth_representative_of_memWkpChart_forall

theorem heatSemigroup_smooth_representative
    (g : SmoothRiemannianMetric I M)
    {t : ℝ}
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (h_iterated_regularity :
      ∀ k : ℕ,
        DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
          (I := I) (M := M) (2 * k) 2
          ((heatSemigroup (I := I) (M := M) g t u_0 :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :
    ∃ u_smooth : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ u_smooth ∧
      ((heatSemigroup (I := I) (M := M) g t u_0 :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] u_smooth :=
  smooth_representative_of_memWkpChart_forall (I := I) (M := M) g
    (heatSemigroup (I := I) (M := M) g t u_0) h_iterated_regularity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_representative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_representative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_representative ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_representative

theorem heatSemigroup_contMDiff_in_time
    (g : SmoothRiemannianMetric I M)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ContDiffOn ℝ ∞
      (fun t : ℝ =>
        (heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)))
      (Set.Ioi (0 : ℝ)) := by
  have h_op : ContDiffOn ℝ ∞
      (fun t : ℝ => (heatSemigroup (I := I) (M := M) g t :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)))
      (Set.Ioi 0) :=
    contDiffOn_heatSemigroup_Ioi (I := I) (M := M) g
  let evalAt :
      (_root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    ContinuousLinearMap.apply ℝ
      (_root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) u_0
  have h_eval_smooth : ContDiff ℝ ∞ evalAt := evalAt.contDiff
  exact h_eval_smooth.contDiffOn.comp h_op (Set.mapsTo_univ _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_contMDiff_in_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_contMDiff_in_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_contMDiff_in_time ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_contMDiff_in_time

theorem heatSemigroup_smooth_in_space_and_time_of_iterated_regularity
    (g : SmoothRiemannianMetric I M)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (h_iterated_regularity_uniform :
      ∀ t : ℝ, 0 < t → ∀ k : ℕ,
        DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
          (I := I) (M := M) (2 * k) 2
          ((heatSemigroup (I := I) (M := M) g t u_0 :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :
    (∀ t : ℝ, 0 < t →
      ∃ u_smooth_t : M → ℝ,
        ContMDiff I 𝓘(ℝ, ℝ) ∞ u_smooth_t ∧
        ((heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
            riemannianVolumeMeasure (I := I) (M := M) g] u_smooth_t) ∧
    ContDiffOn ℝ ∞
      (fun t : ℝ =>
        (heatSemigroup (I := I) (M := M) g t u_0 :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)))
      (Set.Ioi (0 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    exact heatSemigroup_smooth_representative (I := I) (M := M) g u_0
      (h_iterated_regularity_uniform t ht)
  · exact heatSemigroup_contMDiff_in_time (I := I) (M := M) g u_0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_in_space_and_time_of_iterated_regularity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_in_space_and_time_of_iterated_regularity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_in_space_and_time_of_iterated_regularity ``Submission.DifferentialGeometry.Analysis.HeatEquation.heatSemigroup_smooth_in_space_and_time_of_iterated_regularity

end HeatEquation
end Analysis
end DifferentialGeometry

end
