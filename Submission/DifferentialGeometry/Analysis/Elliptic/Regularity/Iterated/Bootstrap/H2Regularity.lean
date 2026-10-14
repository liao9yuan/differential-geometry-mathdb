import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Defs
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.WeakPartialOnVolume
import Submission.DifferentialGeometry.Analysis.Sobolev.Approximation.Density.Smooth

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
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplToLpChartBridge
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartPushed_lp_class_locally_memLp_volume
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_lp : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    _root_.MeasureTheory.MemLp
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        ((u_lp : M → ℝ))) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) := by
  classical
  have h_lp_meas : Measurable ((u_lp : M → ℝ)) :=
    (Lp.stronglyMeasurable u_lp).measurable
  have h_lp_memLp_global : _root_.MeasureTheory.MemLp ((u_lp : M → ℝ)) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := Lp.memLp u_lp
  have h_memLp_w := chartPushed_memLp_chartPulledWeightedMeasure_restrict_of_memLp
    (I := I) (M := M) g α h_lp_meas h_lp_memLp_global
  exact memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure
    h_memLp_w hK_compact hK_compact.isClosed.measurableSet hK_in

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.chartPushed_lp_class_locally_memLp_volume
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.chartPushed_lp_class_locally_memLp_volume target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkpChart_zero_of_lp
    (g : SmoothRiemannianMetric I M)
    (u_lp : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    MemWkpChart (I := I) (M := M) 0 2 ((u_lp : M → ℝ)) := by
  intro α
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_zero]
  set K : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_in_target : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have h_memLp_K : _root_.MeasureTheory.MemLp
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        ((u_lp : M → ℝ))) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) :=
    chartPushed_lp_class_locally_memLp_volume (I := I) (M := M) g α u_lp
      hK_compact hK_in_target
  set f : EuclN → ℝ := chartPushed (I := I) (M := M)
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α ((u_lp : M → ℝ))
    with hf_def
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_chart_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_measurableSet
      (I := I) (M := M) α
  have h_zero_off : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α, y ∉ K → f y = 0 :=
    fun y hy hy_off => chartPushed_eq_zero_off_chartImagePOUTsupport
      (I := I) (M := M) α ((u_lp : M → ℝ)) hy hy_off
  have h_pointwise_eq : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      f y = Set.indicator K f y := by
    intro y hy
    by_cases hyK : y ∈ K
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, h_zero_off y hy hyK]
  have h_ind_memLp_global : _root_.MeasureTheory.MemLp (Set.indicator K f) 2 (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
    rw [MeasureTheory.memLp_indicator_iff_restrict hK_meas]
    exact h_memLp_K
  have h_ind_memLp_chartTarget : _root_.MeasureTheory.MemLp (Set.indicator K f) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    h_ind_memLp_global.restrict _
  have h_ae_eq : (fun y => f y) =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => Set.indicator K f y) :=
    (MeasureTheory.ae_restrict_iff' h_chart_meas).mpr
      (Filter.Eventually.of_forall (fun y hy => h_pointwise_eq y hy))
  exact h_ind_memLp_chartTarget.ae_eq h_ae_eq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.memWkpChart_zero_of_lp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.memWkpChart_zero_of_lp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.memWkpChart_zero_of_lp ``Submission.DifferentialGeometry.Analysis.Laplacian.memWkpChart_zero_of_lp

omit [NeZero (Module.finrank ℝ E)] in
theorem iteratedH2Regularity_zero
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) 0 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  memWkpChart_zero_of_lp (I := I) (M := M) g
    (H1ComplToLp (I := I) (M := M) g u_h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.iteratedH2Regularity_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.iteratedH2Regularity_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.iteratedH2Regularity_zero ``Submission.DifferentialGeometry.Analysis.Laplacian.iteratedH2Regularity_zero

theorem iteratedH2Regularity_one
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 1) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) 2 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) 2 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  rw [laplacianDomainPow_one] at hu_h
  exact laplacianDomain_memWkpChart_two
    (I := I) (M := M) g hu_h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.iteratedH2Regularity_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.iteratedH2Regularity_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.iteratedH2Regularity_one ``Submission.DifferentialGeometry.Analysis.Laplacian.iteratedH2Regularity_one

theorem laplacianDomainPow_memWkpChart_two_k_le_one
    (g : SmoothRiemannianMetric I M)
    {k : ℕ} (hk : k ≤ 1)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  interval_cases k
  · simpa using iteratedH2Regularity_zero (I := I) (M := M) g u_h
  · have h_one : 2 * 1 = 2 := by norm_num
    rw [h_one]
    exact (iteratedH2Regularity_one (I := I) (M := M) g hu_h).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_memWkpChart_two_k_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_memWkpChart_two_k_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_memWkpChart_two_k_le_one ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_memWkpChart_two_k_le_one

end Laplacian
end Analysis
end DifferentialGeometry

end
