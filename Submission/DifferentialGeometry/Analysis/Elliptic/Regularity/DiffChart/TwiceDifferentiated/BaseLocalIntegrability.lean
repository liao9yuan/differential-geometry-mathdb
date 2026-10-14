import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.CanonicalDerivedData
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.VariationalIdentity
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.ThirdMixedPartial
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.EffectiveSource
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.FChartResidual.ResidualMemW1p
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.SmoothCoefWeakPartialIBP
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TwiceDifferentiatedVariationalIdentity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DifferentiatedCrossTermIBP
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DifferentiatedVariationalIdentity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChosenThirdMixedPartialChartPushed
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartSecondOrderEffectiveSource
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.FChartResidualMemW1p
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartChosenFirstPartial

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private lemma base_weak_partial_ae_eq_chartPushedChosenFirstPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).weakPartial i =ᵐ[
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      Analysis.Laplacian.DiffChartChosenFirstPartial.chartPushedChosenFirstPartial
        (I := I) (M := M) g α u_h i :=
  chartPushedWeakPartialLp_ae_eq_chosenFirstPartial_on_chartTarget
    (I := I) (M := M) g α hu_h i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.base_weak_partial_ae_eq_chartPushedChosenFirstPartial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.base_weak_partial_ae_eq_chartPushedChosenFirstPartial target :: scope.openDecls } }

private lemma base_weak_partial_memW1p
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      ((chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).weakPartial i)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_memWkp_2 : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_pair := laplacianDomainPow_two_h2_plus_rhs_h2
      (I := I) (M := M) g hu_h
    exact h_pair.1.1 α
  have h_chosen_memWkp_1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 2
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
          (d := Module.finrank ℝ E) 2 i
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_memWkp_2.chosenWeakPartial_mem i
  have h_chosen :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
          (d := Module.finrank ℝ E) 2 i
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
            (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p).mp
      h_chosen_memWkp_1
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  exact (MemW1p_congr_ae hΩ_open
    (base_weak_partial_ae_eq_chartPushedChosenFirstPartial
      (I := I) (M := M) g α hu_h i)).mpr h_chosen

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.base_weak_partial_memW1p
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.base_weak_partial_memW1p target :: scope.openDecls } }

private lemma chosenWeakPartialOrZero_base_weak_partial_ae_eq_chosenSecond
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
        (d := Module.finrank ℝ E) 2 l₂
        ((chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).weakPartial l₁)
        (chartTargetEuclid (I := I) (M := M) α) =ᵐ[
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂ := by
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_aeEq :=
    base_weak_partial_ae_eq_chartPushedChosenFirstPartial
      (I := I) (M := M) g α hu_h l₁
  have h_congr :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero_ae_congr
      (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_aeEq l₂
  exact h_congr

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.chosenWeakPartialOrZero_base_weak_partial_ae_eq_chosenSecond
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.chosenWeakPartialOrZero_base_weak_partial_ae_eq_chosenSecond target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
lemma base_u_chart_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp ((chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        hu_h).uChart) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) := by
  set D := chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α hu_h
  have h_weighted := D.u_chart_memLp_weighted
  obtain ⟨c, _hc_pos, h_le⟩ :=
    volume_restrict_compact_le_chartPulledWeightedMeasure (I := I) (M := M)
      (g := g) (α := α) hK_compact hK_meas hK_in
  have hc_ne_top : (ENNReal.ofReal c) ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have h_smul : _root_.MeasureTheory.MemLp D.uChart 2
      (ENNReal.ofReal c •
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) :=
    h_weighted.smul_measure hc_ne_top
  exact h_smul.mono_measure h_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.base_u_chart_locally_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.base_u_chart_locally_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.base_u_chart_locally_memLp ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.base_u_chart_locally_memLp

omit [SigmaCompactSpace M] in
lemma base_f_chart_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp ((chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        hu_h).fChart) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) := by
  set D := chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α hu_h
  have h_weighted := D.f_chart_memLp_weighted
  obtain ⟨c, _hc_pos, h_le⟩ :=
    volume_restrict_compact_le_chartPulledWeightedMeasure (I := I) (M := M)
      (g := g) (α := α) hK_compact hK_meas hK_in
  have hc_ne_top : (ENNReal.ofReal c) ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have h_smul : _root_.MeasureTheory.MemLp D.fChart 2
      (ENNReal.ofReal c •
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) :=
    h_weighted.smul_measure hc_ne_top
  exact h_smul.mono_measure h_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.base_f_chart_locally_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.base_f_chart_locally_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.base_f_chart_locally_memLp ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.base_f_chart_locally_memLp

omit [SigmaCompactSpace M] in
lemma base_weak_partial_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp ((chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        hu_h).weakPartial i) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) :=
  (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α hu_h
    ).weak_partial_locally_memLp i K hK_compact hK_in

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.base_weak_partial_locally_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.base_weak_partial_locally_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.base_weak_partial_locally_memLp ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.base_weak_partial_locally_memLp

private lemma chosenWeakPartial_base_wp_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    _root_.MeasureTheory.MemLp (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
        (d := Module.finrank ℝ E) 2 l₂
        ((chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).weakPartial l₁)
        (chartTargetEuclid (I := I) (M := M) α)) 2
      ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K) := by
  have h_w1p := base_weak_partial_memW1p (I := I) (M := M) g α hu_h l₁
  have h_global :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
      h_w1p l₂
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_eq : ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict K =
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [← h_eq]
  exact h_global.restrict K

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.chosenWeakPartial_base_wp_locally_memLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.chosenWeakPartial_base_wp_locally_memLp target :: scope.openDecls } }

private lemma integral_chosenWeakPartial_base_eq_integral_chosenSecond
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E))
    (ψ : EuclN → ℝ) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartialOrZero
          (d := Module.finrank ℝ E) 2 l₂
          ((chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h)).weakPartial l₁)
          (chartTargetEuclid (I := I) (M := M) α)) y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
        chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
      ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) := by
  have h_aeEq := chosenWeakPartialOrZero_base_weak_partial_ae_eq_chosenSecond
    (I := I) (M := M) g α hu_h l₁ l₂
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h_aeEq] with y hy
  rw [hy]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.integral_chosenWeakPartial_base_eq_integral_chosenSecond
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity.integral_chosenWeakPartial_base_eq_integral_chosenSecond target :: scope.openDecls } }

end TwiceDifferentiatedVariationalIdentity
end Laplacian
end Analysis
end DifferentialGeometry

end
