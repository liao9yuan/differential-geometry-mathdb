import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.MixedPartials
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.VariationalIdentity.LeibnizCoefficients
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.CanonicalDerivedData
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.VariationalIdentity
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.ChosenFChartDerivMemW1p
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.BaseFChart.MemWkpTwoTwo
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.EffectiveSource
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.EffectiveSource
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Chart.VariationalData
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.ChosenFirstPartialW1p

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedDifferentiatedData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedMixedPartials
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartChosenFirstPartial
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.CanonicalDerivedChartBilinearH1ComplData
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartSecondOrderEffectiveSource
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChosenThirdMixedPartialChartPushed
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

structure IteratedDiffChartBilinearData
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ) where
  directions : Fin m → Fin (Module.finrank ℝ E)
  diffChartForcing : EuclN → ℝ
  fChartEffective_memLp_weighted :
    _root_.MeasureTheory.MemLp diffChartForcing 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))
  m_diff_variational_identity :
    ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                (m + 1) (Fin.cons i directions) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
            m directions y * ψ y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * diffChartForcing y * ψ y
        ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData

def IteratedDiffChartBilinearData.mkFromHypotheses
    {g : SmoothRiemannianMetric I M} {α : M}
    {u_h : H1Compl (I := I) (M := M) g} {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (diffChartForcing : EuclN → ℝ)
    (fChartEffective_memLp_weighted :
      _root_.MeasureTheory.MemLp diffChartForcing 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
    (m_diff_variational_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                  (m + 1) (Fin.cons i directions) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              m directions y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y * diffChartForcing y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN)) :
    IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m :=
  { directions := directions
    diffChartForcing := diffChartForcing
    fChartEffective_memLp_weighted := fChartEffective_memLp_weighted
    m_diff_variational_identity := m_diff_variational_identity }

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.mkFromHypotheses then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.mkFromHypotheses"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.mkFromHypotheses ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.mkFromHypotheses

namespace IteratedDiffChartBilinearData

omit [NeZero (Module.finrank ℝ E)] in
private lemma m_zero_principal_integrand_eq
    {g : SmoothRiemannianMetric I M} {α : M}
    {u_h : H1Compl (I := I) (M := M) g}
    (y : EuclN) (i j : Fin (Module.finrank ℝ E)) :
    weightedInvGramOnEuclid (I := I) g α i j y *
        chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 1
          (Fin.cons i (Fin.elim0)) y *
        (fderiv ℝ (fun _ : EuclN => (0 : ℝ)) y) (EuclideanSpace.single j 1) =
      weightedInvGramOnEuclid (I := I) g α i j y *
        chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i y *
        (fderiv ℝ (fun _ : EuclN => (0 : ℝ)) y) (EuclideanSpace.single j 1) := by
  rw [chosenMthMixedPartialChartPushedU_one_eq_chosenFirstPartial]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.m_zero_principal_integrand_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.m_zero_principal_integrand_eq target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenMthMixed_one_cons_eq_chartPushedChosenFirstPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) :
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 1
        (Fin.cons i (Fin.elim0)) =
      chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i := by
  rw [chosenMthMixedPartialChartPushedU_one_eq_chosenFirstPartial]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.chosenMthMixed_one_cons_eq_chartPushedChosenFirstPartial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.chosenMthMixed_one_cons_eq_chartPushedChosenFirstPartial target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenMthMixed_zero_elim0_eq_chartPushed
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 0
        (Fin.elim0) =
      chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.chosenMthMixed_zero_elim0_eq_chartPushed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.chosenMthMixed_zero_elim0_eq_chartPushed target :: scope.openDecls } }

private lemma base_u_chart_ae_eq_chartPushed
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        hu_h).uChart =ᵐ[
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) := by
  classical
  have h_coeFn :=
    Analysis.Laplacian.LaplacianDomainVariationalIdentityIntegralForm.chartPushedLpFromLp_coeFn
      (I := I) (M := M) g α (H1ComplToLp (I := I) (M := M) g u_h)
  have h_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have h_v_abs_w :
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro A hA
    unfold chartPulledWeightedMeasure at hA
    rw [show ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
        (chartTargetEuclid (I := I) (M := M) α) =
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).withDensity
          (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      from MeasureTheory.restrict_withDensity h_meas _] at hA
    rw [MeasureTheory.withDensity_apply_eq_zero'
      (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      (ENNReal.measurable_ofReal.comp_aemeasurable
        ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable h_meas))] at hA
    rw [Measure.restrict_apply' h_meas]
    rw [Measure.restrict_apply' h_meas] at hA
    refine MeasureTheory.measure_mono_null ?_ hA
    intro y ⟨hy_A, hy_chart⟩
    refine ⟨⟨?_, hy_A⟩, hy_chart⟩
    have h_pos : 0 < densityOnEuclid (I := I) g α y :=
      densityOnEuclid_pos (I := I) g α hy_chart
    exact (ENNReal.ofReal_pos.mpr h_pos).ne'
  exact h_v_abs_w.ae_le h_coeFn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.base_u_chart_ae_eq_chartPushed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.base_u_chart_ae_eq_chartPushed target :: scope.openDecls } }

private lemma base_weak_partial_ae_eq_chartPushedChosenFirstPartial_aux
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).weakPartial i =ᵐ[
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i :=
  chartPushedWeakPartialLp_ae_eq_chosenFirstPartial_on_chartTarget
    (I := I) (M := M) g α hu_h i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.base_weak_partial_ae_eq_chartPushedChosenFirstPartial_aux
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.base_weak_partial_ae_eq_chartPushedChosenFirstPartial_aux target :: scope.openDecls } }

def ofBase
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    IteratedDiffChartBilinearData (I := I) (M := M) g α u_h 0 where
  directions := Fin.elim0
  diffChartForcing :=
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h)).fChart
  fChartEffective_memLp_weighted :=
    (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h)).f_chart_memLp_weighted
  m_diff_variational_identity := by
    classical
    intro ψ hψ_smooth hψ_cs hψ_support
    set hu_h_lap : u_h ∈ laplacianDomain (I := I) (M := M) g :=
      laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h
    set D := chartBilinearH1ComplDataOfLaplacianDomain
      (I := I) (M := M) g α hu_h_lap with hD_def
    have h_base := D.variational_identity ψ hψ_smooth hψ_cs hψ_support
    have h_wp_ae := base_weak_partial_ae_eq_chartPushedChosenFirstPartial_aux
      (I := I) (M := M) g α hu_h
    have h_u_ae := base_u_chart_ae_eq_chartPushed
      (I := I) (M := M) g α hu_h_lap
    have h_principal_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 1
                  (Fin.cons i (Fin.elim0)) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weakPartial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
      refine MeasureTheory.integral_congr_ae ?_
      have h_wp_all : ∀ i, (chartBilinearH1ComplDataOfLaplacianDomain
            (I := I) (M := M) g α hu_h_lap).weakPartial i =ᵐ[
            (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)]
          chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i :=
        fun i => base_weak_partial_ae_eq_chartPushedChosenFirstPartial_aux
          (I := I) (M := M) g α hu_h i
      have h_ae_eqs : ∀ i,
          ∀ᵐ y ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)),
            chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i y =
            (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M)
              g α hu_h_lap).weakPartial i y := by
        intro i
        filter_upwards [h_wp_all i] with y hy
        exact hy.symm
      have h_all_ae :
          ∀ᵐ y ∂((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)),
            ∀ i : Fin (Module.finrank ℝ E),
              chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i y =
              (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M)
                g α hu_h_lap).weakPartial i y := by
        rw [Filter.eventually_all]
        exact h_ae_eqs
      filter_upwards [h_all_ae] with y hy
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [chosenMthMixed_one_cons_eq_chartPushedChosenFirstPartial
        (I := I) (M := M) g α u_h i, hy i]
    have h_mass_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 0
              (Fin.elim0) y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            D.uChart y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [h_u_ae] with y hy
      rw [chosenMthMixed_zero_elim0_eq_chartPushed]
      rw [hy]
    rw [h_principal_eq, h_mass_eq]
    exact h_base

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.ofBase then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.ofBase"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.ofBase ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.ofBase

end IteratedDiffChartBilinearData

namespace IteratedDiffChartBilinearData

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenMthMixed_two_cons_const_eq_chosenSecond
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (i l : Fin (Module.finrank ℝ E)) :
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 2
        (Fin.cons i (fun _ : Fin 1 => l)) =
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l := by
  apply chosenMthMixedPartialChartPushedU_two_eq_chosenSecondPartialChartPushedU
  · rfl
  · rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.chosenMthMixed_two_cons_const_eq_chosenSecond
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.chosenMthMixed_two_cons_const_eq_chosenSecond target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenMthMixed_one_const_eq_chartPushedChosenFirstPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (l : Fin (Module.finrank ℝ E)) :
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 1
        (fun _ : Fin 1 => l) =
      chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l := by
  rw [chosenMthMixedPartialChartPushedU_one_eq_chosenFirstPartial]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.chosenMthMixed_one_const_eq_chartPushedChosenFirstPartial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.chosenMthMixed_one_const_eq_chartPushedChosenFirstPartial target :: scope.openDecls } }

def ofDiff
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l : Fin (Module.finrank ℝ E)) :
    IteratedDiffChartBilinearData (I := I) (M := M) g α u_h 1 where
  directions := fun _ => l
  diffChartForcing :=
    DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcing
      (I := I) (M := M) g α l hu_h
  fChartEffective_memLp_weighted :=
    DifferentialGeometry.Analysis.Laplacian.DiffChartEffectiveSource.diffChartForcing_memLp_two_weighted
      (I := I) (M := M) (g := g) (α := α) (l := l) (hu_h := hu_h)
  m_diff_variational_identity := by
    classical
    intro ψ hψ_smooth hψ_cs hψ_support
    have h_once := derived_chart_variational_identity
      (I := I) (M := M) g α l hu_h hψ_smooth hψ_cs hψ_support
    have h_principal_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 2
                  (Fin.cons i (fun _ : Fin 1 => l)) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
      refine MeasureTheory.setIntegral_congr_fun
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet ?_
      intro y _hy
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [chosenMthMixed_two_cons_const_eq_chosenSecond
        (I := I) (M := M) g α u_h i l]
    have h_wp_ae :=
      base_weak_partial_ae_eq_chartPushedChosenFirstPartial_aux
        (I := I) (M := M) g α hu_h l
    have h_mass_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 1
              (fun _ : Fin 1 => l) y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weakPartial l y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [h_wp_ae] with y hy
      rw [chosenMthMixed_one_const_eq_chartPushedChosenFirstPartial
        (I := I) (M := M) g α u_h l]
      rw [← hy]
    rw [h_principal_eq, h_mass_eq]
    exact h_once

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.ofDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.ofDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.ofDiff ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.ofDiff

end IteratedDiffChartBilinearData

namespace IteratedDiffChartBilinearData

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenMthMixed_three_cons_two_eq_chosenThird
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (i l₁ l₂ : Fin (Module.finrank ℝ E)) :
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 3
        (Fin.cons i (![l₁, l₂])) =
      chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ l₂ := by
  apply chosenMthMixedPartialChartPushedU_three_eq_chosenThirdMixedPartialChartPushedU
  · rfl
  · rfl
  · rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.chosenMthMixed_three_cons_two_eq_chosenThird
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.chosenMthMixed_three_cons_two_eq_chosenThird target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenMthMixed_two_pair_eq_chosenSecond
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (l₁ l₂ : Fin (Module.finrank ℝ E)) :
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 2
        (![l₁, l₂]) =
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂ := by
  apply chosenMthMixedPartialChartPushedU_two_eq_chosenSecondPartialChartPushedU
  · rfl
  · rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.chosenMthMixed_two_pair_eq_chosenSecond
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.chosenMthMixed_two_pair_eq_chosenSecond target :: scope.openDecls } }

def ofDiffTwice
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E)) :
    IteratedDiffChartBilinearData (I := I) (M := M) g α u_h 2 where
  directions := ![l₁, l₂]
  diffChartForcing :=
    DifferentialGeometry.Analysis.Laplacian.DiffChartSecondOrderEffectiveSource.effectiveSourceChartSecondOrder
      (I := I) (M := M) g α l₁ l₂ hu_h
  fChartEffective_memLp_weighted :=
    DifferentialGeometry.Analysis.Laplacian.DiffChartSecondOrderEffectiveSource.fChartEffectiveTwice_memLp_two_weighted
      (I := I) (M := M) (g := g) (α := α) (l₁ := l₁) (l₂ := l₂) (hu_h := hu_h)
  m_diff_variational_identity := by
    classical
    intro ψ hψ_smooth hψ_cs hψ_support
    have h_base_f_chart_memWkp22 :=
      base_f_chart_memWkp_two_two
        (I := I) (M := M) g α hu_h
    have h_chosenFChartDeriv_memW1p :=
      chosenFChartDeriv_memW1p
        (I := I) (M := M) g α hu_h l₁ h_base_f_chart_memWkp22
    have h_twice := twice_differentiated_variational_identity_holds
      (I := I) (M := M) g α hu_h l₁ l₂ h_chosenFChartDeriv_memW1p
      hψ_smooth hψ_cs hψ_support
    have h_principal_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 3
                  (Fin.cons i (![l₁, l₂])) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ l₂ y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
      refine MeasureTheory.setIntegral_congr_fun
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet ?_
      intro y _hy
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [chosenMthMixed_three_cons_two_eq_chosenThird
        (I := I) (M := M) g α u_h i l₁ l₂]
    have h_mass_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 2
              (![l₁, l₂]) y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenSecondPartialChartPushedU
              (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN) := by
      refine MeasureTheory.setIntegral_congr_fun
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet ?_
      intro y _hy
      rw [chosenMthMixed_two_pair_eq_chosenSecond
        (I := I) (M := M) g α u_h l₁ l₂]
    rw [h_principal_eq, h_mass_eq]
    exact h_twice

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.ofDiffTwice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.ofDiffTwice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.ofDiffTwice ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData.IteratedDiffChartBilinearData.ofDiffTwice

end IteratedDiffChartBilinearData

end IteratedDifferentiatedData
end Laplacian
end Analysis
end DifferentialGeometry

end
