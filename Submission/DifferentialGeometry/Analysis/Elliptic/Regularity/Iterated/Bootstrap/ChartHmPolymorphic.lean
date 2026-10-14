import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.EffectiveSourceRegularity
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.InteriorH2
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.ChartHm
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2RegularitySuccessor
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Powers.EvenOrderBridge
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.MemWkpFour

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedChartHmBootstrapPolymorphic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrap
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFour

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem chartPushed_memWkp_of_laplacianDomainPow_le_two
    (g : SmoothRiemannianMetric I M) (α : M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  interval_cases k
  · have h_zero := iteratedH2Regularity_zero (I := I) (M := M) g u_h α
    have h_eq : (2 : ℕ) * 0 = 0 := by norm_num
    rw [h_eq]
    exact h_zero
  · have h_one := (iteratedH2Regularity_one (I := I) (M := M) g hu_h).1 α
    have h_eq : (2 : ℕ) * 1 = 2 := by norm_num
    rw [h_eq]
    exact h_one
  · have h_two := chartPushed_memWkp_four_two_of_laplacianDomainPow_two
      (I := I) (M := M) g α hu_h
    have h_eq : (2 : ℕ) * 2 = 4 := by norm_num
    rw [h_eq]
    exact h_two

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_of_laplacianDomainPow_le_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_of_laplacianDomainPow_le_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_of_laplacianDomainPow_le_two ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_of_laplacianDomainPow_le_two

theorem chartSideH2kBridge_of_laplacianDomainPow_le_two
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    ChartSideH2kBridge (I := I) (M := M) k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  intro α
  exact chartPushed_memWkp_of_laplacianDomainPow_le_two
    (I := I) (M := M) g α hk hu_h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartSideH2kBridge_of_laplacianDomainPow_le_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartSideH2kBridge_of_laplacianDomainPow_le_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartSideH2kBridge_of_laplacianDomainPow_le_two ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartSideH2kBridge_of_laplacianDomainPow_le_two

theorem memWkpChart_of_laplacianDomainPow_le_two
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro α
  exact chartPushed_memWkp_of_laplacianDomainPow_le_two
    (I := I) (M := M) g α hk hu_h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.memWkpChart_of_laplacianDomainPow_le_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.memWkpChart_of_laplacianDomainPow_le_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.memWkpChart_of_laplacianDomainPow_le_two ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.memWkpChart_of_laplacianDomainPow_le_two

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_of_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) :=
  h_bridge α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_of_laplacianDomainPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_of_laplacianDomainPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_of_laplacianDomainPow ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_of_laplacianDomainPow

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_j_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M) (α : M) {k j : ℕ} (hjk : j ≤ 2 * k)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) j 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le hjk
    (h_bridge α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_j_of_chartSideH2kBridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_j_of_chartSideH2kBridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_j_of_chartSideH2kBridge ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_j_of_chartSideH2kBridge

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_succ_step
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    (u_h : H1Compl (I := I) (M := M) g)
    (h_chart_H_m_plus_1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_top_memWkp_two :
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 2 2
          (Analysis.Laplacian.IteratedMixedPartials.chosenMthMixedPartialChartPushedU
            (I := I) (M := M) g α u_h m idx)
          (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) :=
  chartPushed_memWkp_m_plus_two_step (I := I) (M := M) g α u_h m
    h_chart_H_m_plus_1 h_top_memWkp_two

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_succ_step then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_succ_step"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_succ_step ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_succ_step

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkpChart_2k_of_chartSideH2kBridge_polymorphic
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  fun α => h_bridge α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.memWkpChart_2k_of_chartSideH2kBridge_polymorphic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.memWkpChart_2k_of_chartSideH2kBridge_polymorphic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.memWkpChart_2k_of_chartSideH2kBridge_polymorphic ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.memWkpChart_2k_of_chartSideH2kBridge_polymorphic

theorem chartPushed_memWkp_two_sided_succ_le_two
    (g : SmoothRiemannianMetric I M) (α : M) {k : ℕ} (hk : k + 1 ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1)) :
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (2 * (k + 1)) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α)) ∧
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (2 * k) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((laplacianDomain.preimage (I := I) (M := M) g
              ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g k hu_h⟩ :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  refine ⟨?_, ?_⟩
  · exact chartPushed_memWkp_of_laplacianDomainPow_le_two
      (I := I) (M := M) g α hk hu_h
  · have hk_le_one : k ≤ 1 := by omega
    interval_cases k
    · have h_eq : (2 : ℕ) * 0 = 0 := by norm_num
      rw [h_eq]
      have h_lp := memWkpChart_zero_of_lp (I := I) (M := M) g
        (laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 0 hu_h⟩) α
      exact h_lp
    · have h := laplacianDomainPow_two_iterated_h2 (I := I) (M := M) g hu_h
      have h_eq : (2 : ℕ) * 1 = 2 := by norm_num
      rw [h_eq]
      exact h.2 α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_two_sided_succ_le_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_two_sided_succ_le_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_two_sided_succ_le_two ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic.chartPushed_memWkp_two_sided_succ_le_two

end IteratedChartHmBootstrapPolymorphic
end Laplacian
end Analysis
end DifferentialGeometry

end
