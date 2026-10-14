import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.ChartHm
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.ChartHmPolymorphic
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.ChartHmDomainPow
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.InteriorH2
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.EffectiveSourceRegularity
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.EffectiveSourceSuccessorRegularity
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.BaseFChart.PolymorphicRegularity
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.VariationalIdentity.DifferentiatedData
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.VariationalIdentity.InductiveSuccessor
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.MixedPartials
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Powers.EvenOrderBridge
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2Regularity
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2RegularitySuccessor
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Defs
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
namespace IteratedChartHmBootstrapStrongInduction

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
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedMixedPartials
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrap
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFour

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartSideH2kBridge_mono_of_le
    {k j : ℕ} (hjk : j ≤ k)
    {u : M → ℝ}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) k u) :
    ChartSideH2kBridge (I := I) (M := M) j u := by
  intro α
  have h := h_bridge α
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le
    (by omega : 2 * j ≤ 2 * k) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartSideH2kBridge_mono_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartSideH2kBridge_mono_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartSideH2kBridge_mono_of_le ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartSideH2kBridge_mono_of_le

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_j_of_chartSideH2kBridge_at
    (g : SmoothRiemannianMetric I M) (α : M) {k j : ℕ} (hjk : j ≤ 2 * k)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) j 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le hjk
    (h_bridge α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_j_of_chartSideH2kBridge_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_j_of_chartSideH2kBridge_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_j_of_chartSideH2kBridge_at ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_j_of_chartSideH2kBridge_at

omit [NeZero (Module.finrank ℝ E)] in
theorem chosenMthMixed_memWkp_two_two_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M) (α : M) {k m : ℕ} (hm : m + 2 ≤ 2 * k)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)))
    (idx : Fin m → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  classical
  have h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    chartPushed_memWkp_j_of_chartSideH2kBridge_at
      (I := I) (M := M) g α (k := k) (j := m + 2) hm h_bridge
  have h_parent' : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 + m) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
    have h_eq : 2 + m = m + 2 := Nat.add_comm 2 m
    rw [h_eq]
    exact h_parent
  exact chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
    (I := I) (M := M) g α u_h m 2 h_parent' idx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chosenMthMixed_memWkp_two_two_of_chartSideH2kBridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chosenMthMixed_memWkp_two_two_of_chartSideH2kBridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chosenMthMixed_memWkp_two_two_of_chartSideH2kBridge ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chosenMthMixed_memWkp_two_two_of_chartSideH2kBridge

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  let _ := hu_h
  exact h_bridge α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_two_k_of_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge
    (I := I) (M := M) g α k hu_h h_bridge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_k_of_laplacianDomainPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_k_of_laplacianDomainPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_k_of_laplacianDomainPow ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_k_of_laplacianDomainPow

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkpChart_two_k_of_laplacianDomainPow_bridge
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k)
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro α
  exact chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge
    (I := I) (M := M) g α k hu_h h_bridge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.memWkpChart_two_k_of_laplacianDomainPow_bridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.memWkpChart_two_k_of_laplacianDomainPow_bridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.memWkpChart_two_k_of_laplacianDomainPow_bridge ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.memWkpChart_two_k_of_laplacianDomainPow_bridge

theorem chartPushed_memWkp_two_k_of_le_two
    (g : SmoothRiemannianMetric I M) (α : M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  have h_bridge :=
    IteratedChartHmBootstrapPolymorphic.chartSideH2kBridge_of_laplacianDomainPow_le_two
      (I := I) (M := M) g hk hu_h
  exact chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge
    (I := I) (M := M) g α k hu_h h_bridge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_k_of_le_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_k_of_le_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_k_of_le_two ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_k_of_le_two

theorem memWkpChart_two_k_of_le_two
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro α
  exact chartPushed_memWkp_two_k_of_le_two
    (I := I) (M := M) g α hk hu_h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.memWkpChart_two_k_of_le_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.memWkpChart_two_k_of_le_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.memWkpChart_two_k_of_le_two ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.memWkpChart_two_k_of_le_two

theorem chartPushed_memWkp_two_min_k_two
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * _root_.Min.min k 2) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  classical
  have h_min_le_2 : _root_.Min.min k 2 ≤ 2 := min_le_right _ _
  have hu_h_min : u_h ∈ laplacianDomainPow (I := I) (M := M) g (_root_.Min.min k 2) :=
    laplacianDomainPow_le_of_le (I := I) (M := M) g (min_le_left _ _) hu_h
  exact chartPushed_memWkp_two_k_of_le_two
    (I := I) (M := M) g α h_min_le_2 hu_h_min

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_min_k_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_min_k_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_min_k_two ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_min_k_two

theorem memWkpChart_two_min_k_two
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) (2 * _root_.Min.min k 2) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro α
  exact chartPushed_memWkp_two_min_k_two
    (I := I) (M := M) g α k hu_h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.memWkpChart_two_min_k_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.memWkpChart_two_min_k_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.memWkpChart_two_min_k_two ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.memWkpChart_two_min_k_two

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_succ_step_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M) (α : M) {k m : ℕ} (hm : m + 2 ≤ 2 * k)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  have h_chart_H_m_plus_1 : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    chartPushed_memWkp_j_of_chartSideH2kBridge_at
      (I := I) (M := M) g α (k := k) (j := m + 1) (by omega) h_bridge
  have h_top_memWkp_two : ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx)
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) :=
    fun idx => chosenMthMixed_memWkp_two_two_of_chartSideH2kBridge
      (I := I) (M := M) g α (k := k) (m := m) hm h_bridge idx
  exact chartPushed_memWkp_m_plus_two_step
    (I := I) (M := M) g α u_h m h_chart_H_m_plus_1 h_top_memWkp_two

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_succ_step_of_chartSideH2kBridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_succ_step_of_chartSideH2kBridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_succ_step_of_chartSideH2kBridge ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_succ_step_of_chartSideH2kBridge

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_two_k_plus_two_two_sided_of_chartSideBridges
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1))
    (h_bridge_u : ChartSideH2kBridge (I := I) (M := M) (k + 1)
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)))
    (h_bridge_rhs : ChartSideH2kBridge (I := I) (M := M) (k + 1)
      (((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g k hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (2 * (k + 1)) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) ∧
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (2 * (k + 1)) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((laplacianDomain.preimage (I := I) (M := M) g
              ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g k hu_h⟩ :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) := by
  refine ⟨?_, ?_⟩
  · exact chartPushed_memWkp_two_k_of_laplacianDomainPow_bridge
      (I := I) (M := M) g α (k + 1) hu_h h_bridge_u
  · exact h_bridge_rhs α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_k_plus_two_two_sided_of_chartSideBridges then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_k_plus_two_two_sided_of_chartSideBridges"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_k_plus_two_two_sided_of_chartSideBridges ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.chartPushed_memWkp_two_k_plus_two_two_sided_of_chartSideBridges

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkpChart_two_k_of_preimage_chartSideBridge
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1))
    (h_bridge_rhs : ChartSideH2kBridge (I := I) (M := M) k
      (((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g k hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) (2 * k) 2
      ((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g k hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro α
  exact h_bridge_rhs α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.memWkpChart_two_k_of_preimage_chartSideBridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.memWkpChart_two_k_of_preimage_chartSideBridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.memWkpChart_two_k_of_preimage_chartSideBridge ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapStrongInduction.memWkpChart_two_k_of_preimage_chartSideBridge

end IteratedChartHmBootstrapStrongInduction
end Laplacian
end Analysis
end DifferentialGeometry

end
