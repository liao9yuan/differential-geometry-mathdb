import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.ChartHmPolymorphic
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.EffectiveSourceSuccessorRegularity
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.EffectiveSourceRegularity
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.InteriorH2
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.BaseFChart.PolymorphicRegularity
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2RegularitySuccessor

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedChartHmBootstrapCanonical

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
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFour

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainPow_le_of_le
    (g : SmoothRiemannianMetric I M) {k j : ℕ} (hjk : j ≤ k)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    u_h ∈ laplacianDomainPow (I := I) (M := M) g j := by
  classical
  obtain ⟨d, hd⟩ : ∃ d : ℕ, k = j + d := Nat.exists_eq_add_of_le hjk
  subst hd
  clear hjk
  induction d with
  | zero =>
      simpa using hu_h
  | succ d ih =>
      have h_succ_eq : j + (d + 1) = (j + d) + 1 := by ring
      rw [h_succ_eq] at hu_h
      have hu_h_jd : u_h ∈ laplacianDomainPow (I := I) (M := M) g (j + d) := by
        rw [DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_mem_iff] at hu_h
        obtain ⟨f, hf⟩ := hu_h
        by_cases h_jd_zero : j + d = 0
        · rw [h_jd_zero]
          rw [DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_zero]
          exact Submodule.mem_top
        · obtain ⟨n, hn⟩ : ∃ n : ℕ, j + d = n + 1 :=
            Nat.exists_eq_succ_of_ne_zero h_jd_zero
          rw [hn] at hf ⊢
          rw [DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_succ_apply] at hf
          rw [DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_mem_iff]
          refine ⟨DifferentialGeometry.Analysis.Laplacian.resolventL2
            (I := I) (M := M) g f, ?_⟩
          rw [hf]
          congr 1
          have h1 : DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2
              (I := I) (M := M) g n
              (DifferentialGeometry.Analysis.Laplacian.resolventL2
                (I := I) (M := M) g f) =
            DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2
              (I := I) (M := M) g (n + 1) f := by
            rw [DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_add]
            rfl
          have h2 : DifferentialGeometry.Analysis.Laplacian.resolventL2
              (I := I) (M := M) g
              (DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2
                (I := I) (M := M) g n f) =
            DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2
              (I := I) (M := M) g (n + 1) f := by
            rw [DifferentialGeometry.Analysis.Laplacian.iteratedResolventL2_succ_apply]
          rw [h1, h2]
      exact ih hu_h_jd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.laplacianDomainPow_le_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.laplacianDomainPow_le_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.laplacianDomainPow_le_of_le ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.laplacianDomainPow_le_of_le

theorem chartPushed_memWkp_two_k_of_laplacianDomainPow_le_two
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
        (I := I) (M := M) α) :=
  chartPushed_memWkp_of_laplacianDomainPow_le_two
    (I := I) (M := M) g α hk hu_h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.chartPushed_memWkp_two_k_of_laplacianDomainPow_le_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.chartPushed_memWkp_two_k_of_laplacianDomainPow_le_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.chartPushed_memWkp_two_k_of_laplacianDomainPow_le_two ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.chartPushed_memWkp_two_k_of_laplacianDomainPow_le_two

theorem memWkpChart_two_k_of_laplacianDomainPow_le_two
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk : k ≤ 2)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  memWkpChart_of_laplacianDomainPow_le_two
    (I := I) (M := M) g hk hu_h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.memWkpChart_two_k_of_laplacianDomainPow_le_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.memWkpChart_two_k_of_laplacianDomainPow_le_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.memWkpChart_two_k_of_laplacianDomainPow_le_two ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.memWkpChart_two_k_of_laplacianDomainPow_le_two

theorem chartPushed_memWkp_two_k_of_laplacianDomainPow_min_two
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
  have hu_h_min : u_h ∈ laplacianDomainPow (I := I) (M := M) g (_root_.Min.min k 2) :=
    laplacianDomainPow_le_of_le (I := I) (M := M) g (min_le_left _ _) hu_h
  have h_min_le_2 : _root_.Min.min k 2 ≤ 2 := min_le_right _ _
  exact chartPushed_memWkp_two_k_of_laplacianDomainPow_le_two
    (I := I) (M := M) g α h_min_le_2 hu_h_min

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.chartPushed_memWkp_two_k_of_laplacianDomainPow_min_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.chartPushed_memWkp_two_k_of_laplacianDomainPow_min_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.chartPushed_memWkp_two_k_of_laplacianDomainPow_min_two ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.chartPushed_memWkp_two_k_of_laplacianDomainPow_min_two

theorem chartSideH2kBridge_of_laplacianDomainPow_min_two
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    ChartSideH2kBridge (I := I) (M := M) (_root_.Min.min k 2)
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  classical
  have hu_h_min : u_h ∈ laplacianDomainPow (I := I) (M := M) g (_root_.Min.min k 2) :=
    laplacianDomainPow_le_of_le (I := I) (M := M) g (min_le_left _ _) hu_h
  have h_min_le_2 : _root_.Min.min k 2 ≤ 2 := min_le_right _ _
  exact IteratedChartHmBootstrapPolymorphic.chartSideH2kBridge_of_laplacianDomainPow_le_two
    (I := I) (M := M) g h_min_le_2 hu_h_min

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.chartSideH2kBridge_of_laplacianDomainPow_min_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.chartSideH2kBridge_of_laplacianDomainPow_min_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.chartSideH2kBridge_of_laplacianDomainPow_min_two ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.chartSideH2kBridge_of_laplacianDomainPow_min_two

theorem memWkpChart_two_k_of_laplacianDomainPow_min_two
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) (2 * _root_.Min.min k 2) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  classical
  have hu_h_min : u_h ∈ laplacianDomainPow (I := I) (M := M) g (_root_.Min.min k 2) :=
    laplacianDomainPow_le_of_le (I := I) (M := M) g (min_le_left _ _) hu_h
  have h_min_le_2 : _root_.Min.min k 2 ≤ 2 := min_le_right _ _
  exact memWkpChart_two_k_of_laplacianDomainPow_le_two
    (I := I) (M := M) g h_min_le_2 hu_h_min

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.memWkpChart_two_k_of_laplacianDomainPow_min_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.memWkpChart_two_k_of_laplacianDomainPow_min_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.memWkpChart_two_k_of_laplacianDomainPow_min_two ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.memWkpChart_two_k_of_laplacianDomainPow_min_two

theorem laplacianDomainPow_memWkpChart_two_k
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) (2 * _root_.Min.min k 2) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) (2 * _root_.Min.min k 2) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  classical
  have h_mem := memWkpChart_two_k_of_laplacianDomainPow_min_two
    (I := I) (M := M) g k hu_h
  refine ⟨h_mem, ?_⟩
  exact DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_lt_top_of_memWkpChart
    (I := I) (M := M) (k := 2 * _root_.Min.min k 2) (p := 2) (by norm_num) h_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.laplacianDomainPow_memWkpChart_two_k then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.laplacianDomainPow_memWkpChart_two_k"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.laplacianDomainPow_memWkpChart_two_k ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.laplacianDomainPow_memWkpChart_two_k

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushed_memWkp_two_k_of_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
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
  chartPushed_memWkp_of_laplacianDomainPow
    (I := I) (M := M) g α k h_bridge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.chartPushed_memWkp_two_k_of_laplacianDomainPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.chartPushed_memWkp_two_k_of_laplacianDomainPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.chartPushed_memWkp_two_k_of_laplacianDomainPow ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.chartPushed_memWkp_two_k_of_laplacianDomainPow

omit [NeZero (Module.finrank ℝ E)] in
theorem memWkpChart_two_k_of_laplacianDomainPow
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
  let _ := hu_h
  exact memWkpChart_2k_of_chartSideH2kBridge_polymorphic
    (I := I) (M := M) g k h_bridge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.memWkpChart_two_k_of_laplacianDomainPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.memWkpChart_two_k_of_laplacianDomainPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.memWkpChart_two_k_of_laplacianDomainPow ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical.memWkpChart_two_k_of_laplacianDomainPow

end IteratedChartHmBootstrapCanonical
end Laplacian
end Analysis
end DifferentialGeometry

end
