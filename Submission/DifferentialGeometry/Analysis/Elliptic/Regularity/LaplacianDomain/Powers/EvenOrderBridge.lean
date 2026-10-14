import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2Regularity

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
namespace LaplacianDomainPowH2kBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

def ChartSideH2kBridge (k : ℕ) (u : M → ℝ) : Prop :=
  ∀ α : M,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α u)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.ChartSideH2kBridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.ChartSideH2kBridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.ChartSideH2kBridge ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.ChartSideH2kBridge

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem memWkpChart_2k_of_chartSideH2kBridge
    (k : ℕ) {u : M → ℝ}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) k u) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) (2 * k) 2 u := by
  intro α
  exact h_bridge α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.memWkpChart_2k_of_chartSideH2kBridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.memWkpChart_2k_of_chartSideH2kBridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.memWkpChart_2k_of_chartSideH2kBridge ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.memWkpChart_2k_of_chartSideH2kBridge

omit [NeZero (Module.finrank ℝ E)] in
theorem wkpNormChart_2k_lt_top_of_chartSideH2kBridge
    (k : ℕ) {u : M → ℝ}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) k u) :
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) (2 * k) 2 u < ⊤ :=
  DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_lt_top_of_memWkpChart
    (I := I) (M := M) (k := 2 * k) (p := 2) (by norm_num)
    (memWkpChart_2k_of_chartSideH2kBridge (I := I) (M := M) k h_bridge)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.wkpNormChart_2k_lt_top_of_chartSideH2kBridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.wkpNormChart_2k_lt_top_of_chartSideH2kBridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.wkpNormChart_2k_lt_top_of_chartSideH2kBridge ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.wkpNormChart_2k_lt_top_of_chartSideH2kBridge

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  refine ⟨?_, ?_⟩
  · exact memWkpChart_2k_of_chartSideH2kBridge (I := I) (M := M) k h_bridge
  · exact wkpNormChart_2k_lt_top_of_chartSideH2kBridge (I := I) (M := M) k h_bridge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    ∃ u : M → ℝ,
      u = ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) (2 * k) 2 u ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) (2 * k) 2 u < ⊤ := by
  refine ⟨((H1ComplToLp (I := I) (M := M) g u_h :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ), rfl, ?_, ?_⟩
  · exact (laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge (I := I) (M := M) g k h_bridge).1
  · exact (laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge (I := I) (M := M) g k h_bridge).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.exists_laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.exists_laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.exists_laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.exists_laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainPow_memWkpChart_2k_two_sided_of_chartSideBridges
    (g : SmoothRiemannianMetric I M) (k : ℕ)
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
    (DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) (2 * (k + 1)) 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) (2 * (k + 1)) 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤) ∧
    (DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) (2 * (k + 1)) 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g k hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
        (I := I) (M := M) (2 * (k + 1)) 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g k hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤) := by
  refine ⟨laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
    (I := I) (M := M) g (k + 1) h_bridge_u, ?_⟩
  refine ⟨memWkpChart_2k_of_chartSideH2kBridge (I := I) (M := M) (k + 1)
    h_bridge_rhs, ?_⟩
  exact wkpNormChart_2k_lt_top_of_chartSideH2kBridge (I := I) (M := M) (k + 1) h_bridge_rhs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_two_sided_of_chartSideBridges then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_two_sided_of_chartSideBridges"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_two_sided_of_chartSideBridges ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_two_sided_of_chartSideBridges

omit [NeZero (Module.finrank ℝ E)] in
theorem chartSideH2kBridge_zero
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl (I := I) (M := M) g) :
    ChartSideH2kBridge (I := I) (M := M) 0
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  intro α
  have h := iteratedH2Regularity_zero (I := I) (M := M) g u_h
  have h_eq : (2 : ℕ) * 0 = 0 := by norm_num
  rw [h_eq]
  exact h α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_zero ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_zero

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge_zero
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) 0 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) 0 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  have h_bridge := chartSideH2kBridge_zero (I := I) (M := M) g u_h
  have h_eq : (2 : ℕ) * 0 = 0 := by norm_num
  have := laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge
    (I := I) (M := M) g 0 h_bridge
  rw [h_eq] at this
  exact this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge_zero ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge_zero

theorem chartSideH2kBridge_one
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 1) :
    ChartSideH2kBridge (I := I) (M := M) 1
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  intro α
  have h := (iteratedH2Regularity_one (I := I) (M := M) g hu_h).1
  have h_eq : (2 : ℕ) * 1 = 2 := by norm_num
  rw [h_eq]
  exact h α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_one ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_one

theorem laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge_one
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
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ :=
  iteratedH2Regularity_one (I := I) (M := M) g hu_h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge_one ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge_one

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartSideH2kBridge_le_of_le
    {k j : ℕ} (hkj : j ≤ k) {u : M → ℝ}
    (h : ChartSideH2kBridge (I := I) (M := M) k u) :
    ChartSideH2kBridge (I := I) (M := M) j u := by
  intro α
  have h_le : 2 * j ≤ 2 * k := Nat.mul_le_mul_left 2 hkj
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le h_le (h α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_le_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_le_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_le_of_le ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_le_of_le

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chartSideH2kBridge_pred
    (k : ℕ) {u : M → ℝ}
    (h : ChartSideH2kBridge (I := I) (M := M) (k + 1) u) :
    ChartSideH2kBridge (I := I) (M := M) k u :=
  chartSideH2kBridge_le_of_le (I := I) (M := M) (Nat.le_succ k) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_pred then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_pred"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_pred ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_pred

omit [NeZero (Module.finrank ℝ E)] in
theorem chartSideH2kBridge_add
    (k : ℕ)
    {u v : M → ℝ}
    (hu : ChartSideH2kBridge (I := I) (M := M) k u)
    (hv : ChartSideH2kBridge (I := I) (M := M) k v) :
    ChartSideH2kBridge (I := I) (M := M) k (fun x => u x + v x) := by
  intro α
  rw [chartPushed_add]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.add
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) (hv α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_add ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_add

omit [NeZero (Module.finrank ℝ E)] in
theorem chartSideH2kBridge_const_smul
    (k : ℕ)
    (c : ℝ) {u : M → ℝ}
    (hu : ChartSideH2kBridge (I := I) (M := M) k u) :
    ChartSideH2kBridge (I := I) (M := M) k (fun x => c * u x) := by
  intro α
  rw [chartPushed_const_smul]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.const_smul
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_const_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_const_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_const_smul ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_const_smul

omit [NeZero (Module.finrank ℝ E)] in
theorem chartSideH2kBridge_neg
    (k : ℕ)
    {u : M → ℝ}
    (hu : ChartSideH2kBridge (I := I) (M := M) k u) :
    ChartSideH2kBridge (I := I) (M := M) k (fun x => -u x) := by
  have h := chartSideH2kBridge_const_smul (I := I) (M := M) k (-1) hu
  have hEq : (fun x : M => (-1 : ℝ) * u x) = (fun x : M => -u x) := by
    funext x; ring
  rw [hEq] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_neg ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_neg

omit [NeZero (Module.finrank ℝ E)] in
theorem chartSideH2kBridge_sub
    (k : ℕ)
    {u v : M → ℝ}
    (hu : ChartSideH2kBridge (I := I) (M := M) k u)
    (hv : ChartSideH2kBridge (I := I) (M := M) k v) :
    ChartSideH2kBridge (I := I) (M := M) k (fun x => u x - v x) := by
  have hneg := chartSideH2kBridge_neg (I := I) (M := M) k hv
  have h := chartSideH2kBridge_add (I := I) (M := M) k hu hneg
  have hEq : (fun x : M => u x + -v x) = (fun x : M => u x - v x) := by
    funext x; ring
  rw [hEq] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_sub ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.chartSideH2kBridge_sub

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem memWkpChart_2j_of_chartSideH2kBridge
    {k j : ℕ} (hkj : j ≤ k) {u : M → ℝ}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) k u) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) (2 * j) 2 u := by
  have h_full := memWkpChart_2k_of_chartSideH2kBridge (I := I) (M := M) k h_bridge
  exact DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart.le_of_le
    (Nat.mul_le_mul_left 2 hkj) h_full

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.memWkpChart_2j_of_chartSideH2kBridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.memWkpChart_2j_of_chartSideH2kBridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.memWkpChart_2j_of_chartSideH2kBridge ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.memWkpChart_2j_of_chartSideH2kBridge

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainPow_memWkpChart_2j_of_chartSideH2kBridge
    (g : SmoothRiemannianMetric I M)
    {k j : ℕ} (hkj : j ≤ k)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) (2 * j) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  memWkpChart_2j_of_chartSideH2kBridge (I := I) (M := M) hkj h_bridge

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2j_of_chartSideH2kBridge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2j_of_chartSideH2kBridge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2j_of_chartSideH2kBridge ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2j_of_chartSideH2kBridge

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainPow_memWkpChart_2k_unified
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (h_bridge : ChartSideH2kBridge (I := I) (M := M) k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  (laplacianDomainPow_memWkpChart_2k_of_chartSideH2kBridge (I := I) (M := M) g k h_bridge).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_unified then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_unified"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_unified ``Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge.laplacianDomainPow_memWkpChart_2k_unified

end LaplacianDomainPowH2kBridge
end Laplacian
end Analysis
end DifferentialGeometry

end
