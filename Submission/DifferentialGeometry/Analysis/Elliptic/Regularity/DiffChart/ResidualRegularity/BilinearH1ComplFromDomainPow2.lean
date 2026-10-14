import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.CLM.Leibniz
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Chart.LocalRegularity
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Multiplication.H1Completion
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.SmoothMul

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
namespace DiffChartBilinearH1Compl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalIdentityIntegralForm
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

theorem memWkpChart_two_two_smooth_mul_laplacianDomain
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) 2 2
      (fun x : M => (φ : M → ℝ) x *
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x) := by
  have h_uh := (laplacianDomain_memWkpChart_two
    (I := I) (M := M) g hu_h).1
  exact DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart_smooth_mul
    (I := I) (M := M) (by norm_num : (1 : ℝ≥0∞) ≤ 2) φ h_uh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.memWkpChart_two_two_smooth_mul_laplacianDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.memWkpChart_two_two_smooth_mul_laplacianDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.memWkpChart_two_two_smooth_mul_laplacianDomain ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.memWkpChart_two_two_smooth_mul_laplacianDomain

theorem memWkpChart_two_two_smoothMulLp_laplacianDomain_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) 2 2
      ((smoothMulLp (I := I) (M := M) g φ
        (H1ComplToLp (I := I) (M := M) g u_h) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  classical
  have h_phase3 := smoothMulH1Compl_mem_laplacianDomain
    (I := I) (M := M) g φ hu_h
  have h_cstep := (laplacianDomain_memWkpChart_two
    (I := I) (M := M) g h_phase3).1
  have h_phase2 := H1ComplToLp_smoothMulH1Compl (I := I) (M := M) g φ u_h
  rw [h_phase2] at h_cstep
  exact h_cstep

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.memWkpChart_two_two_smoothMulLp_laplacianDomain_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.memWkpChart_two_two_smoothMulLp_laplacianDomain_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.memWkpChart_two_two_smoothMulLp_laplacianDomain_coeFn ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.memWkpChart_two_two_smoothMulLp_laplacianDomain_coeFn

theorem memWkpChart_two_two_smoothMulLp_preimage_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) 2 2
      ((smoothMulLp (I := I) (M := M) g φ
        (laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  classical
  obtain ⟨w_h, hw_h_dom, hw_h_eq⟩ :=
    laplacianDomainPow_two_preimage_eq (I := I) (M := M) g hu_h
  have h_phase3 := smoothMulH1Compl_mem_laplacianDomain
    (I := I) (M := M) g φ hw_h_dom
  have h_cstep := (laplacianDomain_memWkpChart_two
    (I := I) (M := M) g h_phase3).1
  have h_phase2 := H1ComplToLp_smoothMulH1Compl (I := I) (M := M) g φ w_h
  rw [h_phase2, hw_h_eq] at h_cstep
  exact h_cstep

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.memWkpChart_two_two_smoothMulLp_preimage_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.memWkpChart_two_two_smoothMulLp_preimage_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.memWkpChart_two_two_smoothMulLp_preimage_coeFn ``Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.memWkpChart_two_two_smoothMulLp_preimage_coeFn

end DiffChartBilinearH1Compl
end Laplacian
end Analysis
end DifferentialGeometry

end
