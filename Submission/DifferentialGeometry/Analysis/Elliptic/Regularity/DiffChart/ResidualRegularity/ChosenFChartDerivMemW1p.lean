import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.ChosenFirstPartialW1p
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.MemWkpThreeSmooth
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.FChartResidual.ResidualMemW1p
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev

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
namespace ChosenFChartDerivMemW1p

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.DiffChartChosenFirstPartial
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem chosenFChartDeriv_memW1p_of_base_memWkp22
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (direction : Fin (Module.finrank ℝ E))
    (h_base_f_chart_memWkp22 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).fChart
        (chartTargetEuclid (I := I) (M := M) α)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chosenFChartDeriv (I := I) (M := M) g α hu_h direction)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold chosenFChartDeriv
  have h_step := h_base_f_chart_memWkp22.chosenWeakPartial_mem direction
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    at h_step
  exact h_step

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.chosenFChartDeriv_memW1p_of_base_memWkp22 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.chosenFChartDeriv_memW1p_of_base_memWkp22"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.chosenFChartDeriv_memW1p_of_base_memWkp22 ``Submission.DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.chosenFChartDeriv_memW1p_of_base_memWkp22

omit [SigmaCompactSpace M] in
theorem chosenFChartDeriv_memW1p
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ : Fin (Module.finrank ℝ E))
    (h_base_f_chart_memWkp22 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).fChart
        (chartTargetEuclid (I := I) (M := M) α)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
      (chartTargetEuclid (I := I) (M := M) α) :=
  chosenFChartDeriv_memW1p_of_base_memWkp22 (I := I) (M := M) g α hu_h l₁
    h_base_f_chart_memWkp22

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.chosenFChartDeriv_memW1p then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.chosenFChartDeriv_memW1p"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.chosenFChartDeriv_memW1p ``Submission.DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.chosenFChartDeriv_memW1p

omit [SigmaCompactSpace M] in
theorem chosenFChartDeriv_memW1p_of_base_f_chart_memWkp22
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ : Fin (Module.finrank ℝ E))
    (h_base_f_chart_memWkp22 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).fChart
        (chartTargetEuclid (I := I) (M := M) α)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
      (chartTargetEuclid (I := I) (M := M) α) :=
  chosenFChartDeriv_memW1p (I := I) (M := M) g α hu_h l₁
    h_base_f_chart_memWkp22

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.chosenFChartDeriv_memW1p_of_base_f_chart_memWkp22 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.chosenFChartDeriv_memW1p_of_base_f_chart_memWkp22"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.chosenFChartDeriv_memW1p_of_base_f_chart_memWkp22 ``Submission.DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p.chosenFChartDeriv_memW1p_of_base_f_chart_memWkp22

end ChosenFChartDerivMemW1p
end Laplacian
end Analysis
end DifferentialGeometry

end
