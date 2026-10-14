import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.Chart.Invariance
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function _root_.FiberBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianChartAlphaMatrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartInvariance

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem chartAlphaMatrixIdentity_holds_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    chartAlphaMatrixIdentity (I := I) (M := M) g α f x := by
  classical
  intro i j
  exact chartAlphaMatrixIdentity_holds (I := I) g α hf hx i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.chartAlphaMatrixIdentity_holds_chartSource then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.chartAlphaMatrixIdentity_holds_chartSource"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.chartAlphaMatrixIdentity_holds_chartSource ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.chartAlphaMatrixIdentity_holds_chartSource

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem chartHessian_contraction_comm
    (g : SmoothRiemannianMetric I M) (α : M)
    (f f' : M → ℝ) (x : M) :
    ∑ i : Fin (Module.finrank ℝ E), ∑ j, ∑ k, ∑ l,
      2 * (chartInvGramMatrix (I := I) g α x i k *
        chartInvGramMatrix (I := I) g α x j l *
        chartHessianTensor (I := I) g α f' i j x *
        chartHessianTensor (I := I) g α f k l x) =
    ∑ i : Fin (Module.finrank ℝ E), ∑ j, ∑ k, ∑ l,
      2 * (chartInvGramMatrix (I := I) g α x i k *
        chartInvGramMatrix (I := I) g α x j l *
        chartHessianTensor (I := I) g α f i j x *
        chartHessianTensor (I := I) g α f' k l x) := by
  classical
  set n := Module.finrank ℝ E
  set G : Fin n → Fin n → ℝ :=
    fun i k => chartInvGramMatrix (I := I) g α x i k with hG_def
  set Hf : Fin n → Fin n → ℝ :=
    fun i j => chartHessianTensor (I := I) g α f i j x with hHf_def
  set Hf' : Fin n → Fin n → ℝ :=
    fun i j => chartHessianTensor (I := I) g α f' i j x with hHf'_def
  have h_Gsymm : ∀ i k : Fin n, G i k = G k i := by
    intro i k
    change chartInvGramMatrix (I := I) g α x i k = chartInvGramMatrix (I := I) g α x k i
    have hHerm : (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α x).IsHermitian :=
      DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_isHermitian (I := I) g α x
    have hHermInv : (chartInvGramMatrix (I := I) g α x).IsHermitian := by
      unfold chartInvGramMatrix
      exact hHerm.inv
    have h_apply := hHermInv.apply i k
    rw [_root_.TrivialStar.star_trivial] at h_apply
    exact h_apply.symm
  have h_LHS_abbr :
      (∑ i : Fin n, ∑ j, ∑ k, ∑ l,
        2 * (chartInvGramMatrix (I := I) g α x i k *
          chartInvGramMatrix (I := I) g α x j l *
          chartHessianTensor (I := I) g α f' i j x *
          chartHessianTensor (I := I) g α f k l x)) =
      ∑ i : Fin n, ∑ j, ∑ k, ∑ l,
        2 * (G i k * G j l * Hf' i j * Hf k l) := rfl
  have h_RHS_abbr :
      (∑ i : Fin n, ∑ j, ∑ k, ∑ l,
        2 * (chartInvGramMatrix (I := I) g α x i k *
          chartInvGramMatrix (I := I) g α x j l *
          chartHessianTensor (I := I) g α f i j x *
          chartHessianTensor (I := I) g α f' k l x)) =
      ∑ i : Fin n, ∑ j, ∑ k, ∑ l,
        2 * (G i k * G j l * Hf i j * Hf' k l) := rfl
  rw [h_LHS_abbr, h_RHS_abbr]
  have h_LHS_reorder1 :
      (∑ i : Fin n, ∑ j, ∑ k, ∑ l,
        2 * (G i k * G j l * Hf' i j * Hf k l)) =
      (∑ i : Fin n, ∑ j, ∑ l, ∑ k,
        2 * (G i k * G j l * Hf' i j * Hf k l)) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.sum_comm]
  have h_LHS_reorder2 :
      (∑ i : Fin n, ∑ j, ∑ l, ∑ k,
        2 * (G i k * G j l * Hf' i j * Hf k l)) =
      (∑ i : Fin n, ∑ l, ∑ j, ∑ k,
        2 * (G i k * G j l * Hf' i j * Hf k l)) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_comm]
  have h_LHS_reorder3 :
      (∑ i : Fin n, ∑ l, ∑ j, ∑ k,
        2 * (G i k * G j l * Hf' i j * Hf k l)) =
      (∑ l : Fin n, ∑ i, ∑ j, ∑ k,
        2 * (G i k * G j l * Hf' i j * Hf k l)) := by
    rw [Finset.sum_comm]
  have h_LHS_reorder4 :
      (∑ l : Fin n, ∑ i, ∑ j, ∑ k,
        2 * (G i k * G j l * Hf' i j * Hf k l)) =
      (∑ l : Fin n, ∑ i, ∑ k, ∑ j,
        2 * (G i k * G j l * Hf' i j * Hf k l)) := by
    refine Finset.sum_congr rfl ?_
    intro l _
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_comm]
  have h_LHS_reorder5 :
      (∑ l : Fin n, ∑ i, ∑ k, ∑ j,
        2 * (G i k * G j l * Hf' i j * Hf k l)) =
      (∑ l : Fin n, ∑ k, ∑ i, ∑ j,
        2 * (G i k * G j l * Hf' i j * Hf k l)) := by
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [Finset.sum_comm]
  have h_LHS_reorder6 :
      (∑ l : Fin n, ∑ k, ∑ i, ∑ j,
        2 * (G i k * G j l * Hf' i j * Hf k l)) =
      (∑ k : Fin n, ∑ l, ∑ i, ∑ j,
        2 * (G i k * G j l * Hf' i j * Hf k l)) := by
    rw [Finset.sum_comm]
  rw [h_LHS_reorder1, h_LHS_reorder2, h_LHS_reorder3, h_LHS_reorder4, h_LHS_reorder5,
    h_LHS_reorder6]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [h_Gsymm k i, h_Gsymm l j]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.chartHessian_contraction_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.chartHessian_contraction_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.chartHessian_contraction_comm ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix.chartHessian_contraction_comm

end HessianChartAlphaMatrix
end Laplacian
end Analysis
end DifferentialGeometry

end
