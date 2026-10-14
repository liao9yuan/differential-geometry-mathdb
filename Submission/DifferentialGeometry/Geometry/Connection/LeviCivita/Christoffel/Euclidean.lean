import Submission.DifferentialGeometry.Geometry.Geodesic.Equation.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Euclidean

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold

namespace DifferentialGeometry.Geometry.Connection

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private theorem chartGramOnE_euclideanMetric (x : V) (i j : Fin (Module.finrank ℝ V)) :
    chartGramOnE (euclideanMetric (E := V)) x i j =
      fun _ => _root_.Inner.inner ℝ ((chartModelBasis V) i) ((chartModelBasis V) j) := by
  funext y
  rw [chartGramOnE_def, chartGramMatrix_apply, euclideanMetric_inner]
  simp only [chartBasisVecFiber, TangentBundle.symmL_model_space]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.chartGramOnE_euclideanMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.chartGramOnE_euclideanMetric target :: scope.openDecls } }

theorem chartChristoffel_euclideanMetric (x : V) (i j k : Fin (Module.finrank ℝ V)) :
    chartChristoffel (euclideanMetric (E := V)) x i j k = 0 := by
  funext y
  rw [chartChristoffel_def]
  simp_rw [chartGramOnE_euclideanMetric]
  simp [partialDeriv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartChristoffel_euclideanMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartChristoffel_euclideanMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartChristoffel_euclideanMetric ``Submission.DifferentialGeometry.Geometry.Connection.chartChristoffel_euclideanMetric

theorem chartChristoffelContraction_euclideanMetric (x u v y : V) :
    chartChristoffelContraction (euclideanMetric (E := V)) x u v y = 0 := by
  rw [chartChristoffelContraction_def]
  simp_rw [chartChristoffel_euclideanMetric]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartChristoffelContraction_euclideanMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartChristoffelContraction_euclideanMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartChristoffelContraction_euclideanMetric ``Submission.DifferentialGeometry.Geometry.Connection.chartChristoffelContraction_euclideanMetric

end DifferentialGeometry.Geometry.Connection
