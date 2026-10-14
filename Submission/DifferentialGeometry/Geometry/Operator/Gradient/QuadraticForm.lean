import Submission.DifferentialGeometry.Analysis.Normed.Matrix.CovectorBilinear
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.Manifold _root_.ContDiff _root_.Matrix.Norms.Elementwise

namespace DifferentialGeometry.Geometry.Operator

open _root_.Submission.DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.covectorNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.covectorNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.covectorNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.covectorNormedSpace target :: scope.openDecls } }

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.covectorDualNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.covectorDualNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.covectorDualNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.covectorDualNormedSpace target :: scope.openDecls } }

private local instance covectorBilinearNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.covectorBilinearNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.covectorBilinearNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorBilinearNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.covectorBilinearNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.covectorBilinearNormedSpace target :: scope.openDecls } }

def chartGradientBilin (g : SmoothRiemannianMetric I M) (alpha x : M) :
    (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  Matrix.covectorBilin (chartModelBasis E) (chartInvGramMatrix g alpha x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.chartGradientBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.chartGradientBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.chartGradientBilin ``Submission.DifferentialGeometry.Geometry.Operator.chartGradientBilin

theorem chartGradientBilin_apply (g : SmoothRiemannianMetric I M)
    (alpha x : M) (u v : E →L[ℝ] ℝ) :
    chartGradientBilin g alpha x u v =
      ∑ i, ∑ j, chartInvGramMatrix g alpha x i j *
        u (chartModelBasis E j) * v (chartModelBasis E i) :=
  Matrix.covectorBilin_apply _ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.chartGradientBilin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.chartGradientBilin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.chartGradientBilin_apply ``Submission.DifferentialGeometry.Geometry.Operator.chartGradientBilin_apply

theorem grad_norm_sq_eq_chartGradientBilin [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (alpha : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (chartAt H alpha).source) :
    g.inner x (gradFun g f x) (gradFun g f x) =
      chartGradientBilin g alpha x
        (fderiv ℝ (scalarOnE (I := I) alpha f) (extChartAt I alpha x))
        (fderiv ℝ (scalarOnE (I := I) alpha f) (extChartAt I alpha x)) := by
  rw [chartGradientBilin_apply, grad_norm_sq_chart g alpha hf hx]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.grad_norm_sq_eq_chartGradientBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.grad_norm_sq_eq_chartGradientBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.grad_norm_sq_eq_chartGradientBilin ``Submission.DifferentialGeometry.Geometry.Operator.grad_norm_sq_eq_chartGradientBilin

end DifferentialGeometry.Geometry.Operator
