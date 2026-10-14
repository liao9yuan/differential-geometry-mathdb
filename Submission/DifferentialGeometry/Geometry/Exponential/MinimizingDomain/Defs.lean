import Submission.DifferentialGeometry.Geometry.Exponential.Defs
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

private local instance tangentSpaceNormedAddCommGroup
    (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TangentSpace I y) x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.tangentSpaceNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Exponential.tangentSpaceNormedAddCommGroup target :: scope.openDecls } }

private local instance tangentSpaceInnerProductSpace
    (x : M) : InnerProductSpace ℝ (TangentSpace I x) :=
  Bundle.instInnerProductSpaceReal (E := fun y : M => TangentSpace I y) x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.tangentSpaceInnerProductSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Exponential.tangentSpaceInnerProductSpace target :: scope.openDecls } }

private local instance tangentSpaceNormedSpace
    (x : M) : NormedSpace ℝ (TangentSpace I x) := inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.tangentSpaceNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.Exponential.tangentSpaceNormedSpace target :: scope.openDecls } }

def minimizingDomain (g : SmoothRiemannianMetric I M) (p : M) : Set E :=
  {v | ENNReal.ofReal (Real.sqrt
      (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v))) =
    _root_.Manifold.riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from v))}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.minimizingDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.minimizingDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.minimizingDomain ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.minimizingDomain

def extendibleMinimizingDomain (g : SmoothRiemannianMetric I M) (p : M) : Set E :=
  {v | ∃ c : ℝ, 1 < c ∧ c • v ∈ minimizingDomain (I := I) g p}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.extendibleMinimizingDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.extendibleMinimizingDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.extendibleMinimizingDomain ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.extendibleMinimizingDomain

end DifferentialGeometry.Geometry.Riemannian.Exponential
