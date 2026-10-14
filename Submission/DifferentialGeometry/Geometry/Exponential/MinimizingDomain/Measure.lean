import Submission.DifferentialGeometry.Geometry.Exponential.MinimizingDomain.Topology
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Polar.NullSets

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)]
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

variable [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

variable [MeasurableSpace E] [BorelSpace E]

theorem measure_minimizingDomain_sdiff_extendibleMinimizingDomain
    (g : SmoothRiemannianMetric I M) (p : M)
    (μ : _root_.MeasureTheory.Measure E) [μ.IsAddHaarMeasure] :
    μ (minimizingDomain (I := I) g p \
      extendibleMinimizingDomain (I := I) g p) = 0 := by
  apply _root_.MeasureTheory.measure_mono_null ?_
    ((isSigmaCompact_minimizingDomain (I := I) g p).measure_setOf_forall_smul_notMem μ)
  rintro v ⟨hv, hvnot⟩
  exact ⟨hv, fun c hc hcv => hvnot ⟨c, hc, hcv⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Exponential.measure_minimizingDomain_sdiff_extendibleMinimizingDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Exponential.measure_minimizingDomain_sdiff_extendibleMinimizingDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Exponential.measure_minimizingDomain_sdiff_extendibleMinimizingDomain ``Submission.DifferentialGeometry.Geometry.Riemannian.Exponential.measure_minimizingDomain_sdiff_extendibleMinimizingDomain

end DifferentialGeometry.Geometry.Riemannian.Exponential
