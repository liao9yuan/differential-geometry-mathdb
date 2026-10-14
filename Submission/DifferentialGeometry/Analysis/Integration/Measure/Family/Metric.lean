import Submission.DifferentialGeometry.Geometry.Metric.Family.Basic
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.Integral.Measure

noncomputable section

open _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

abbrev metricForMeasure (g : SmoothRiemannianMetric I M) :
    SmoothRiemannianMetric I M :=
  g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.metricForMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.metricForMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.metricForMeasure ``Submission.DifferentialGeometry.Integral.Measure.metricForMeasure

omit [FiniteDimensional ℝ E] in
@[simp]
theorem metricForMeasure_inner (g : SmoothRiemannianMetric I M) (x : M) :
    (metricForMeasure (I := I) (M := M) g).inner x = g.inner x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.metricForMeasure_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.metricForMeasure_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.metricForMeasure_inner ``Submission.DifferentialGeometry.Integral.Measure.metricForMeasure_inner


abbrev volumeMeasureAt [T2Space M] [SigmaCompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Time)
      (t : Time) :
    MeasureTheory.Measure M :=
  riemannianVolumeMeasure (I := I) (M := M) (G.metric t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volumeMeasureAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volumeMeasureAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volumeMeasureAt ``Submission.DifferentialGeometry.Integral.Measure.volumeMeasureAt

@[simp]
theorem volumeMeasureAt_eq [T2Space M] [SigmaCompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Time)
      (t : Time) :
    volumeMeasureAt (I := I) (M := M) G t =
      riemannianVolumeMeasure (I := I) (M := M) (G.metric t) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volumeMeasureAt_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volumeMeasureAt_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volumeMeasureAt_eq ``Submission.DifferentialGeometry.Integral.Measure.volumeMeasureAt_eq


abbrev volumeMeasureOn [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D) :
  MeasureTheory.Measure M :=
  riemannianVolumeMeasure (I := I) (M := M) (G.metricAt t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volumeMeasureOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volumeMeasureOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volumeMeasureOn ``Submission.DifferentialGeometry.Integral.Measure.volumeMeasureOn

@[simp]
theorem volumeMeasureOn_eq [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D) :
    volumeMeasureOn (I := I) (M := M) G t =
      riemannianVolumeMeasure (I := I) (M := M) (G.metricAt t) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volumeMeasureOn_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volumeMeasureOn_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volumeMeasureOn_eq ``Submission.DifferentialGeometry.Integral.Measure.volumeMeasureOn_eq

@[simp]
theorem volumeMeasureOn_eq_metric [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D) :
    volumeMeasureOn (I := I) (M := M) G t =
      riemannianVolumeMeasure (I := I) (M := M) (G.metric (t : Real)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volumeMeasureOn_eq_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volumeMeasureOn_eq_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volumeMeasureOn_eq_metric ``Submission.DifferentialGeometry.Integral.Measure.volumeMeasureOn_eq_metric

theorem volumeMeasureAt_isLocallyFiniteMeasure [T2Space M] [SigmaCompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Time)
      (t : Time) :
    IsLocallyFiniteMeasure (volumeMeasureAt (I := I) (M := M) G t) := by
  exact riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M)
    (G.metric t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volumeMeasureAt_isLocallyFiniteMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volumeMeasureAt_isLocallyFiniteMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volumeMeasureAt_isLocallyFiniteMeasure ``Submission.DifferentialGeometry.Integral.Measure.volumeMeasureAt_isLocallyFiniteMeasure

theorem volumeMeasureAt_sigmaFinite [T2Space M] [SigmaCompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Time)
      (t : Time) :
    SigmaFinite (volumeMeasureAt (I := I) (M := M) G t) := by
  exact riemannianVolumeMeasure_sigmaFinite (I := I) (M := M)
    (G.metric t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volumeMeasureAt_sigmaFinite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volumeMeasureAt_sigmaFinite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volumeMeasureAt_sigmaFinite ``Submission.DifferentialGeometry.Integral.Measure.volumeMeasureAt_sigmaFinite

theorem volumeMeasureAt_isFiniteMeasure_of_compactSpace
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Time)
      (t : Time) :
    IsFiniteMeasure (volumeMeasureAt (I := I) (M := M) G t) := by
  exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
    (I := I) (M := M) (G.metric t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volumeMeasureAt_isFiniteMeasure_of_compactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volumeMeasureAt_isFiniteMeasure_of_compactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volumeMeasureAt_isFiniteMeasure_of_compactSpace ``Submission.DifferentialGeometry.Integral.Measure.volumeMeasureAt_isFiniteMeasure_of_compactSpace

theorem volumeMeasureOn_isLocallyFiniteMeasure [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D) :
    IsLocallyFiniteMeasure (volumeMeasureOn (I := I) (M := M) G t) := by
  exact riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) (M := M)
    (G.metricAt t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volumeMeasureOn_isLocallyFiniteMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volumeMeasureOn_isLocallyFiniteMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volumeMeasureOn_isLocallyFiniteMeasure ``Submission.DifferentialGeometry.Integral.Measure.volumeMeasureOn_isLocallyFiniteMeasure

theorem volumeMeasureOn_sigmaFinite [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D) :
    SigmaFinite (volumeMeasureOn (I := I) (M := M) G t) := by
  exact riemannianVolumeMeasure_sigmaFinite (I := I) (M := M)
    (G.metricAt t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volumeMeasureOn_sigmaFinite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volumeMeasureOn_sigmaFinite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volumeMeasureOn_sigmaFinite ``Submission.DifferentialGeometry.Integral.Measure.volumeMeasureOn_sigmaFinite

theorem volumeMeasureOn_isFiniteMeasure_of_compactSpace
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D) :
    IsFiniteMeasure (volumeMeasureOn (I := I) (M := M) G t) := by
  exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
    (I := I) (M := M) (G.metricAt t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.volumeMeasureOn_isFiniteMeasure_of_compactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.volumeMeasureOn_isFiniteMeasure_of_compactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.volumeMeasureOn_isFiniteMeasure_of_compactSpace ``Submission.DifferentialGeometry.Integral.Measure.volumeMeasureOn_isFiniteMeasure_of_compactSpace

end

end DifferentialGeometry.Integral.Measure
