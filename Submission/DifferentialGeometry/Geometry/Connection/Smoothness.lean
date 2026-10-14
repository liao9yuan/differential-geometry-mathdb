import Submission.DifferentialGeometry.Geometry.Metric.Family.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Connection

open _root_.Bundle _root_.Submission.Bundle
open _root_.CovariantDerivative _root_.Submission.CovariantDerivative
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

section Smoothness

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

def ConnectionFamilySmooth
    (G : MetricConnectionFamily (I := I) (M := M) Time) : Prop :=
  forall t : Time, _root_.CovariantDerivative.ContMDiffCovariantDerivative (G.connection t) ∞

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.ConnectionFamilySmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.ConnectionFamilySmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.ConnectionFamilySmooth ``Submission.DifferentialGeometry.Geometry.Connection.ConnectionFamilySmooth


theorem connection_smooth_at_of_connectionFamilySmooth
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (hG : ConnectionFamilySmooth G) (t : Time) :
    ContMDiffCovariantDerivative (G.connection t) ∞ :=
  hG t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connection_smooth_at_of_connectionFamilySmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connection_smooth_at_of_connectionFamilySmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connection_smooth_at_of_connectionFamilySmooth ``Submission.DifferentialGeometry.Geometry.Connection.connection_smooth_at_of_connectionFamilySmooth


def ConnectionFamilySmoothOn
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D) : Prop :=
  forall t : RealTimeInterval.FlowTime D, _root_.CovariantDerivative.ContMDiffCovariantDerivative (G.connectionAt t) ∞

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.ConnectionFamilySmoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.ConnectionFamilySmoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.ConnectionFamilySmoothOn ``Submission.DifferentialGeometry.Geometry.Connection.ConnectionFamilySmoothOn


theorem connection_smooth_at_of_connectionFamilySmoothOn
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (hG : ConnectionFamilySmoothOn (I := I) (M := M) G)
    (t : RealTimeInterval.FlowTime D) :
    ContMDiffCovariantDerivative (G.connectionAt t) ∞ :=
  hG t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.connection_smooth_at_of_connectionFamilySmoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.connection_smooth_at_of_connectionFamilySmoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.connection_smooth_at_of_connectionFamilySmoothOn ``Submission.DifferentialGeometry.Geometry.Connection.connection_smooth_at_of_connectionFamilySmoothOn

end Smoothness

end DifferentialGeometry.Geometry.Connection
