import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Defs
import Submission.DifferentialGeometry.Geometry.Metric.Family.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Connection

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Pointwise

variable [FiniteDimensional Real E] [CompleteSpace E]
variable [SigmaCompactSpace M] [T2Space M]

def IsTorsionFreeAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _)) (x : M) : Prop :=
  cov.torsion x = 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsTorsionFreeAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsTorsionFreeAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsTorsionFreeAt ``Submission.DifferentialGeometry.Geometry.Connection.IsTorsionFreeAt


def IsLeviCivitaAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) (x : M) : Prop :=
  IsMetricCompatibleOn cov.toFun g {x} /\ IsTorsionFreeAt (I := I) cov x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsLeviCivitaAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsLeviCivitaAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsLeviCivitaAt ``Submission.DifferentialGeometry.Geometry.Connection.IsLeviCivitaAt

def IsTorsionFree
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _)) : Prop :=
  forall x : M, IsTorsionFreeAt (I := I) cov x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsTorsionFree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsTorsionFree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsTorsionFree ``Submission.DifferentialGeometry.Geometry.Connection.IsTorsionFree


def IsLeviCivita
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) : Prop :=
  IsMetricCompatible (I := I) cov g /\ IsTorsionFree (I := I) cov

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsLeviCivita then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsLeviCivita"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsLeviCivita ``Submission.DifferentialGeometry.Geometry.Connection.IsLeviCivita

omit [SigmaCompactSpace M] [T2Space M] in
theorem metricCompatible_of_isLeviCivita
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (h : IsLeviCivita (I := I) cov g) :
    IsMetricCompatible (I := I) cov g :=
  h.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.metricCompatible_of_isLeviCivita then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.metricCompatible_of_isLeviCivita"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.metricCompatible_of_isLeviCivita ``Submission.DifferentialGeometry.Geometry.Connection.metricCompatible_of_isLeviCivita

omit [SigmaCompactSpace M] [T2Space M] in
theorem torsionFree_of_isLeviCivita
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (h : IsLeviCivita (I := I) cov g) :
    IsTorsionFree (I := I) cov :=
  h.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.torsionFree_of_isLeviCivita then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.torsionFree_of_isLeviCivita"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.torsionFree_of_isLeviCivita ``Submission.DifferentialGeometry.Geometry.Connection.torsionFree_of_isLeviCivita

omit [SigmaCompactSpace M] [T2Space M] in
theorem isLeviCivita_of_parts
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (hmc : IsMetricCompatible (I := I) cov g)
    (htf : IsTorsionFree (I := I) cov) :
    IsLeviCivita (I := I) cov g :=
  ⟨hmc, htf⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.isLeviCivita_of_parts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.isLeviCivita_of_parts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.isLeviCivita_of_parts ``Submission.DifferentialGeometry.Geometry.Connection.isLeviCivita_of_parts

end Pointwise

section Family

variable [FiniteDimensional Real E] [CompleteSpace E]
variable [SigmaCompactSpace M] [T2Space M]


def IsTorsionFreeFamilyOn
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D) : Prop :=
  forall t : RealTimeInterval.FlowTime D,
    IsTorsionFree (I := I) (G.connectionAt t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsTorsionFreeFamilyOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsTorsionFreeFamilyOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsTorsionFreeFamilyOn ``Submission.DifferentialGeometry.Geometry.Connection.IsTorsionFreeFamilyOn


def IsLeviCivitaFamilyOn
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D) : Prop :=
  forall t : RealTimeInterval.FlowTime D,
    IsLeviCivita (I := I) (G.connectionAt t) (G.metricAt t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsLeviCivitaFamilyOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsLeviCivitaFamilyOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsLeviCivitaFamilyOn ``Submission.DifferentialGeometry.Geometry.Connection.IsLeviCivitaFamilyOn

end Family

end DifferentialGeometry.Geometry.Connection
