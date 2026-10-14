import Submission.DifferentialGeometry.Geometry.Connection.Smoothness
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

open _root_.Submission.DifferentialGeometry.Analysis
namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {A Time : Type*} [CommRing A] [Algebra Real A]

abbrev RicciTensorField (Time : Type*) :=
  Time -> (x : M) -> TangentSpace I x -> TangentSpace I x -> Real

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.RicciTensorField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.RicciTensorField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.RicciTensorField ``Submission.DifferentialGeometry.PDE.RicciFlow.RicciTensorField

def MetricVariationEquation
    (td : TimeDerivativeData Real A Time)
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (Ric : RicciTensorField (I := I) (M := M) Time) : Prop :=
  forall (t : Time) (x : M) (X Y : TangentSpace I x),
    metricTimeDerivative td G t x X Y = (-2 : Real) * Ric t x X Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.MetricVariationEquation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.MetricVariationEquation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.MetricVariationEquation ``Submission.DifferentialGeometry.PDE.RicciFlow.MetricVariationEquation

theorem metric_dt_eq_neg_two_ricci_of_metricVariationEquation
    (td : TimeDerivativeData Real A Time)
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (Ric : RicciTensorField (I := I) (M := M) Time)
    (hEq : MetricVariationEquation td G Ric)
    (t : Time) (x : M) (X Y : TangentSpace I x) :
    metricTimeDerivative td G t x X Y = (-2 : Real) * Ric t x X Y :=
  hEq t x X Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metric_dt_eq_neg_two_ricci_of_metricVariationEquation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metric_dt_eq_neg_two_ricci_of_metricVariationEquation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metric_dt_eq_neg_two_ricci_of_metricVariationEquation ``Submission.DifferentialGeometry.PDE.RicciFlow.metric_dt_eq_neg_two_ricci_of_metricVariationEquation

def MetricVariationEquationDerivAt
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (Ric : RicciTensorField (I := I) (M := M) Real) (t : Real) : Prop :=
  forall (x : M) (X Y : TangentSpace I x),
    HasDerivAt
      (fun s : Real => (G.metric s).inner x X Y)
      ((-2 : Real) * Ric t x X Y)
      t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.MetricVariationEquationDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.MetricVariationEquationDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.MetricVariationEquationDerivAt ``Submission.DifferentialGeometry.PDE.RicciFlow.MetricVariationEquationDerivAt

theorem metric_deriv_eq_neg_two_ricci_of_metricVariationEquationDerivAt
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (Ric : RicciTensorField (I := I) (M := M) Real) {t : Real}
    (hEq : MetricVariationEquationDerivAt (I := I) G Ric t)
    (x : M) (X Y : TangentSpace I x) :
    deriv (fun s : Real => (G.metric s).inner x X Y) t =
      (-2 : Real) * Ric t x X Y :=
  (hEq x X Y).deriv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metric_deriv_eq_neg_two_ricci_of_metricVariationEquationDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metric_deriv_eq_neg_two_ricci_of_metricVariationEquationDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metric_deriv_eq_neg_two_ricci_of_metricVariationEquationDerivAt ``Submission.DifferentialGeometry.PDE.RicciFlow.metric_deriv_eq_neg_two_ricci_of_metricVariationEquationDerivAt

section Interval

variable [FiniteDimensional Real E] [CompleteSpace E]
variable [SigmaCompactSpace M] [T2Space M]
variable [IsManifold I 1 M]

def MetricConnectionFamilyVariationEquationOn
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (Ric : RicciTensorField (I := I) (M := M) Real) : Prop :=
  forall (t : RealTimeInterval.RegularTime D) (x : M) (X Y : TangentSpace I x),
    HasDerivWithinAt
      (fun s : Real => (G.metric s).inner x X Y)
      ((-2 : Real) * Ric (t : Real) x X Y)
      D.carrier
      (t : Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.MetricConnectionFamilyVariationEquationOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.MetricConnectionFamilyVariationEquationOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.MetricConnectionFamilyVariationEquationOn ``Submission.DifferentialGeometry.PDE.RicciFlow.MetricConnectionFamilyVariationEquationOn

structure MetricEvolutionDataOn (D : RealTimeInterval) where
  family : MetricConnectionFamilyOn (I := I) (M := M) D
  drivingTensor : RicciTensorField (I := I) (M := M) Real

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.MetricEvolutionDataOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.MetricEvolutionDataOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.MetricEvolutionDataOn ``Submission.DifferentialGeometry.PDE.RicciFlow.MetricEvolutionDataOn

structure IsMetricEvolutionOn
    {D : RealTimeInterval}
    (S : MetricEvolutionDataOn (I := I) (M := M) D) : Prop where
  smoothMetric : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric
  smoothConnection : DifferentialGeometry.Geometry.Connection.ConnectionFamilySmoothOn (I := I)
    (M := M) S.family
  leviCivita : DifferentialGeometry.Geometry.Connection.IsLeviCivitaFamilyOn (I := I) S.family
  equation : MetricConnectionFamilyVariationEquationOn (I := I) S.family S.drivingTensor

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IsMetricEvolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IsMetricEvolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IsMetricEvolutionOn ``Submission.DifferentialGeometry.PDE.RicciFlow.IsMetricEvolutionOn

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I 1 M] in
theorem metric_derivWithin_eq_neg_two_ricci_of_metricVariationEquationOn
    {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    (Ric : RicciTensorField (I := I) (M := M) Real)
    (hEq : MetricConnectionFamilyVariationEquationOn (I := I) G Ric)
    (t : RealTimeInterval.RegularTime D) (x : M) (X Y : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real => (G.metric s).inner x X Y)
      ((-2 : Real) * Ric (t : Real) x X Y)
      D.carrier
      (t : Real) :=
  hEq t x X Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metric_derivWithin_eq_neg_two_ricci_of_metricVariationEquationOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metric_derivWithin_eq_neg_two_ricci_of_metricVariationEquationOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metric_derivWithin_eq_neg_two_ricci_of_metricVariationEquationOn ``Submission.DifferentialGeometry.PDE.RicciFlow.metric_derivWithin_eq_neg_two_ricci_of_metricVariationEquationOn

omit [SigmaCompactSpace M] [T2Space M] [IsManifold I 1 M] in
theorem metric_derivWithin_eq_neg_two_drivingTensor_of_isMetricEvolutionOn
    {D : RealTimeInterval}
    (S : MetricEvolutionDataOn (I := I) (M := M) D)
    (hS : IsMetricEvolutionOn (I := I) S)
    (t : RealTimeInterval.RegularTime D) (x : M) (X Y : TangentSpace I x) :
    HasDerivWithinAt
      (fun s : Real => (S.family.metric s).inner x X Y)
      ((-2 : Real) * S.drivingTensor (t : Real) x X Y)
      D.carrier
      (t : Real) :=
  hS.equation t x X Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metric_derivWithin_eq_neg_two_drivingTensor_of_isMetricEvolutionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metric_derivWithin_eq_neg_two_drivingTensor_of_isMetricEvolutionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metric_derivWithin_eq_neg_two_drivingTensor_of_isMetricEvolutionOn ``Submission.DifferentialGeometry.PDE.RicciFlow.metric_derivWithin_eq_neg_two_drivingTensor_of_isMetricEvolutionOn

end Interval

end DifferentialGeometry.PDE.RicciFlow
