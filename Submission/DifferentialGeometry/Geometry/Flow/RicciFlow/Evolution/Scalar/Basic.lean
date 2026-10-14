import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.Contractions
import Submission.DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization
import Submission.DifferentialGeometry.Geometry.Operator.Family.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.RicciNorm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.InverseSmooth
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.Covariant
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.Evolution
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.Trace
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.ChristoffelAlgebra
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.ChristoffelCoordinates
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.Bianchi
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.Commutator
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.CoordinateRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.CoordinateIdentities
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Equation.Lichnerowicz
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Estimate.QuadraticForm
import Mathlib.Algebra.Order.Chebyshev

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

def ScalarPreBianchiEvolutionEquationOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (scalar scalarLap contractedRicciHessian ricciNormSq : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => scalar s x)
      (2 * scalarLap (t : Real) x -
        2 * contractedRicciHessian (t : Real) x +
        2 * ricciNormSq (t : Real) x)
      D.carrier
      (t : Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ScalarPreBianchiEvolutionEquationOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ScalarPreBianchiEvolutionEquationOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ScalarPreBianchiEvolutionEquationOn ``Submission.DifferentialGeometry.PDE.RicciFlow.ScalarPreBianchiEvolutionEquationOn

def ScalarContractedBianchiReductionOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (scalarLap contractedRicciHessian : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
    2 * scalarLap (t : Real) x -
        2 * contractedRicciHessian (t : Real) x =
      scalarLap (t : Real) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ScalarContractedBianchiReductionOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ScalarContractedBianchiReductionOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ScalarContractedBianchiReductionOn ``Submission.DifferentialGeometry.PDE.RicciFlow.ScalarContractedBianchiReductionOn

def ScalarSecondDerivativeContractedBianchiOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (scalarLap contractedRicciHessian : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
    contractedRicciHessian (t : Real) x =
      (1 / 2 : Real) * scalarLap (t : Real) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ScalarSecondDerivativeContractedBianchiOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ScalarSecondDerivativeContractedBianchiOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ScalarSecondDerivativeContractedBianchiOn ``Submission.DifferentialGeometry.PDE.RicciFlow.ScalarSecondDerivativeContractedBianchiOn

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem scalarContractedBianchiReductionOn_of_secondDerivativeContractedBianchi
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (scalarLap contractedRicciHessian : Real -> M -> Real)
    (hbianchi : ScalarSecondDerivativeContractedBianchiOn (D := D)
      scalarLap contractedRicciHessian) :
    ScalarContractedBianchiReductionOn (D := D)
      scalarLap contractedRicciHessian := by
  intro t x
  rw [hbianchi t x]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalarContractedBianchiReductionOn_of_secondDerivativeContractedBianchi then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalarContractedBianchiReductionOn_of_secondDerivativeContractedBianchi"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalarContractedBianchiReductionOn_of_secondDerivativeContractedBianchi ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarContractedBianchiReductionOn_of_secondDerivativeContractedBianchi

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem scalarEvolutionEquationOn_of_contractedBianchi
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (scalar scalarLap contractedRicciHessian ricciNormSq : Real -> M -> Real)
    (hpre : ScalarPreBianchiEvolutionEquationOn (D := D)
      scalar scalarLap contractedRicciHessian ricciNormSq)
    (hbianchi : ScalarContractedBianchiReductionOn (D := D)
      scalarLap contractedRicciHessian) :
    ScalarEvolutionEquationOn (D := D) scalar scalarLap ricciNormSq := by
  intro t x
  exact (hpre t x).congr_deriv (by
    rw [hbianchi t x])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalarEvolutionEquationOn_of_contractedBianchi then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalarEvolutionEquationOn_of_contractedBianchi"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalarEvolutionEquationOn_of_contractedBianchi ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarEvolutionEquationOn_of_contractedBianchi

omit [SigmaCompactSpace M] in
theorem scalar_evolution_of_smooth_solution
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (hmetric : ∀ t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D,
      G.metric (t : Real) = S.family.metric (t : Real))
    (hconnection : ∀ t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D,
      G.connection (t : Real) = S.family.connection (t : Real)) :
    ScalarEvolutionEquationOn (D := D)
      S.scalar
      (fun t x => DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) G t (S.scalar t) x)
      (fun t x =>
        normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x)) := by
  intro t x
  exact hS.scalarEvolution G hmetric hconnection t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalar_evolution_of_smooth_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalar_evolution_of_smooth_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalar_evolution_of_smooth_solution ``Submission.DifferentialGeometry.PDE.RicciFlow.scalar_evolution_of_smooth_solution

def ScalarLaplacianRealizesHeatOperatorOn
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (scalar scalarLap : Real -> M -> Real) : Prop :=
  forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
    scalarLap t x =
      DifferentialGeometry.Geometry.Curvature.heatOperator (I := I) G t (scalar t) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn ``Submission.DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn

namespace ScalarLaplacianRealizesHeatOperatorOn

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem zero_drift
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real}
    {T : Real} {scalar scalarLap : Real -> M -> Real}
    (h : ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      scalarLap t x =
        DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift (I := I) G t
          (fun y : M => (0 : TangentSpace I y)) (scalar t) x := by
  intro t ht x
  calc
    scalarLap t x = DifferentialGeometry.Geometry.Curvature.heatOperator (I := I) G t (scalar t) x
      := h t ht x
    _ = DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift (I := I) G t
          (fun y : M => (0 : TangentSpace I y)) (scalar t) x := by
        rw [DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_zero_drift]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn.zero_drift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn.zero_drift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn.zero_drift ``Submission.DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn.zero_drift

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem of_laplacianAt
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real}
    {T : Real} {scalar scalarLap : Real -> M -> Real}
    (h : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      scalarLap t x = DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) G t (scalar t)
        x) :
    ScalarLaplacianRealizesHeatOperatorOn (I := I) G T scalar scalarLap := by
  intro t ht x
  simpa [DifferentialGeometry.Geometry.Curvature.heatOperator] using h t ht x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn.of_laplacianAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn.of_laplacianAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn.of_laplacianAt ``Submission.DifferentialGeometry.PDE.RicciFlow.ScalarLaplacianRealizesHeatOperatorOn.of_laplacianAt

end ScalarLaplacianRealizesHeatOperatorOn

end DifferentialGeometry.PDE.RicciFlow
