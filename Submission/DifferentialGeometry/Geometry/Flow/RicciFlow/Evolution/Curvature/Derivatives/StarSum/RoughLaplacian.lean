import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.IteratedCovariantDerivativeFields
import Submission.DifferentialGeometry.Geometry.Connection.MetricTrace.CovariantDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle

open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

omit [I.Boundaryless] in
omit [Module.Finite ℝ E] in
omit [SigmaCompactSpace M] in
theorem nabla_roughLap0S_nablaKRm
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) (S.base.metric t) x basis gInv)
    (X : TangentSpace I x) (tail : Fin (4 + k) -> TangentSpace I x) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (4 + k) (S.family.connection t)
        (metricTraceFirstTwoField (I := I) (M := M) (S.base.metric t)
          (nablaKRm04Field (I := I) S t (k + 2))) x (Fin.cons X tail) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          nablaKRm04Field (I := I) S t (k + 3) x
            (Fin.cons X (metricTraceInput (I := I) (basis i) (basis j) tail)) := by
  have hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I)
      (S.family.connection t) (S.base.metric t) := by
    simpa [SolutionFamily.connection, metricCov] using
      leviCivitaConnectionOfMetric_isMetricCompatible (I := I) (S.base.metric t)
  refine (nabla_metricTraceFirstTwo0S (I := I) (M := M) (S.family.connection t)
    (S.base.metric t) hmc (nablaKRm04Field (I := I) S t (k + 2)) basis gInv hinv X
    tail).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nabla_roughLap0S_nablaKRm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nabla_roughLap0S_nablaKRm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nabla_roughLap0S_nablaKRm ``Submission.DifferentialGeometry.PDE.RicciFlow.nabla_roughLap0S_nablaKRm

omit [I.Boundaryless] in
omit [Module.Finite ℝ E] in
omit [SigmaCompactSpace M] in
theorem spatialComm_nablaKRm_traceDiff
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) (S.base.metric t) x basis gInv)
    (X : TangentSpace I x) (tail : Fin (4 + k) -> TangentSpace I x) :
    metricTraceFirstTwo0STensor (I := I) (S.base.metric t)
        (nablaKRm04Field (I := I) S t (k + 3) x)
        (Fin.cons X tail) -
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (4 + k) (S.family.connection t)
        (metricTraceFirstTwoField (I := I) (M := M) (S.base.metric t)
          (nablaKRm04Field (I := I) S t (k + 2))) x (Fin.cons X tail) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          (nablaKRm04Field (I := I) S t (k + 3) x
              (metricTraceInput (I := I) (basis i) (basis j) (Fin.cons X tail)) -
            nablaKRm04Field (I := I) S t (k + 3) x
              (Fin.cons X (metricTraceInput (I := I) (basis i) (basis j) tail))) := by
  rw [metricTraceFirstTwo0STensor_apply (I := I) (S.base.metric t)
    (nablaKRm04Field (I := I) S t (k + 3) x) (Fin.cons X tail)]
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) (S.base.metric t) basis gInv hinv
    (nablaKRm04Field (I := I) S t (k + 3) x) (Fin.cons X tail)]
  rw [metricTrace0S2InBasis]
  rw [nabla_roughLap0S_nablaKRm (I := I) (M := M) S t k basis gInv hinv X tail]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.spatialComm_nablaKRm_traceDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.spatialComm_nablaKRm_traceDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.spatialComm_nablaKRm_traceDiff ``Submission.DifferentialGeometry.PDE.RicciFlow.spatialComm_nablaKRm_traceDiff

omit [I.Boundaryless] in
omit [Module.Finite ℝ E] in
omit [SigmaCompactSpace M] in
theorem spatialComm_nablaKRm_split
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (k : ℕ)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) (M := M) (S.base.metric (t : Real)) x basis gInv)
    (X : TangentSpace I x) (tail : Fin (4 + k) -> TangentSpace I x) :
    metricTraceFirstTwo0STensor (I := I) (S.base.metric (t : Real))
        (nablaKRm04Field (I := I) S (t : Real) (k + 3) x)
        (Fin.cons X tail) -
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (4 + k) (S.family.connection (t : Real))
        (metricTraceFirstTwoField (I := I) (M := M) (S.base.metric (t : Real))
          (nablaKRm04Field (I := I) S (t : Real) (k + 2))) x (Fin.cons X tail) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          ((nablaKRm04Field (I := I) S (t : Real) (k + 3) x
                (metricTraceInput (I := I) (basis i) (basis j) (Fin.cons X tail)) -
              nablaKRm04Field (I := I) S (t : Real) (k + 3) x
                (metricTraceInput (I := I) (basis i) X (Fin.cons (basis j) tail))) +
            curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
              (nablaKRm04Field (I := I) S (t : Real) (k + 1) x)
              (basis i) X (Fin.cons (basis j) tail)) := by
  rw [spatialComm_nablaKRm_traceDiff (I := I) S (t : Real) k basis gInv hinv X tail]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have h := (nablaKRm04_ricciIdentityAt (I := I) S t (k + 1) x)
    (basis i) X (Fin.cons (basis j) tail)
  have hCC :
      (nablaKRm04Field (I := I) S (t : Real) (k + 3) x)
          (Fin.cons X (metricTraceInput (I := I) (basis i) (basis j) tail)) =
        (nablaKRm04Field (I := I) S (t : Real) (k + 3) x)
          (metricTraceInput (I := I) X (basis i) (Fin.cons (basis j) tail)) := rfl
  rw [hCC]
  linarith [h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.spatialComm_nablaKRm_split then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.spatialComm_nablaKRm_split"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.spatialComm_nablaKRm_split ``Submission.DifferentialGeometry.PDE.RicciFlow.spatialComm_nablaKRm_split

end DifferentialGeometry.PDE.RicciFlow
