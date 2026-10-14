import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.Trace
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.ChristoffelAlgebra
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.ChristoffelCoordinates
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.Bianchi
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.Commutator
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.CoordinateRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.CoordinateIdentities
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Equation.Lichnerowicz
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Estimate.QuadraticForm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.TraceAlgebra
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.RmTrace
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.EvolutionEquation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {Idx : Type*} [Fintype Idx]

local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry ``Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry

private theorem sum_swap_four
    {R : Type*} [AddCommMonoid R]
    (F : Idx -> Idx -> Idx -> Idx -> R) :
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i j k l) =
      ∑ k : Idx, ∑ l : Idx, ∑ i : Idx, ∑ j : Idx, F i j k l := by
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx, F i j k l) =
        ∑ i : Idx, ∑ k : Idx, ∑ j : Idx, ∑ l : Idx, F i j k l := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
    _ = ∑ k : Idx, ∑ i : Idx, ∑ j : Idx, ∑ l : Idx, F i j k l := by
          rw [Finset.sum_comm]
    _ = ∑ k : Idx, ∑ l : Idx, ∑ i : Idx, ∑ j : Idx, F i j k l := by
          refine Finset.sum_congr rfl fun k _ => ?_
          calc
            (∑ i : Idx, ∑ j : Idx, ∑ l : Idx, F i j k l) =
                ∑ i : Idx, ∑ l : Idx, ∑ j : Idx, F i j k l := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.sum_comm]
            _ = ∑ l : Idx, ∑ i : Idx, ∑ j : Idx, F i j k l := by
                  rw [Finset.sum_comm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.sum_swap_four
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.sum_swap_four target :: scope.openDecls } }

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem scalarHessianFromNabla2Ric_trace_eq_roughLapRic_trace
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) :
    (∑ i : Idx, ∑ j : Idx,
      gInv t x i j *
        scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric t x i j) =
      scalarLaplacianTraceInFrame (M := M) gInv
        (roughLapRicInFrame (M := M) gInv nabla2Ric) t x := by
  classical
  unfold scalarHessianFromNabla2RicInFrame scalarLaplacianTraceInFrame
    roughLapRicInFrame
  calc
    (∑ i : Idx, ∑ j : Idx,
      gInv t x i j *
        (∑ k : Idx, ∑ l : Idx, gInv t x k l * nabla2Ric t x i j k l)) =
        ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          gInv t x i j * (gInv t x k l * nabla2Ric t x i j k l) := by
          simp [Finset.mul_sum]
    _ = ∑ k : Idx, ∑ l : Idx, ∑ i : Idx, ∑ j : Idx,
          gInv t x i j * (gInv t x k l * nabla2Ric t x i j k l) :=
          sum_swap_four
            (Idx := Idx)
            (fun i j k l =>
              gInv t x i j * (gInv t x k l * nabla2Ric t x i j k l))
    _ = ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
          gInv t x i j * (gInv t x k l * nabla2Ric t x k l i j) := by
          simp [mul_left_comm]
    _ = ∑ i : Idx, ∑ j : Idx,
          gInv t x i j *
            (∑ k : Idx, ∑ l : Idx,
              gInv t x k l * nabla2Ric t x k l i j) := by
          simp [Finset.mul_sum]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalarHessianFromNabla2Ric_trace_eq_roughLapRic_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalarHessianFromNabla2Ric_trace_eq_roughLapRic_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalarHessianFromNabla2Ric_trace_eq_roughLapRic_trace ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarHessianFromNabla2Ric_trace_eq_roughLapRic_trace

omit [SigmaCompactSpace M] [T2Space M] in
theorem scalarLaplacianTraceInFrame_realizes_heatOperator_of_nabla2RicTrace
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (nabla2Ric : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (scalarHess : Real -> (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (htrace : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      DifferentialGeometry.Geometry.Operator.ScalarLaplacianRealizesTraceAtInBasis (I := I)
        (G.connection t) (G.metric t)
        (hframe.toBasisAt (hcover x))
        (gInv t x) (scalarTraceInFrame (I := I) S gInv frame t)
        (scalarHess t x))
    (hcomp : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      forall i j : Idx,
        scalarHess t x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (frame i x)
          (frame j x)) =
          scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric t x i j) :
    ScalarLaplacianRealizesHeatOperatorOn (I := I) G T
      (scalarTraceInFrame (I := I) S gInv frame)
      (scalarLaplacianTraceInFrame (M := M) gInv
        (roughLapRicInFrame (M := M) gInv nabla2Ric)) := by
  refine scalarLaplacianTraceInFrame_realizes_heatOperator_of_laplacianAt
    (I := I) S G T gInv frame
    (roughLapRicInFrame (M := M) gInv nabla2Ric) ?_
  intro t ht x
  let basis := hframe.toBasisAt (hcover x)
  have hmetric :
      DifferentialGeometry.Geometry.Operator.metricTrace0S2InBasis (I := I) basis (gInv t x)
          (scalarHess t x) Fin.elim0 =
        ∑ i : Idx, ∑ j : Idx,
          gInv t x i j *
            scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric t x i j := by
    unfold DifferentialGeometry.Geometry.Operator.metricTrace0S2InBasis
    refine Finset.sum_congr rfl fun i _hi => ?_
    refine Finset.sum_congr rfl fun j _hj => ?_
    congr 1
    have hinput :
        DifferentialGeometry.Geometry.Operator.metricTraceInput (I := I) (basis i) (basis j)
          Fin.elim0 =
          DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (frame i x) (frame j x) := by
      have hbi : basis i = frame i x := by
        simp [basis, IsLocalFrameOn.toBasisAt_coe]
      have hbj : basis j = frame j x := by
        simp [basis, IsLocalFrameOn.toBasisAt_coe]
      rw [hbi, hbj]
      funext q
      fin_cases q
      · simp [DifferentialGeometry.Geometry.Operator.metricTraceInput,
        DifferentialGeometry.Geometry.Curvature.vec2,
        DifferentialGeometry.Geometry.Curvature.vec2]
      · rfl
    rw [hinput, hcomp t ht x i j]
  have htrace_tx := htrace t ht x
  unfold DifferentialGeometry.Geometry.Operator.ScalarLaplacianRealizesTraceAtInBasis at htrace_tx
  calc
    scalarLaplacianTraceInFrame (M := M) gInv
        (roughLapRicInFrame (M := M) gInv nabla2Ric) t x =
        ∑ i : Idx, ∑ j : Idx,
          gInv t x i j *
            scalarHessianFromNabla2RicInFrame (M := M) gInv nabla2Ric t x i j :=
          (scalarHessianFromNabla2Ric_trace_eq_roughLapRic_trace
            (M := M) gInv nabla2Ric t x).symm
    _ = DifferentialGeometry.Geometry.Operator.metricTrace0S2InBasis (I := I) basis (gInv t x)
          (scalarHess t x) Fin.elim0 := hmetric.symm
    _ = DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) G t
          (scalarTraceInFrame (I := I) S gInv frame t) x := by
        unfold DifferentialGeometry.Geometry.Curvature.laplacianAt
        exact htrace_tx.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.scalarLaplacianTraceInFrame_realizes_heatOperator_of_nabla2RicTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.scalarLaplacianTraceInFrame_realizes_heatOperator_of_nabla2RicTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.scalarLaplacianTraceInFrame_realizes_heatOperator_of_nabla2RicTrace ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarLaplacianTraceInFrame_realizes_heatOperator_of_nabla2RicTrace

end DifferentialGeometry.PDE.RicciFlow
