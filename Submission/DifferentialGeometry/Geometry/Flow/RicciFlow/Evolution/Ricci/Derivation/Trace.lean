import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Components
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Pairing
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Christoffel
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.Evolution
import Submission.DifferentialGeometry.Geometry.Coordinates.Frame.Coordinate
import Submission.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import Submission.DifferentialGeometry.Bundle.PartialMfderiv.ModelMixed
import Submission.DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative
import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.Contractions
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Identities
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Sections
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.MetricFlatBasis
import Mathlib.Tactic.Ring

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
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

section Components

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {u : Set M}

def RicciTensorRealizesRm04TraceInFrameOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall t : Real,
    DifferentialGeometry.Geometry.Curvature.ricciTensorRealizesRm04TraceInFrame
      (I := I) (S.ricci t) (Rm04 t) (gInv t) frame

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.RicciTensorRealizesRm04TraceInFrameOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.RicciTensorRealizesRm04TraceInFrameOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.RicciTensorRealizesRm04TraceInFrameOn ``Submission.DifferentialGeometry.PDE.RicciFlow.RicciTensorRealizesRm04TraceInFrameOn

def RicciTensorRealizesRm04FirstTraceInFrameOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall t : Real,
    DifferentialGeometry.Geometry.Curvature.RicciTensorRealizesRm04FirstTraceInFrame
      (I := I) (S.ricci t) (Rm04 t) (gInv t) frame

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.RicciTensorRealizesRm04FirstTraceInFrameOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.RicciTensorRealizesRm04FirstTraceInFrameOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.RicciTensorRealizesRm04FirstTraceInFrameOn ``Submission.DifferentialGeometry.PDE.RicciFlow.RicciTensorRealizesRm04FirstTraceInFrameOn

def RicciTensorRealizesRm04FirstTraceInFrameOnRegular
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D,
    DifferentialGeometry.Geometry.Curvature.RicciTensorRealizesRm04FirstTraceInFrame
      (I := I) (S.ricci (t : Real)) (Rm04 (t : Real)) (gInv (t : Real)) frame

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.RicciTensorRealizesRm04FirstTraceInFrameOnRegular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.RicciTensorRealizesRm04FirstTraceInFrameOnRegular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.RicciTensorRealizesRm04FirstTraceInFrameOnRegular ``Submission.DifferentialGeometry.PDE.RicciFlow.RicciTensorRealizesRm04FirstTraceInFrameOnRegular

omit [DecidableEq Idx] in
omit [SigmaCompactSpace M] in
theorem ricciCompInFrame_eq_rm04_trace
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (htrace : RicciTensorRealizesRm04TraceInFrameOn
      (I := I) S Rm04 gInv frame)
    (t : Real) (x : M) (i j : Idx) :
    ricciCompInFrame (I := I) S frame t x i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv t x k l *
          DifferentialGeometry.Geometry.Curvature.rm04Comp (I := I) (Rm04 t) frame x k i j l := by
  unfold ricciCompInFrame
  change (S.base.ricciAt t x)
    (DifferentialGeometry.Geometry.Curvature.vec2 (frame i x) (frame j x)) = _
  rw [← S.base.ricci_apply t x]
  exact DifferentialGeometry.Geometry.Curvature.ricciComp_eq_trace (I := I)
    (S.ricci t) (Rm04 t) (gInv t) frame (htrace t) x i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciCompInFrame_eq_rm04_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciCompInFrame_eq_rm04_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciCompInFrame_eq_rm04_trace ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciCompInFrame_eq_rm04_trace

omit [SigmaCompactSpace M] [T2Space M] in
private theorem metricInverseInBasis_of_solution_frame
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (t : Real) {x : M} (hx : x ∈ u) :
    Tensor0SBundle.MetricInverseInBasis
      (I := I) (M := M) (S.family.metric t) x
      (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) := by
  intro i j
  constructor
  · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
      (hinv t x hx i j).1
  · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
      (hinv t x hx i j).2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.metricInverseInBasis_of_solution_frame
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.metricInverseInBasis_of_solution_frame target :: scope.openDecls } }

omit [SigmaCompactSpace M] [T2Space M] in
theorem metricInverseInBasis_of_local
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (t : Real) {x : M} (hx : x ∈ u) :
    Tensor0SBundle.MetricInverseInBasis
      (I := I) (M := M) (S.family.metric t) x
      (hframe.toBasisAt hx) (fun i j : Idx => gInv t x i j) := by
  intro i j
  constructor
  · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
      (hinv t x hx i j).1
  · simpa [metricCompInFrame, IsLocalFrameOn.toBasisAt_coe] using
      (hinv t x hx i j).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricInverseInBasis_of_local then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricInverseInBasis_of_local"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricInverseInBasis_of_local ``Submission.DifferentialGeometry.PDE.RicciFlow.metricInverseInBasis_of_local

omit [SigmaCompactSpace M] in
theorem ricciTensorRealizesRm04FirstTraceInFrameOnRegular_of_rm13Trace
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (hRicTrace13 : forall t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime
      D,
      DifferentialGeometry.Geometry.Curvature.ricciTensorRealizesRm13Trace (I := I)
        (S.ricci (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      (x : M),
      DifferentialGeometry.Geometry.Curvature.Rm04LowersRm13At (I := I)
        (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x))
    :
    RicciTensorRealizesRm04FirstTraceInFrameOnRegular
      (I := I) S Rm04 gInv frame := by
  intro t x i j
  have hx : x ∈ u := hcover x
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) (M := M) (S.family.metric (t : Real)) x
        (hframe.toBasisAt hx)
        (fun a b : Idx => gInv (t : Real) x a b) :=
    metricInverseInBasis_of_local
      (I := I) S gInv frame hframe hinv (t : Real) hx
  have hAt :=
    DifferentialGeometry.Geometry.Curvature.ricciFirstTraceAt_of_rm13_section
      (I := I) (S.family.metric (t : Real)) (hframe.toBasisAt hx)
      (fun a b : Idx => gInv (t : Real) x a b) hinvAt
      (S.ricci (t : Real)) (Rm13 (t : Real)) (Rm04 (t : Real))
      (hRicTrace13 t) (hLower t x)
  simpa [DifferentialGeometry.Geometry.Curvature.RicciTensorRealizesRm04FirstTraceInFrame,
    IsLocalFrameOn.toBasisAt_coe] using hAt i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciTensorRealizesRm04FirstTraceInFrameOnRegular_of_rm13Trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciTensorRealizesRm04FirstTraceInFrameOnRegular_of_rm13Trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciTensorRealizesRm04FirstTraceInFrameOnRegular_of_rm13Trace ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciTensorRealizesRm04FirstTraceInFrameOnRegular_of_rm13Trace

def ConnectionLocallySmoothOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) : Prop :=
  forall t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D,
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (S.family.connection (t : Real)) (1 : WithTop ℕ∞)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ConnectionLocallySmoothOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ConnectionLocallySmoothOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ConnectionLocallySmoothOn ``Submission.DifferentialGeometry.PDE.RicciFlow.ConnectionLocallySmoothOn

omit [SigmaCompactSpace M] [T2Space M] in
theorem connSmoothOfSolution
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (s : Real) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (S.family.connection s) (1 : WithTop ℕ∞) := by
  simpa [SolutionFamily.connection, metricCov] using
    DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
      (I := I) (M := M) (S.base.metric s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.connSmoothOfSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.connSmoothOfSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.connSmoothOfSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.connSmoothOfSolution

omit [SigmaCompactSpace M] [T2Space M] in
theorem connCurvOfSolution
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (x₀ : M) (s : Real) :
    DifferentialGeometry.Geometry.Curvature.ConnectionCurvatureCoordAt (I := I)
      (S.family.connection s) x₀ := by
  have htop :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) (S.family.connection s) ∞ := by
    simpa [SolutionFamily.connection, metricCov] using
      metricCov_smooth (I := I) (M := M) (S.base.metric s)
  exact DifferentialGeometry.Geometry.Curvature.connection_curvature_coord_of_christoffel
    (I := I) (S.family.connection s) htop x₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.connCurvOfSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.connCurvOfSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.connCurvOfSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.connCurvOfSolution

omit [SigmaCompactSpace M] in
theorem rm13OfSolution
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (s : Real) :
    DifferentialGeometry.Geometry.Curvature.rm13RealizesConnection (I := I)
      (S.family.connection s) (S.base.rm13 s) := by
  have h := (metricCurvatureSections (I := I) (M := M) (S.base.metric s)).rm13Realizes
  change DifferentialGeometry.Geometry.Curvature.rm13RealizesConnection (I := I)
    (metricCov (I := I) (M := M) (S.base.metric s))
    (metricRm13 (I := I) (M := M) (S.base.metric s)) at h
  change DifferentialGeometry.Geometry.Curvature.rm13RealizesConnection (I := I)
    (metricCov (I := I) (M := M) (S.base.metric s))
    (metricRm13 (I := I) (M := M) (S.base.metric s))
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rm13OfSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rm13OfSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rm13OfSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.rm13OfSolution

omit [SigmaCompactSpace M] in
theorem ricciTraceOfSolution
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (s : Real) :
    DifferentialGeometry.Geometry.Curvature.ricciTensorRealizesRm13Trace (I := I)
      (S.ricci s) (S.base.rm13 s) := by
  have h := (metricCurvatureSections (I := I) (M := M) (S.base.metric s)).ricciRealizes
  change DifferentialGeometry.Geometry.Curvature.ricciTensorRealizesRm13Trace (I := I)
    (metricRicci (I := I) (M := M) (S.base.metric s))
    (metricRm13 (I := I) (M := M) (S.base.metric s)) at h
  simpa only [SolutionOn.ricci_eq, SolutionFamily.ricci, SolutionFamily.rm13] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciTraceOfSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciTraceOfSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciTraceOfSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciTraceOfSolution

def RicciSymmetricInFrameOnRegular
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) x i j,
    ricciCompInFrame (I := I) S frame (t : Real) x i j =
      ricciCompInFrame (I := I) S frame (t : Real) x j i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.RicciSymmetricInFrameOnRegular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.RicciSymmetricInFrameOnRegular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.RicciSymmetricInFrameOnRegular ``Submission.DifferentialGeometry.PDE.RicciFlow.RicciSymmetricInFrameOnRegular

omit [SigmaCompactSpace M] [T2Space M] in
theorem lcAt_regular
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) :
    DifferentialGeometry.Geometry.Connection.IsLeviCivita (I := I)
      (S.family.connection (t : Real)) (S.family.metric (t : Real)) := by
  simpa [DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.connectionAt,
    DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn.metricAt] using
    SolutionOn.leviCivita (I := I) S
      (DifferentialGeometry.Geometry.Curvature.RealTimeInterval.regularToFlow t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.lcAt_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.lcAt_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.lcAt_regular ``Submission.DifferentialGeometry.PDE.RicciFlow.lcAt_regular

omit [SigmaCompactSpace M] [T2Space M] in
private theorem rm04Realizes_regular
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (hRm13 : forall t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Geometry.Curvature.rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      (x : M),
      DifferentialGeometry.Geometry.Curvature.Rm04LowersRm13At (I := I)
        (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x))
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) :
    DifferentialGeometry.Geometry.Curvature.rm04RealizesConnection (I := I)
      (S.family.metric (t : Real))
      (S.family.connection (t : Real)) (Rm04 (t : Real)) :=
  DifferentialGeometry.Geometry.Curvature.rm04RealizesLower (I := I) (S.family.metric (t : Real))
    (S.family.connection (t : Real)) (Rm13 (t : Real)) (Rm04 (t : Real))
    (hRm13 t) (hLower t)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.rm04Realizes_regular
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.rm04Realizes_regular target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem rm04OutputSkew_regular
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (hRm13 : forall t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Geometry.Curvature.rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      (x : M),
      DifferentialGeometry.Geometry.Curvature.Rm04LowersRm13At (I := I)
        (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x)) :
    forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Geometry.Curvature.Rm04OutputSkewAt (I := I) (Rm04 (t : Real) x) := by
  intro t x
  exact DifferentialGeometry.Geometry.Connection.rm04OutputSkew_ofMC
    (I := I) (S.family.metric (t : Real)) (S.family.connection (t : Real))
    (connSmoothOfSolution (I := I) S (t : Real))
    (DifferentialGeometry.Geometry.Connection.metricCompatible_of_isLeviCivita
      (I := I) (lcAt_regular (I := I) S t))
    (Rm04 (t : Real))
    (rm04Realizes_regular (I := I) S Rm13 Rm04 hRm13 hLower t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rm04OutputSkew_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rm04OutputSkew_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rm04OutputSkew_regular ``Submission.DifferentialGeometry.PDE.RicciFlow.rm04OutputSkew_regular

omit [SigmaCompactSpace M] in
theorem rm04FirstBianchi_regular
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (hRm13 : forall t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Geometry.Curvature.rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      (x : M),
      DifferentialGeometry.Geometry.Curvature.Rm04LowersRm13At (I := I)
        (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x)) :
    forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
      DifferentialGeometry.Geometry.Curvature.FirstBianchiAt (I := I) (Rm04 (t : Real) x) := by
  intro t x
  exact DifferentialGeometry.Geometry.Connection.firstBianchi_ofTF
    (I := I) (S.family.metric (t : Real)) (S.family.connection (t : Real))
    (connSmoothOfSolution (I := I) S (t : Real))
    (DifferentialGeometry.Geometry.Connection.torsionFree_of_isLeviCivita
      (I := I) (lcAt_regular (I := I) S t))
    (Rm04 (t : Real))
    (rm04Realizes_regular (I := I) S Rm13 Rm04 hRm13 hLower t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rm04FirstBianchi_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rm04FirstBianchi_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rm04FirstBianchi_regular ``Submission.DifferentialGeometry.PDE.RicciFlow.rm04FirstBianchi_regular

omit [SigmaCompactSpace M] in
theorem rm04PairSymm_regular
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (hRm13 : forall t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Geometry.Curvature.rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      (x : M),
      DifferentialGeometry.Geometry.Curvature.Rm04LowersRm13At (I := I)
        (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x)) :
    forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
      forall W X Y Z : TangentSpace I x,
        Rm04 (t : Real) x (DifferentialGeometry.Geometry.Curvature.vec4 W X Y Z) =
          Rm04 (t : Real) x (DifferentialGeometry.Geometry.Curvature.vec4 Y Z W X) := by
  intro t x
  exact DifferentialGeometry.Geometry.Connection.rm04PairSymm_ofLC
    (I := I) (S.family.metric (t : Real)) (S.family.connection (t : Real))
    (connSmoothOfSolution (I := I) S (t : Real))
    (lcAt_regular (I := I) S t) (Rm04 (t : Real))
    (rm04Realizes_regular (I := I) S Rm13 Rm04 hRm13 hLower t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rm04PairSymm_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rm04PairSymm_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rm04PairSymm_regular ``Submission.DifferentialGeometry.PDE.RicciFlow.rm04PairSymm_regular

omit [SigmaCompactSpace M] in
theorem rm04InputSkew_regular_first_two
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (hRm13 : forall t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Geometry.Curvature.rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      (x : M),
      DifferentialGeometry.Geometry.Curvature.Rm04LowersRm13At (I := I)
        (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x)) :
    forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
      forall X Y Z W : TangentSpace I x,
        Rm04 (t : Real) x (DifferentialGeometry.Geometry.Curvature.vec4 Y X Z W) =
          -Rm04 (t : Real) x (DifferentialGeometry.Geometry.Curvature.vec4 X Y Z W) := by
  intro t x
  exact DifferentialGeometry.Geometry.Connection.rm04InputSkew_ofRealizes
    (I := I) (S.family.metric (t : Real)) (S.family.connection (t : Real))
    (Rm04 (t : Real))
    (rm04Realizes_regular (I := I) S Rm13 Rm04 hRm13 hLower t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rm04InputSkew_regular_first_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rm04InputSkew_regular_first_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rm04InputSkew_regular_first_two ``Submission.DifferentialGeometry.PDE.RicciFlow.rm04InputSkew_regular_first_two

omit [SigmaCompactSpace M] in
theorem rm04InputSkew_regular
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm13 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor13Section (I := I) (M := M))
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (hRm13 : forall t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D,
      DifferentialGeometry.Geometry.Curvature.rm13RealizesConnection (I := I)
        (S.family.connection (t : Real)) (Rm13 (t : Real)))
    (hLower : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      (x : M),
      DifferentialGeometry.Geometry.Curvature.Rm04LowersRm13At (I := I)
        (S.family.metric (t : Real)) x
        (Rm13 (t : Real) x) (Rm04 (t : Real) x)) :
    forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
      forall X Y Z W : TangentSpace I x,
        Rm04 (t : Real) x (DifferentialGeometry.Geometry.Curvature.vec4 Y X Z W) =
          -Rm04 (t : Real) x (DifferentialGeometry.Geometry.Curvature.vec4 X Y Z W) :=
  rm04InputSkew_regular_first_two
    (I := I) S Rm13 Rm04 hRm13 hLower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rm04InputSkew_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rm04InputSkew_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rm04InputSkew_regular ``Submission.DifferentialGeometry.PDE.RicciFlow.rm04InputSkew_regular

omit [SigmaCompactSpace M] in
theorem ricciSymm_regular
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {u : Set M}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hcover : forall x : M, x ∈ u)
    (hinv : InvMetricLocal (I := I) S gInv frame u)
    (hTrace : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      (x : M),
      DifferentialGeometry.Geometry.Curvature.RicciRealizesRm04FirstTraceAt (I := I)
        (S.ricci (t : Real) x) (Rm04 (t : Real) x)
        (gInv (t : Real) x)
        (hframe.toBasisAt (hcover x)))
    (hPair : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      (x : M),
      forall W X Y Z : TangentSpace I x,
        Rm04 (t : Real) x (DifferentialGeometry.Geometry.Curvature.vec4 W X Y Z) =
          Rm04 (t : Real) x (DifferentialGeometry.Geometry.Curvature.vec4 Y Z W X))
    (hOutput : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      (x : M),
      DifferentialGeometry.Geometry.Curvature.Rm04OutputSkewAt (I := I) (Rm04 (t : Real) x))
    (hInput : forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
      (x : M),
      forall X Y Z W : TangentSpace I x,
        Rm04 (t : Real) x (DifferentialGeometry.Geometry.Curvature.vec4 Y X Z W) =
          -Rm04 (t : Real) x (DifferentialGeometry.Geometry.Curvature.vec4 X Y Z W)) :
    RicciSymmetricInFrameOnRegular (I := I) S frame := by
  intro t x i j
  let basis := hframe.toBasisAt (hcover x)
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) (M := M) (S.family.metric (t : Real)) x
        basis (fun a b : Idx => gInv (t : Real) x a b) :=
    metricInverseInBasis_of_local
      (I := I) S gInv frame hframe hinv (t : Real)
      (hcover x)
  have hsym :=
    DifferentialGeometry.Geometry.Curvature.ricciSymm_of_rm04 (I := I) basis
      (fun a b : Idx => gInv (t : Real) x a b)
      (S.ricci (t : Real) x) (Rm04 (t : Real) x)
      (hTrace t x) (hPair t x) (hOutput t x) (hInput t x)
      (Tensor0SBundle.MetricInverseInBasis.symmetric
        (I := I) (M := M) (S.family.metric (t : Real)) x basis
        (fun a b : Idx => gInv (t : Real) x a b) hinvAt)
      i j
  simpa [basis, ricciCompInFrame, DifferentialGeometry.Geometry.Curvature.ricciComp,
    DifferentialGeometry.Geometry.Curvature.ricciComp, IsLocalFrameOn.toBasisAt_coe] using hsym

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ricciSymm_regular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ricciSymm_regular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ricciSymm_regular ``Submission.DifferentialGeometry.PDE.RicciFlow.ricciSymm_regular

def RiemannEvolutionEquationInFrameOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  forall (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M)
    (a i j l : Idx),
    HasDerivWithinAt
      (fun s : Real => DifferentialGeometry.Geometry.Curvature.rm04Comp (I := I) (Rm04 s) frame x a
        i j l)
      (rm04Dt (t : Real) x a i j l)
      D.carrier
      (t : Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.RiemannEvolutionEquationInFrameOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.RiemannEvolutionEquationInFrameOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.RiemannEvolutionEquationInFrameOn ``Submission.DifferentialGeometry.PDE.RicciFlow.RiemannEvolutionEquationInFrameOn

end Components

end DifferentialGeometry.PDE.RicciFlow
