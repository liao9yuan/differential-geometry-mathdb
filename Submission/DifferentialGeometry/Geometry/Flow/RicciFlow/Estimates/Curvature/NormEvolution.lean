import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.Trace
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.ChristoffelAlgebra
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.ChristoffelCoordinates
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.Bianchi
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.Commutator
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.CoordinateRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.CoordinateIdentities
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Equation.Lichnerowicz
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Estimate.QuadraticForm
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry ``Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealHAddWithTopENatSomeTopOfNat_differentialGeometry

section Components

variable {Idx : Type*} [Fintype Idx]

def raisedRm04CompInFrame
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (a b c d : Idx) : Real :=
  ∑ p : Idx, ∑ q : Idx, ∑ r : Idx, ∑ s : Idx,
    gInv t x a p * gInv t x b q * gInv t x c r * gInv t x d s *
      DifferentialGeometry.Geometry.Curvature.rm04Comp (I := I) (Rm04 t) frame x p q r s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.raisedRm04CompInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.raisedRm04CompInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.raisedRm04CompInFrame ``Submission.DifferentialGeometry.PDE.RicciFlow.raisedRm04CompInFrame

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem raisedRm04CompInFrame_apply
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) (a b c d : Idx) :
    raisedRm04CompInFrame (I := I) Rm04 gInv frame t x a b c d =
      ∑ p : Idx, ∑ q : Idx, ∑ r : Idx, ∑ s : Idx,
        gInv t x a p * gInv t x b q * gInv t x c r * gInv t x d s *
          DifferentialGeometry.Geometry.Curvature.rm04Comp (I := I) (Rm04 t) frame x p q r s := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.raisedRm04CompInFrame_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.raisedRm04CompInFrame_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.raisedRm04CompInFrame_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.raisedRm04CompInFrame_apply

def rm04NormSqInFrame
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
      DifferentialGeometry.Geometry.Curvature.rm04Comp (I := I) (Rm04 t) frame x a b c d *
        raisedRm04CompInFrame (I := I) Rm04 gInv frame t x a b c d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rm04NormSqInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rm04NormSqInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rm04NormSqInFrame ``Submission.DifferentialGeometry.PDE.RicciFlow.rm04NormSqInFrame

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem rm04NormSqInFrame_apply
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (t : Real) (x : M) :
    rm04NormSqInFrame (I := I) Rm04 gInv frame t x =
      ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
        DifferentialGeometry.Geometry.Curvature.rm04Comp (I := I) (Rm04 t) frame x a b c d *
          raisedRm04CompInFrame (I := I) Rm04 gInv frame t x a b c d := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rm04NormSqInFrame_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rm04NormSqInFrame_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rm04NormSqInFrame_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.rm04NormSqInFrame_apply

private def derivProduct5RHS
    (u v w y z du dv dw dy dz : Real) : Real :=
  ((((du * v + u * dv) * w + (u * v) * dw) * y + ((u * v) * w) * dy) * z +
    (((u * v) * w) * y) * dz)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.derivProduct5RHS
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.derivProduct5RHS target :: scope.openDecls } }

def raisedRm04DerivRHSInFrame
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) (a b c d : Idx) : Real :=
  ∑ p : Idx, ∑ q : Idx, ∑ r : Idx, ∑ s : Idx,
    derivProduct5RHS
      (gInv t x a p)
      (gInv t x b q)
      (gInv t x c r)
      (gInv t x d s)
      (DifferentialGeometry.Geometry.Curvature.rm04Comp (I := I) (Rm04 t) frame x p q r s)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x a p)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x b q)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x c r)
      (inverseMetricEvolutionRHSInFrame (I := I) S gInv frame t x d s)
      (rm04Dt t x p q r s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.raisedRm04DerivRHSInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.raisedRm04DerivRHSInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.raisedRm04DerivRHSInFrame ``Submission.DifferentialGeometry.PDE.RicciFlow.raisedRm04DerivRHSInFrame

def rm04NormDerivRHSInFrame
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (t : Real) (x : M) : Real :=
  ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
    (rm04Dt t x a b c d *
        raisedRm04CompInFrame (I := I) Rm04 gInv frame t x a b c d +
      DifferentialGeometry.Geometry.Curvature.rm04Comp (I := I) (Rm04 t) frame x a b c d *
        raisedRm04DerivRHSInFrame (I := I) S Rm04 gInv frame rm04Dt
          t x a b c d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rm04NormDerivRHSInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rm04NormDerivRHSInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rm04NormDerivRHSInFrame ``Submission.DifferentialGeometry.PDE.RicciFlow.rm04NormDerivRHSInFrame

def Rm04NormRawDerivativeEquationOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => rm04NormSqInFrame (I := I) Rm04 gInv frame s x)
      (rm04NormDerivRHSInFrame (I := I) S Rm04 gInv frame rm04Dt
        (t : Real) x)
      D.carrier
      (t : Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Rm04NormRawDerivativeEquationOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Rm04NormRawDerivativeEquationOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Rm04NormRawDerivativeEquationOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Rm04NormRawDerivativeEquationOn

def roughLapRm04InnerInFrame
    (roughLapRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    Real -> M -> Real :=
  fun t x =>
    ∑ a : Idx, ∑ b : Idx, ∑ c : Idx, ∑ d : Idx,
      roughLapRm04 t x a b c d *
        raisedRm04CompInFrame (I := I) Rm04 gInv frame t x a b c d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.roughLapRm04InnerInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.roughLapRm04InnerInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.roughLapRm04InnerInFrame ``Submission.DifferentialGeometry.PDE.RicciFlow.roughLapRm04InnerInFrame

def nablaRm04NormSqInFrame
    (nablaRm04 : Real -> M -> Idx -> Idx -> Idx -> Idx -> Idx -> Real)
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx) :
    Real -> M -> Real :=
  fun t x =>
    ∑ a : Idx, ∑ b : Idx,
    ∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
    ∑ p : Idx, ∑ q : Idx, ∑ r : Idx, ∑ s : Idx,
      gInv t x a b *
        gInv t x i p * gInv t x j q * gInv t x k r * gInv t x l s *
          nablaRm04 t x a i j k l * nablaRm04 t x b p q r s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nablaRm04NormSqInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nablaRm04NormSqInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nablaRm04NormSqInFrame ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaRm04NormSqInFrame

def Rm04NormDerivativeSimplifiesInFrame
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (roughLapInner reaction : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
    rm04NormDerivRHSInFrame (I := I) S Rm04 gInv frame rm04Dt
        (t : Real) x =
      2 * roughLapInner (t : Real) x + reaction (t : Real) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Rm04NormDerivativeSimplifiesInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Rm04NormDerivativeSimplifiesInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Rm04NormDerivativeSimplifiesInFrame ``Submission.DifferentialGeometry.PDE.RicciFlow.Rm04NormDerivativeSimplifiesInFrame

def Rm04NormTimeDerivativeComponentsOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (rmNormSq roughLapInner reaction : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => rmNormSq s x)
      (2 * roughLapInner (t : Real) x + reaction (t : Real) x)
      D.carrier
      (t : Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Rm04NormTimeDerivativeComponentsOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Rm04NormTimeDerivativeComponentsOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Rm04NormTimeDerivativeComponentsOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Rm04NormTimeDerivativeComponentsOn

omit [SigmaCompactSpace M] [T2Space M] in
theorem rm04NormTimeDerivativeComponentsOn_of_rawDerivative
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (roughLapInner reaction : Real -> M -> Real)
    (h_raw : Rm04NormRawDerivativeEquationOn
      (I := I) S Rm04 gInv frame rm04Dt)
    (h_simplify : Rm04NormDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame rm04Dt roughLapInner reaction) :
    Rm04NormTimeDerivativeComponentsOn
      (D := D) (rm04NormSqInFrame (I := I) Rm04 gInv frame)
      roughLapInner reaction := by
  intro t x
  simpa [h_simplify t x] using h_raw t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rm04NormTimeDerivativeComponentsOn_of_rawDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rm04NormTimeDerivativeComponentsOn_of_rawDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rm04NormTimeDerivativeComponentsOn_of_rawDerivative ``Submission.DifferentialGeometry.PDE.RicciFlow.rm04NormTimeDerivativeComponentsOn_of_rawDerivative

def Rm04NormLaplacianComponentsOn
    (rmNormLap roughLapInner nablaRmNormSq : Real -> M -> Real) : Prop :=
  ∀ (t : Real) (x : M),
    rmNormLap t x = 2 * roughLapInner t x + 2 * nablaRmNormSq t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Rm04NormLaplacianComponentsOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Rm04NormLaplacianComponentsOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Rm04NormLaplacianComponentsOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Rm04NormLaplacianComponentsOn

def Rm04NormHeatEquationOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (rmNormSq rmNormLap nablaRmNormSq reaction : Real -> M -> Real) : Prop :=
  ∀ (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D) (x : M),
    HasDerivWithinAt
      (fun s : Real => rmNormSq s x)
      (rmNormLap (t : Real) x +
        (-2 * nablaRmNormSq (t : Real) x + reaction (t : Real) x))
      D.carrier
      (t : Real)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Rm04NormHeatEquationOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Rm04NormHeatEquationOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Rm04NormHeatEquationOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Rm04NormHeatEquationOn

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem rm04NormHeatEquationOn_of_components
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (rmNormSq rmNormLap roughLapInner nablaRmNormSq reaction : Real -> M -> Real)
    (h_dt : Rm04NormTimeDerivativeComponentsOn
      (D := D) rmNormSq roughLapInner reaction)
    (h_lap : Rm04NormLaplacianComponentsOn
      rmNormLap roughLapInner nablaRmNormSq) :
    Rm04NormHeatEquationOn
      (D := D) rmNormSq rmNormLap nablaRmNormSq reaction := by
  intro t x
  have hvalue :
      rmNormLap (t : Real) x +
          (-2 * nablaRmNormSq (t : Real) x + reaction (t : Real) x) =
        2 * roughLapInner (t : Real) x + reaction (t : Real) x := by
    rw [h_lap (t : Real) x]
    ring
  rw [hvalue]
  exact h_dt t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rm04NormHeatEquationOn_of_components then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rm04NormHeatEquationOn_of_components"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rm04NormHeatEquationOn_of_components ``Submission.DifferentialGeometry.PDE.RicciFlow.rm04NormHeatEquationOn_of_components

omit [SigmaCompactSpace M] [T2Space M] in
theorem rm04NormHeatEquationOn_of_rawDerivative
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (Rm04 : Real -> DifferentialGeometry.Geometry.Curvature.Tensor04Section (I := I) (M := M))
    (gInv : Real -> DifferentialGeometry.Geometry.Curvature.InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (rm04Dt : Real -> M -> Idx -> Idx -> Idx -> Idx -> Real)
    (rmNormLap roughLapInner nablaRmNormSq reaction : Real -> M -> Real)
    (h_raw : Rm04NormRawDerivativeEquationOn
      (I := I) S Rm04 gInv frame rm04Dt)
    (h_simplify : Rm04NormDerivativeSimplifiesInFrame
      (I := I) S Rm04 gInv frame rm04Dt roughLapInner reaction)
    (h_lap : Rm04NormLaplacianComponentsOn
      rmNormLap roughLapInner nablaRmNormSq) :
    Rm04NormHeatEquationOn
      (D := D) (rm04NormSqInFrame (I := I) Rm04 gInv frame)
      rmNormLap nablaRmNormSq reaction := by
  exact
    rm04NormHeatEquationOn_of_components
      (D := D)
      (rm04NormSqInFrame (I := I) Rm04 gInv frame)
      rmNormLap roughLapInner nablaRmNormSq reaction
      (rm04NormTimeDerivativeComponentsOn_of_rawDerivative
        (I := I) S Rm04 gInv frame rm04Dt roughLapInner reaction
        h_raw h_simplify)
      h_lap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.rm04NormHeatEquationOn_of_rawDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.rm04NormHeatEquationOn_of_rawDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.rm04NormHeatEquationOn_of_rawDerivative ``Submission.DifferentialGeometry.PDE.RicciFlow.rm04NormHeatEquationOn_of_rawDerivative

end Components

end DifferentialGeometry.PDE.RicciFlow
