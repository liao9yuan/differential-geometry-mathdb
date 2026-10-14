import Submission.DifferentialGeometry.Analysis.Time
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Submission.DifferentialGeometry.Analysis
namespace DifferentialGeometry.Tensor.Coordinates

noncomputable section

open _root_.Bundle _root_.Module
open scoped _root_.BigOperators _root_.Manifold _root_.ContDiff

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {Idx : Type*}
  {u : Set M}

def christoffelSymbolInFrame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : Idx) : 𝕜 :=
  hframe.coeff k x ((cov (frame j) x) (frame i x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame


def christoffelAlongInFrame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (X : TangentSpace I x) (j k : Idx) : 𝕜 :=
  hframe.coeff k x ((cov (frame j) x) X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame

omit [CompleteSpace 𝕜] in
@[simp] theorem christoffelSymbolInFrame_eval
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : Idx) :
    christoffelSymbolInFrame cov frame hframe x i j k =
      hframe.coeff k x ((cov (frame j) x) (frame i x)) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame_eval ``Submission.DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame_eval

omit [CompleteSpace 𝕜] in
@[simp] theorem christoffelAlongInFrame_eval
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (X : TangentSpace I x) (j k : Idx) :
    christoffelAlongInFrame cov frame hframe x X j k =
      hframe.coeff k x ((cov (frame j) x) X) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame_eval ``Submission.DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame_eval

omit [CompleteSpace 𝕜] in
theorem christoffelAlongInFrame_frame
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : Idx) :
    christoffelAlongInFrame cov frame hframe x (frame i x) j k =
      christoffelSymbolInFrame cov frame hframe x i j k := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame_frame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame_frame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame_frame ``Submission.DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame_frame


omit [CompleteSpace 𝕜] in
theorem christoffelAlongInFrame_eq_sum_coeff
    [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (X : TangentSpace I x) (j k : Idx) :
    christoffelAlongInFrame cov frame hframe x X j k =
      ∑ i : Idx,
        hframe.coeff i x X *
          christoffelSymbolInFrame cov frame hframe x i j k := by
  classical
  have hX : X = ∑ i : Idx, hframe.coeff i x X • frame i x := by
    simpa [IsLocalFrameOn.coeff, hx, IsLocalFrameOn.toBasisAt_coe] using
      ((hframe.toBasisAt hx).sum_repr X).symm
  calc
    christoffelAlongInFrame cov frame hframe x X j k
        = hframe.coeff k x ((cov (frame j) x) X) := rfl
    _ = hframe.coeff k x
          ((cov (frame j) x)
            (∑ i : Idx, hframe.coeff i x X • frame i x)) := by
          rw [← hX]
    _ = ∑ i : Idx,
          hframe.coeff i x X *
            christoffelSymbolInFrame cov frame hframe x i j k := by
          simp [map_sum, map_smul, christoffelSymbolInFrame]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame_eq_sum_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame_eq_sum_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame_eq_sum_coeff ``Submission.DifferentialGeometry.Tensor.Coordinates.christoffelAlongInFrame_eq_sum_coeff


omit [CompleteSpace 𝕜] in
theorem covariantDerivative_eq_sum_christoffel
    [Fintype Idx]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    (cov (frame j) x) (frame i x) =
      ∑ k, christoffelSymbolInFrame cov frame hframe x i j k • frame k x := by
  exact hframe.coeff_sum_eq (fun y => (cov (frame j) y) (frame i y)) hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.covariantDerivative_eq_sum_christoffel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.covariantDerivative_eq_sum_christoffel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.covariantDerivative_eq_sum_christoffel ``Submission.DifferentialGeometry.Tensor.Coordinates.covariantDerivative_eq_sum_christoffel

theorem torsion_coeff_eq_christoffel_skew
    [FiniteDimensional 𝕜 E] [CompleteSpace E]
    [IsManifold I 2 M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (i j k : Idx)
    (hi : MDiffAt (T% (frame i)) x) (hj : MDiffAt (T% (frame j)) x) :
    hframe.coeff k x (cov.torsion x (frame i x) (frame j x)) =
      christoffelSymbolInFrame cov frame hframe x i j k -
        christoffelSymbolInFrame cov frame hframe x j i k -
          hframe.coeff k x (VectorField.mlieBracket I (frame i) (frame j) x) := by
  rw [cov.torsion_apply hi hj]
  simp [christoffelSymbolInFrame, map_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.torsion_coeff_eq_christoffel_skew then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.torsion_coeff_eq_christoffel_skew"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.torsion_coeff_eq_christoffel_skew ``Submission.DifferentialGeometry.Tensor.Coordinates.torsion_coeff_eq_christoffel_skew

def IsNormalFrameForConnectionAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) : Prop :=
  forall i j k : Idx, christoffelSymbolInFrame cov frame hframe x i j k = 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.IsNormalFrameForConnectionAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.IsNormalFrameForConnectionAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.IsNormalFrameForConnectionAt ``Submission.DifferentialGeometry.Tensor.Coordinates.IsNormalFrameForConnectionAt

section Difference

variable [FiniteDimensional 𝕜 E]
  [VectorBundle 𝕜 E (TangentSpace I : M -> Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]


def christoffelSymbolDifferenceInFrame
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (i j k : Idx) : 𝕜 :=
  hframe.coeff k x (((CovariantDerivative.difference cov cov' x) (frame j x)) (frame i x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.christoffelSymbolDifferenceInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.christoffelSymbolDifferenceInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.christoffelSymbolDifferenceInFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.christoffelSymbolDifferenceInFrame


theorem christoffelSymbolDifference_expansion
    [Fintype Idx]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    ((CovariantDerivative.difference cov cov' x) (frame j x)) (frame i x) =
      ∑ k, christoffelSymbolDifferenceInFrame cov cov' frame hframe x i j k • frame k x := by
  exact hframe.coeff_sum_eq
    (fun y => ((CovariantDerivative.difference cov cov' y) (frame j y)) (frame i y)) hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.christoffelSymbolDifference_expansion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.christoffelSymbolDifference_expansion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.christoffelSymbolDifference_expansion ``Submission.DifferentialGeometry.Tensor.Coordinates.christoffelSymbolDifference_expansion

theorem christoffelSymbolDifferenceInFrame_eq_sub
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    {x : M} (i j k : Idx)
    (hframe_j : MDiffAt (T% (frame j)) x) :
    christoffelSymbolDifferenceInFrame cov cov' frame hframe x i j k =
      christoffelSymbolInFrame cov frame hframe x i j k -
        christoffelSymbolInFrame cov' frame hframe x i j k := by
  unfold christoffelSymbolDifferenceInFrame christoffelSymbolInFrame
  change hframe.coeff k x
      (((cov.isCovariantDerivativeOnUniv.difference cov'.isCovariantDerivativeOnUniv x)
        (frame j x)) (frame i x)) =
    hframe.coeff k x ((cov (frame j) x) (frame i x)) -
      hframe.coeff k x ((cov' (frame j) x) (frame i x))
  rw [IsCovariantDerivativeOn.difference_apply
    (hcov := cov.isCovariantDerivativeOnUniv)
    (hcov' := cov'.isCovariantDerivativeOnUniv)
    (σ := frame j) (x := x) (hx := by trivial) hframe_j]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.christoffelSymbolDifferenceInFrame_eq_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.christoffelSymbolDifferenceInFrame_eq_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.christoffelSymbolDifferenceInFrame_eq_sub ``Submission.DifferentialGeometry.Tensor.Coordinates.christoffelSymbolDifferenceInFrame_eq_sub

end Difference

section TimeDerivative

variable {A Time : Type*} [CommRing A] [Algebra 𝕜 A]


def christoffelSymbolTimeDerivativeInFrame
    (td : TimeDerivativeData 𝕜 A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (t : Time) (x : M) (i j k : Idx) : 𝕜 :=
  td.dtApply (fun s => christoffelSymbolInFrame (covFam s) frame hframe x i j k) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.christoffelSymbolTimeDerivativeInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.christoffelSymbolTimeDerivativeInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.christoffelSymbolTimeDerivativeInFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.christoffelSymbolTimeDerivativeInFrame

omit [CompleteSpace 𝕜] in
@[simp] theorem christoffelSymbolTimeDerivativeInFrame_eval
    (td : TimeDerivativeData 𝕜 A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (t : Time) (x : M) (i j k : Idx) :
    christoffelSymbolTimeDerivativeInFrame td covFam frame hframe t x i j k =
      td.dtApply (fun s => christoffelSymbolInFrame (covFam s) frame hframe x i j k) t := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.christoffelSymbolTimeDerivativeInFrame_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.christoffelSymbolTimeDerivativeInFrame_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.christoffelSymbolTimeDerivativeInFrame_eval ``Submission.DifferentialGeometry.Tensor.Coordinates.christoffelSymbolTimeDerivativeInFrame_eval


def ChristoffelSymbolEvolutionEquationInFrame
    (td : TimeDerivativeData 𝕜 A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Time -> M -> Idx -> Idx -> Idx -> 𝕜) : Prop :=
  forall t x i j k,
    christoffelSymbolTimeDerivativeInFrame td covFam frame hframe t x i j k =
      rhs t x i j k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.ChristoffelSymbolEvolutionEquationInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.ChristoffelSymbolEvolutionEquationInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.ChristoffelSymbolEvolutionEquationInFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.ChristoffelSymbolEvolutionEquationInFrame

omit [CompleteSpace 𝕜] in
theorem christoffelSymbolEvolution_from_equation
    (td : TimeDerivativeData 𝕜 A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (rhs : Time -> M -> Idx -> Idx -> Idx -> 𝕜)
    (h_evolution : ChristoffelSymbolEvolutionEquationInFrame td covFam frame hframe rhs)
    (t : Time) (x : M) (i j k : Idx) :
    christoffelSymbolTimeDerivativeInFrame td covFam frame hframe t x i j k =
      rhs t x i j k :=
  h_evolution t x i j k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.christoffelSymbolEvolution_from_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.christoffelSymbolEvolution_from_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.christoffelSymbolEvolution_from_equation ``Submission.DifferentialGeometry.Tensor.Coordinates.christoffelSymbolEvolution_from_equation

def ricciFlowChristoffelEvolutionRHSInFrame
    (nablaRicLastRaised nablaRicDirectionRaised : Time -> M -> Idx -> Idx -> Idx -> 𝕜)
    (t : Time) (x : M) (i j k : Idx) : 𝕜 :=
  - nablaRicLastRaised t x i j k -
    nablaRicLastRaised t x j i k +
    nablaRicDirectionRaised t x i j k

def RicciFlowChristoffelSymbolEvolutionEquationInFrame
    (td : TimeDerivativeData 𝕜 A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRicLastRaised nablaRicDirectionRaised :
      Time -> M -> Idx -> Idx -> Idx -> 𝕜) : Prop :=
  ChristoffelSymbolEvolutionEquationInFrame td covFam frame hframe
    (ricciFlowChristoffelEvolutionRHSInFrame nablaRicLastRaised nablaRicDirectionRaised)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.RicciFlowChristoffelSymbolEvolutionEquationInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.RicciFlowChristoffelSymbolEvolutionEquationInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.RicciFlowChristoffelSymbolEvolutionEquationInFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.RicciFlowChristoffelSymbolEvolutionEquationInFrame

omit [CompleteSpace 𝕜] in
theorem ricciFlow_christoffelSymbolEvolution_from_equation
    (td : TimeDerivativeData 𝕜 A Time)
    (covFam : Time -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (nablaRicLastRaised nablaRicDirectionRaised :
      Time -> M -> Idx -> Idx -> Idx -> 𝕜)
    (h_evolution : RicciFlowChristoffelSymbolEvolutionEquationInFrame
      td covFam frame hframe nablaRicLastRaised nablaRicDirectionRaised)
    (t : Time) (x : M) (i j k : Idx) :
    christoffelSymbolTimeDerivativeInFrame td covFam frame hframe t x i j k =
      - nablaRicLastRaised t x i j k -
        nablaRicLastRaised t x j i k +
        nablaRicDirectionRaised t x i j k := by
  simpa [RicciFlowChristoffelSymbolEvolutionEquationInFrame,
    ChristoffelSymbolEvolutionEquationInFrame, ricciFlowChristoffelEvolutionRHSInFrame]
    using h_evolution t x i j k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.ricciFlow_christoffelSymbolEvolution_from_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.ricciFlow_christoffelSymbolEvolution_from_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.ricciFlow_christoffelSymbolEvolution_from_equation ``Submission.DifferentialGeometry.Tensor.Coordinates.ricciFlow_christoffelSymbolEvolution_from_equation

end TimeDerivative

end

end DifferentialGeometry.Tensor.Coordinates
