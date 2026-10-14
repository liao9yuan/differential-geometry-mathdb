import Submission.DifferentialGeometry.Geometry.Metric.Comparison.BallMonotonicity
import Submission.DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev RawTangentField :=
  (x : M) -> TangentSpace I x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RawTangentField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RawTangentField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RawTangentField ``Submission.DifferentialGeometry.Geometry.Curvature.RawTangentField

abbrev RawTwoTensorField :=
  (x : M) -> TangentSpace I x -> TangentSpace I x -> Real

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RawTwoTensorField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RawTwoTensorField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RawTwoTensorField ``Submission.DifferentialGeometry.Geometry.Curvature.RawTwoTensorField

abbrev RawFourTensorField :=
  (x : M) -> TangentSpace I x -> TangentSpace I x -> TangentSpace I x ->
    TangentSpace I x -> Real

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RawFourTensorField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RawFourTensorField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RawFourTensorField ``Submission.DifferentialGeometry.Geometry.Curvature.RawFourTensorField


abbrev InverseMetricComponents (M : Type*) (Idx : Type*) :=
  M -> Idx -> Idx -> Real

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.InverseMetricComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.InverseMetricComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.InverseMetricComponents ``Submission.DifferentialGeometry.Geometry.Curvature.InverseMetricComponents

def connectionRiemannCurvatureField
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : RawTangentField (I := I) (M := M)) :
    RawTangentField (I := I) (M := M) :=
  fun x =>
    (cov (fun y => (cov Z y) (Y y)) x) (X x) -
      (cov (fun y => (cov Z y) (X y)) x) (Y x) -
        (cov Z x) (VectorField.mlieBracket I X Y x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.connectionRiemannCurvatureField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.connectionRiemannCurvatureField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.connectionRiemannCurvatureField ``Submission.DifferentialGeometry.Geometry.Curvature.connectionRiemannCurvatureField


theorem connectionRiemannCurvatureField_swap
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : RawTangentField (I := I) (M := M)) (x : M) :
    connectionRiemannCurvatureField (I := I) cov Y X Z x =
      -connectionRiemannCurvatureField (I := I) cov X Y Z x := by
  unfold connectionRiemannCurvatureField
  rw [VectorField.mlieBracket_swap_apply (I := I) (V := Y) (W := X) (x := x)]
  simp [map_neg, sub_eq_add_neg]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.connectionRiemannCurvatureField_swap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.connectionRiemannCurvatureField_swap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.connectionRiemannCurvatureField_swap ``Submission.DifferentialGeometry.Geometry.Curvature.connectionRiemannCurvatureField_swap

section MetricTrace

variable {Idx : Type*} [Fintype Idx]

def InverseMetricComponentsInFrame [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall x i j,
    (∑ k : Idx, gInv x i k * g.inner x (frame k x) (frame j x)) =
        (if i = j then 1 else 0) ∧
      (∑ k : Idx, g.inner x (frame i x) (frame k x) * gInv x k j) =
        (if i = j then 1 else 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.InverseMetricComponentsInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.InverseMetricComponentsInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.InverseMetricComponentsInFrame ``Submission.DifferentialGeometry.Geometry.Curvature.InverseMetricComponentsInFrame


theorem invComp_symm [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hinv : InverseMetricComponentsInFrame (I := I) g gInv frame) :
    forall x i j, gInv x i j = gInv x j i := by
  classical
  intro x i j
  let A : Matrix Idx Idx Real := fun i j => gInv x i j
  let G : Matrix Idx Idx Real := fun i j => g.inner x (frame i x) (frame j x)
  have hAG : A * G = 1 := by
    ext a b
    simpa [A, G, Matrix.mul_apply] using! (hinv x a b).1
  have hGA : G * A = 1 := by
    ext a b
    simpa [A, G, Matrix.mul_apply] using! (hinv x a b).2
  have hGt : Matrix.transpose G = G := by
    ext a b
    simpa [G] using! g.symm x (frame b x) (frame a x)
  have hAtG : Matrix.transpose A * G = 1 := by
    calc
      Matrix.transpose A * G = Matrix.transpose A * Matrix.transpose G := by rw [hGt]
      _ = Matrix.transpose (G * A) := by rw [Matrix.transpose_mul]
      _ = 1 := by rw [hGA]; simp
  have hAt : Matrix.transpose A = A := by
    calc
      Matrix.transpose A = Matrix.transpose A * 1 := by simp
      _ = Matrix.transpose A * (G * A) := by rw [hGA]
      _ = (Matrix.transpose A * G) * A := by rw [← Matrix.mul_assoc]
      _ = 1 * A := by rw [hAtG]
      _ = A := by simp
  have hentry := congrArg (fun B : Matrix Idx Idx Real => B j i) hAt
  simpa [A] using! hentry

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.invComp_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.invComp_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.invComp_symm ``Submission.DifferentialGeometry.Geometry.Curvature.invComp_symm

def ricciFromRiemann04TraceInFrame
    (Riemann04 : RawFourTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    RawTwoTensorField (I := I) (M := M) :=
  fun x X Y =>
    ∑ k : Idx, ∑ l : Idx, gInv x k l * Riemann04 x (frame k x) X Y (frame l x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciFromRiemann04TraceInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciFromRiemann04TraceInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciFromRiemann04TraceInFrame ``Submission.DifferentialGeometry.Geometry.Curvature.ricciFromRiemann04TraceInFrame

omit [IsManifold I ∞ M] in
@[simp]
theorem ricciFromRiemann04TraceInFrame_apply
    (Riemann04 : RawFourTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (X Y : TangentSpace I x) :
    ricciFromRiemann04TraceInFrame (I := I) Riemann04 gInv frame x X Y =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l * Riemann04 x (frame k x) X Y (frame l x) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciFromRiemann04TraceInFrame_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciFromRiemann04TraceInFrame_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciFromRiemann04TraceInFrame_apply ``Submission.DifferentialGeometry.Geometry.Curvature.ricciFromRiemann04TraceInFrame_apply


def scalarFromRicciTraceInFrame
    (Ric : RawTwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : M -> Real :=
  fun x => ∑ i : Idx, ∑ j : Idx, gInv x i j * Ric x (frame i x) (frame j x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.scalarFromRicciTraceInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.scalarFromRicciTraceInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.scalarFromRicciTraceInFrame ``Submission.DifferentialGeometry.Geometry.Curvature.scalarFromRicciTraceInFrame

omit [IsManifold I ∞ M] in
@[simp]
theorem scalarFromRicciTraceInFrame_apply
    (Ric : RawTwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) (x : M) :
    scalarFromRicciTraceInFrame (I := I) Ric gInv frame x =
      ∑ i : Idx, ∑ j : Idx, gInv x i j * Ric x (frame i x) (frame j x) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.scalarFromRicciTraceInFrame_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.scalarFromRicciTraceInFrame_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.scalarFromRicciTraceInFrame_apply ``Submission.DifferentialGeometry.Geometry.Curvature.scalarFromRicciTraceInFrame_apply

end MetricTrace

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Integral.Connection

abbrev InverseMetricComponents :=
  DifferentialGeometry.Geometry.Curvature.InverseMetricComponents

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Connection.InverseMetricComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Connection.InverseMetricComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Connection.InverseMetricComponents ``Submission.DifferentialGeometry.Integral.Connection.InverseMetricComponents

end DifferentialGeometry.Integral.Connection
