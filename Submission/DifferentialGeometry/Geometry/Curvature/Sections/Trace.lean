import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.RawFields
import Submission.DifferentialGeometry.Tensor.RSTensor.Field

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


section MetricTrace

variable {Idx : Type*} [Fintype Idx]


def ricciRealizesRm04TraceInFrame
    (Ric : RawTwoTensorField (I := I) (M := M))
    (Riemann04 : RawFourTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall x X Y, Ric x X Y =
    ricciFromRiemann04TraceInFrame (I := I) Riemann04 gInv frame x X Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciRealizesRm04TraceInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciRealizesRm04TraceInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciRealizesRm04TraceInFrame ``Submission.DifferentialGeometry.Geometry.Curvature.ricciRealizesRm04TraceInFrame

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem ricci_comp_eq_trace
    (Ric : RawTwoTensorField (I := I) (M := M))
    (Riemann04 : RawFourTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic : ricciRealizesRm04TraceInFrame (I := I) Ric Riemann04 gInv frame)
    (x : M) (i j : Idx) :
    Ric x (frame i x) (frame j x) =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l * Riemann04 x (frame k x) (frame i x) (frame j x)
          (frame l x) := by
  simpa [ricciFromRiemann04TraceInFrame] using hRic x (frame i x) (frame j x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricci_comp_eq_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricci_comp_eq_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricci_comp_eq_trace ``Submission.DifferentialGeometry.Geometry.Curvature.ricci_comp_eq_trace

abbrev scalarCurvatureFromRicciTraceInFrame
    (Ric : RawTwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : M -> Real :=
  scalarFromRicciTraceInFrame (I := I) Ric gInv frame

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.scalarCurvatureFromRicciTraceInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.scalarCurvatureFromRicciTraceInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.scalarCurvatureFromRicciTraceInFrame ``Submission.DifferentialGeometry.Geometry.Curvature.scalarCurvatureFromRicciTraceInFrame

omit [FiniteDimensional ℝ E] in
omit [IsManifold I ∞ M] in
@[simp]
theorem scalarCurvatureFromRicciTraceInFrame_apply
    (Ric : RawTwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) (x : M) :
    scalarCurvatureFromRicciTraceInFrame (I := I) Ric gInv frame x =
      ∑ i : Idx, ∑ j : Idx, gInv x i j * Ric x (frame i x) (frame j x) := by
  exact scalarFromRicciTraceInFrame_apply (I := I) Ric gInv frame x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.scalarCurvatureFromRicciTraceInFrame_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.scalarCurvatureFromRicciTraceInFrame_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.scalarCurvatureFromRicciTraceInFrame_apply ``Submission.DifferentialGeometry.Geometry.Curvature.scalarCurvatureFromRicciTraceInFrame_apply


def scalarRealizesRicciTraceInFrame
    (scalar : M -> Real)
    (Ric : RawTwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall x, scalar x = scalarFromRicciTraceInFrame (I := I) Ric gInv frame x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.scalarRealizesRicciTraceInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.scalarRealizesRicciTraceInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.scalarRealizesRicciTraceInFrame ``Submission.DifferentialGeometry.Geometry.Curvature.scalarRealizesRicciTraceInFrame

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem scalar_eq_trace
    (scalar : M -> Real)
    (Ric : RawTwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hScalar : scalarRealizesRicciTraceInFrame (I := I) scalar Ric gInv frame)
    (x : M) :
    scalar x =
      ∑ i : Idx, ∑ j : Idx, gInv x i j * Ric x (frame i x) (frame j x) := by
  simpa [scalarFromRicciTraceInFrame] using hScalar x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.scalar_eq_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.scalar_eq_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.scalar_eq_trace ``Submission.DifferentialGeometry.Geometry.Curvature.scalar_eq_trace


omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem scalarCurvatureFromRicciTraceInFrame_realizes
    (Ric : RawTwoTensorField (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) :
    scalarRealizesRicciTraceInFrame (I := I)
      (scalarCurvatureFromRicciTraceInFrame (I := I) Ric gInv frame)
      Ric gInv frame := by
  intro x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.scalarCurvatureFromRicciTraceInFrame_realizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.scalarCurvatureFromRicciTraceInFrame_realizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.scalarCurvatureFromRicciTraceInFrame_realizes ``Submission.DifferentialGeometry.Geometry.Curvature.scalarCurvatureFromRicciTraceInFrame_realizes

end MetricTrace

end DifferentialGeometry.Geometry.Curvature
