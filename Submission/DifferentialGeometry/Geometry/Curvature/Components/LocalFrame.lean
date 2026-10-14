import Submission.DifferentialGeometry.Geometry.Curvature.Components.RicciTrace

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
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}

section LocalFrame

variable {u : Set M}

omit [Fintype Idx] [DecidableEq Idx] in
theorem ricciCompAt_eq_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i j =
      ricciComp (I := I) Ric frame x i j := by
  unfold ricciCompAt ricciComp component0S slots2 vec2
  congr 1
  funext a
  fin_cases a <;> simp [IsLocalFrameOn.toBasisAt_coe]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciCompAt_eq_frame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciCompAt_eq_frame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciCompAt_eq_frame ``Submission.DifferentialGeometry.Geometry.Curvature.ricciCompAt_eq_frame

omit [Fintype Idx] [DecidableEq Idx] in
theorem rm04CompAt_eq_frame
    (Rm04 : Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    {x : M} (hx : x ∈ u) (i j k l : Idx) :
    rm04CompAt (I := I) (hframe.toBasisAt hx) (Rm04 x) i j k l =
      rm04Comp (I := I) Rm04 frame x i j k l := by
  unfold rm04CompAt rm04Comp component0S slots4 vec4
  congr 1
  funext a
  fin_cases a <;> simp [IsLocalFrameOn.toBasisAt_coe]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rm04CompAt_eq_frame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rm04CompAt_eq_frame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rm04CompAt_eq_frame ``Submission.DifferentialGeometry.Geometry.Curvature.rm04CompAt_eq_frame

omit [DecidableEq Idx] in
theorem ricciTraceAt_of_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hRic : ricciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInv frame)
    {x : M} (hx : x ∈ u) :
    RicciRealizesRm04TraceAt (I := I) (Ric x) (Rm04 x) (gInv x)
      (hframe.toBasisAt hx) := by
  intro X Y
  simpa [ricciTensorRealizesRm04TraceInFrame, tensor02ToField, tensor04ToField,
    IsLocalFrameOn.toBasisAt_coe] using hRic x X Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciTraceAt_of_frame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciTraceAt_of_frame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciTraceAt_of_frame ``Submission.DifferentialGeometry.Geometry.Curvature.ricciTraceAt_of_frame

def RicciTensorRealizesRm04FirstTraceInFrame
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  forall x i j,
    Ric x (vec2 (frame i x) (frame j x)) =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l * Rm04 x (vec4 (frame k x) (frame i x) (frame j x) (frame l x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.RicciTensorRealizesRm04FirstTraceInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.RicciTensorRealizesRm04FirstTraceInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.RicciTensorRealizesRm04FirstTraceInFrame ``Submission.DifferentialGeometry.Geometry.Curvature.RicciTensorRealizesRm04FirstTraceInFrame

omit [DecidableEq Idx] in
theorem ricciFirstTraceAt_of_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hRic : RicciTensorRealizesRm04FirstTraceInFrame (I := I) Ric Rm04 gInv frame)
    {x : M} (hx : x ∈ u) :
    RicciRealizesRm04FirstTraceAt (I := I) (Ric x) (Rm04 x) (gInv x)
      (hframe.toBasisAt hx) := by
  intro i j
  simpa [RicciTensorRealizesRm04FirstTraceInFrame, IsLocalFrameOn.toBasisAt_coe]
    using hRic x i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciFirstTraceAt_of_frame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciFirstTraceAt_of_frame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciFirstTraceAt_of_frame ``Submission.DifferentialGeometry.Geometry.Curvature.ricciFirstTraceAt_of_frame


omit [DecidableEq Idx] in
theorem ricciComp_eq_firstTrace_rm04_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hRic : RicciTensorRealizesRm04FirstTraceInFrame (I := I) Ric Rm04 gInv frame)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l *
          rm04CompAt (I := I) (hframe.toBasisAt hx) (Rm04 x) k i j l := by
  have hAt := ricciFirstTraceAt_of_frame
    (I := I) Ric Rm04 gInv frame hframe hRic hx
  rw [ricciCompAt_apply]
  simp_rw [rm04CompAt_apply]
  exact hAt i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciComp_eq_firstTrace_rm04_frame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciComp_eq_firstTrace_rm04_frame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciComp_eq_firstTrace_rm04_frame ``Submission.DifferentialGeometry.Geometry.Curvature.ricciComp_eq_firstTrace_rm04_frame

omit [DecidableEq Idx] in
theorem scalarTraceAt_of_frame
    (scalar : M -> Real)
    (Ric : Tensor02Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hScalar : scalarSectionRealizesRicciTraceInFrame (I := I) scalar Ric gInv frame)
    {x : M} (hx : x ∈ u) :
    ScalarRealizesRicciTraceAt (I := I) (scalar x) (Ric x) (gInv x)
      (hframe.toBasisAt hx) := by
  simpa [ScalarRealizesRicciTraceAt, scalarSectionRealizesRicciTraceInFrame,
    tensor02ToField, IsLocalFrameOn.toBasisAt_coe] using hScalar x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.scalarTraceAt_of_frame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.scalarTraceAt_of_frame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.scalarTraceAt_of_frame ``Submission.DifferentialGeometry.Geometry.Curvature.scalarTraceAt_of_frame

omit [DecidableEq Idx] in
theorem ricciComp_eq_trace_rm04_frame
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hRic : ricciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInv frame)
    {x : M} (hx : x ∈ u) (i j : Idx) :
    ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l *
          rm04CompAt (I := I) (hframe.toBasisAt hx) (Rm04 x) k i j l := by
  exact ricciComp_eq_trace_rm04 (I := I) (hframe.toBasisAt hx) (Ric x) (Rm04 x)
    (gInv x) (ricciTraceAt_of_frame (I := I) Ric Rm04 gInv frame hframe hRic hx) i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciComp_eq_trace_rm04_frame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciComp_eq_trace_rm04_frame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciComp_eq_trace_rm04_frame ``Submission.DifferentialGeometry.Geometry.Curvature.ricciComp_eq_trace_rm04_frame

omit [DecidableEq Idx] in
theorem scalar_eq_trace_ricci_frame
    (scalar : M -> Real)
    (Ric : Tensor02Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (hScalar : scalarSectionRealizesRicciTraceInFrame (I := I) scalar Ric gInv frame)
    {x : M} (hx : x ∈ u) :
    scalar x =
      ∑ i : Idx, ∑ j : Idx,
        gInv x i j * ricciCompAt (I := I) (hframe.toBasisAt hx) (Ric x) i j := by
  exact scalar_eq_trace_ricci (I := I) (hframe.toBasisAt hx) (scalar x) (Ric x)
    (gInv x) (scalarTraceAt_of_frame (I := I) scalar Ric gInv frame hframe hScalar hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.scalar_eq_trace_ricci_frame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.scalar_eq_trace_ricci_frame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.scalar_eq_trace_ricci_frame ``Submission.DifferentialGeometry.Geometry.Curvature.scalar_eq_trace_ricci_frame

end LocalFrame
end DifferentialGeometry.Geometry.Curvature
