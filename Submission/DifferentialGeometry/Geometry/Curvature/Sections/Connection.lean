import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.Tensor
import Submission.DifferentialGeometry.Geometry.Curvature.Sections.Trace
import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Field
import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Pointwise
import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections

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

abbrev SmoothTangentSection :=
  ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.SmoothTangentSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.SmoothTangentSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.SmoothTangentSection ``Submission.DifferentialGeometry.Geometry.Curvature.SmoothTangentSection

def rm13RealizesConnection
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M)) : Prop :=
  forall (X Y Z : SmoothTangentSection (I := I) (M := M)) (x : M)
    (alpha : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x),
      Rm13 x alpha (vec3 (X x) (Y x) (Z x)) =
        cotangentToDual (I := I) alpha
          ((connectionRiemannCurvatureField (I := I) cov
            (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p)) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rm13RealizesConnection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rm13RealizesConnection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rm13RealizesConnection ``Submission.DifferentialGeometry.Geometry.Curvature.rm13RealizesConnection

def rm04RealizesConnection
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm04 : Tensor04Section (I := I) (M := M)) : Prop :=
  forall (X Y Z W : SmoothTangentSection (I := I) (M := M)) (x : M),
    Rm04 x (vec4 (X x) (Y x) (Z x) (W x)) =
      g.inner x (W x) ((connectionRiemannCurvatureField (I := I) cov
        (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p)) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rm04RealizesConnection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rm04RealizesConnection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rm04RealizesConnection ``Submission.DifferentialGeometry.Geometry.Curvature.rm04RealizesConnection


theorem rm04_eq_of_realizes [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {A B : Tensor04Section (I := I) (M := M)}
    (hA : rm04RealizesConnection (I := I) g cov A)
    (hB : rm04RealizesConnection (I := I) g cov B)
    (x : M) :
    A x = B x := by
  classical
  apply tensor0SSpace_ext 4 x
  intro v
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (v 0)
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (v 1)
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (v 2)
  obtain ⟨W, hW⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (v 3)
  have hv : v = vec4 (I := I) (X x) (Y x) (Z x) (W x) := by
    funext i
    fin_cases i <;> simp_all [vec4]
  rw [hv, hA X Y Z W x, hB X Y Z W x]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rm04_eq_of_realizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rm04_eq_of_realizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rm04_eq_of_realizes ``Submission.DifferentialGeometry.Geometry.Curvature.rm04_eq_of_realizes


def ricciTensorRealizesRm13Trace
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M)) : Prop :=
  forall x : M, Ric x = ricciFromRm13At (I := I) (M := M) (Rm13 x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciTensorRealizesRm13Trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciTensorRealizesRm13Trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciTensorRealizesRm13Trace ``Submission.DifferentialGeometry.Geometry.Curvature.ricciTensorRealizesRm13Trace


def ricciTensorRealizesRm04TraceInFrame
    {Idx : Type*} [Fintype Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  DifferentialGeometry.Geometry.Curvature.ricciRealizesRm04TraceInFrame (I := I)
    (tensor02ToField (I := I) Ric) (tensor04ToField (I := I) Rm04) gInv frame

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciTensorRealizesRm04TraceInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciTensorRealizesRm04TraceInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciTensorRealizesRm04TraceInFrame ``Submission.DifferentialGeometry.Geometry.Curvature.ricciTensorRealizesRm04TraceInFrame


def scalarSectionRealizesRicciTraceInFrame
    {Idx : Type*} [Fintype Idx]
    (scalar : M -> Real)
    (Ric : Tensor02Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x) : Prop :=
  DifferentialGeometry.Geometry.Curvature.scalarRealizesRicciTraceInFrame (I := I)
    scalar (tensor02ToField (I := I) Ric) gInv frame

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.scalarSectionRealizesRicciTraceInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.scalarSectionRealizesRicciTraceInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.scalarSectionRealizesRicciTraceInFrame ``Submission.DifferentialGeometry.Geometry.Curvature.scalarSectionRealizesRicciTraceInFrame


theorem rm04_comp_eq_connection
    {Idx : Type*}
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hRm : rm04RealizesConnection (I := I) g cov Rm04)
    (x : M) (a b c d : Idx) :
    rm04Comp (I := I) Rm04 (fun i y => frame i y) x a b c d =
      g.inner x (frame d x) ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame a y) (fun y => frame b y) (fun y => frame c y)) x) := by
  simpa [rm04Comp] using
    hRm (frame a) (frame b) (frame c) (frame d) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rm04_comp_eq_connection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rm04_comp_eq_connection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rm04_comp_eq_connection ``Submission.DifferentialGeometry.Geometry.Curvature.rm04_comp_eq_connection

theorem ricciComp_eq_trace
    {Idx : Type*} [Fintype Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm04 : Tensor04Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic : ricciTensorRealizesRm04TraceInFrame (I := I) Ric Rm04 gInv frame)
    (x : M) (i j : Idx) :
    ricciComp (I := I) Ric frame x i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l * rm04Comp (I := I) Rm04 frame x k i j l := by
  simpa [ricciTensorRealizesRm04TraceInFrame, tensor02ToField, tensor04ToField,
    ricciComp, rm04Comp] using
    DifferentialGeometry.Geometry.Curvature.ricci_comp_eq_trace (I := I)
      (tensor02ToField (I := I) Ric) (tensor04ToField (I := I) Rm04) gInv frame hRic x i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciComp_eq_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciComp_eq_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciComp_eq_trace ``Submission.DifferentialGeometry.Geometry.Curvature.ricciComp_eq_trace

theorem scalarSection_eq_trace
    {Idx : Type*} [Fintype Idx]
    (scalar : M -> Real)
    (Ric : Tensor02Section (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hScalar : scalarSectionRealizesRicciTraceInFrame (I := I) scalar Ric gInv frame)
    (x : M) :
    scalar x =
      ∑ i : Idx, ∑ j : Idx,
        gInv x i j * ricciComp (I := I) Ric frame x i j := by
  simpa [scalarSectionRealizesRicciTraceInFrame, tensor02ToField, ricciComp] using
    DifferentialGeometry.Geometry.Curvature.scalar_eq_trace (I := I)
      scalar (tensor02ToField (I := I) Ric) gInv frame hScalar x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.scalarSection_eq_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.scalarSection_eq_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.scalarSection_eq_trace ``Submission.DifferentialGeometry.Geometry.Curvature.scalarSection_eq_trace

theorem rm13_comp_eq_connection
    {Idx : Type*} {u : Set M}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (Rm13 : Tensor13Section (I := I) (M := M))
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hframe : IsLocalFrameOn I E ∞ (fun i y => frame i y) u)
    (hRm : rm13RealizesConnection (I := I) cov Rm13)
    (x : M) (a b c d : Idx) :
    rm13Comp (I := I) Rm13 (fun i y => frame i y) hframe x a b c d =
      hframe.coeff a x ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame b y) (fun y => frame c y) (fun y => frame d y)) x) := by
  simpa [rm13Comp] using
    hRm (frame b) (frame c) (frame d) x (dualToCotangent (hframe.coeff a x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rm13_comp_eq_connection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rm13_comp_eq_connection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rm13_comp_eq_connection ``Submission.DifferentialGeometry.Geometry.Curvature.rm13_comp_eq_connection

namespace CurvatureSections

theorem rm13_comp_eq_connection
    {Idx : Type*} {u : Set M}
    (K : CurvatureSections (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hframe : IsLocalFrameOn I E ∞ (fun i y => frame i y) u)
    (hRm : rm13RealizesConnection (I := I) cov K.rm13)
    (x : M) (a b c d : Idx) :
    rm13Comp (I := I) K.rm13 (fun i y => frame i y) hframe x a b c d =
      hframe.coeff a x ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame b y) (fun y => frame c y) (fun y => frame d y)) x) :=
  DifferentialGeometry.Geometry.Curvature.rm13_comp_eq_connection (I := I) cov K.rm13 frame hframe
    hRm x a b c d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.CurvatureSections.rm13_comp_eq_connection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.CurvatureSections.rm13_comp_eq_connection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.CurvatureSections.rm13_comp_eq_connection ``Submission.DifferentialGeometry.Geometry.Curvature.CurvatureSections.rm13_comp_eq_connection

theorem rm04_comp_eq_connection
    {Idx : Type*}
    (K : CurvatureSections (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hRm : rm04RealizesConnection (I := I) g cov K.rm04)
    (x : M) (a b c d : Idx) :
    rm04Comp (I := I) K.rm04 (fun i y => frame i y) x a b c d =
      g.inner x (frame d x) ((connectionRiemannCurvatureField (I := I) cov
        (fun y => frame a y) (fun y => frame b y) (fun y => frame c y)) x) :=
  DifferentialGeometry.Geometry.Curvature.rm04_comp_eq_connection (I := I) g cov K.rm04 frame hRm x
    a b c d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.CurvatureSections.rm04_comp_eq_connection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.CurvatureSections.rm04_comp_eq_connection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.CurvatureSections.rm04_comp_eq_connection ``Submission.DifferentialGeometry.Geometry.Curvature.CurvatureSections.rm04_comp_eq_connection

theorem ricci_comp_eq_trace
    {Idx : Type*} [Fintype Idx]
    (K : CurvatureSections (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hRic : ricciTensorRealizesRm04TraceInFrame (I := I) K.ricci K.rm04 gInv frame)
    (x : M) (i j : Idx) :
    ricciComp (I := I) K.ricci frame x i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l * rm04Comp (I := I) K.rm04 frame x k i j l :=
  DifferentialGeometry.Geometry.Curvature.ricciComp_eq_trace (I := I) K.ricci K.rm04 gInv frame
    hRic x i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.CurvatureSections.ricci_comp_eq_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.CurvatureSections.ricci_comp_eq_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.CurvatureSections.ricci_comp_eq_trace ``Submission.DifferentialGeometry.Geometry.Curvature.CurvatureSections.ricci_comp_eq_trace

theorem ricci_comp_eq_connection_trace
    {Idx : Type*} [Fintype Idx]
    (K : CurvatureSections (I := I) (M := M))
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> SmoothTangentSection (I := I) (M := M))
    (hRm : rm04RealizesConnection (I := I) g cov K.rm04)
    (hRic : ricciTensorRealizesRm04TraceInFrame (I := I) K.ricci K.rm04 gInv
      (fun i y => frame i y))
    (x : M) (i j : Idx) :
    ricciComp (I := I) K.ricci (fun i y => frame i y) x i j =
      ∑ k : Idx, ∑ l : Idx,
        gInv x k l *
          g.inner x (frame l x) ((connectionRiemannCurvatureField (I := I) cov
            (fun y => frame k y) (fun y => frame i y) (fun y => frame j y)) x) := by
  rw [CurvatureSections.ricci_comp_eq_trace (I := I) K gInv
    (fun i y => frame i y) hRic x i j]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [DifferentialGeometry.Geometry.Curvature.rm04_comp_eq_connection (I := I) g cov K.rm04 frame
    hRm x k i j l]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.CurvatureSections.ricci_comp_eq_connection_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.CurvatureSections.ricci_comp_eq_connection_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.CurvatureSections.ricci_comp_eq_connection_trace ``Submission.DifferentialGeometry.Geometry.Curvature.CurvatureSections.ricci_comp_eq_connection_trace

theorem scalar_eq_trace
    {Idx : Type*} [Fintype Idx]
    (K : CurvatureSections (I := I) (M := M))
    (gInv : InverseMetricComponents M Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hScalar : scalarSectionRealizesRicciTraceInFrame (I := I) K.scalar K.ricci gInv frame)
    (x : M) :
    K.scalar x =
      ∑ i : Idx, ∑ j : Idx,
        gInv x i j * ricciComp (I := I) K.ricci frame x i j :=
  DifferentialGeometry.Geometry.Curvature.scalarSection_eq_trace (I := I) K.scalar K.ricci gInv
    frame hScalar x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.CurvatureSections.scalar_eq_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.CurvatureSections.scalar_eq_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.CurvatureSections.scalar_eq_trace ``Submission.DifferentialGeometry.Geometry.Curvature.CurvatureSections.scalar_eq_trace

end CurvatureSections

section Producers

variable [T2Space M]

structure ConnectionCurvatureSections
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) where
  rm13 : Tensor13Section (I := I) (M := M)
  rm04 : Tensor04Section (I := I) (M := M)
  ricci : Tensor02Section (I := I) (M := M)
  rm13Realizes : rm13RealizesConnection (I := I) cov rm13
  rm04Realizes : rm04RealizesConnection (I := I) g cov rm04
  ricciRealizes : ricciTensorRealizesRm13Trace (I := I) ricci rm13

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ConnectionCurvatureSections then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ConnectionCurvatureSections"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ConnectionCurvatureSections ``Submission.DifferentialGeometry.Geometry.Curvature.ConnectionCurvatureSections

theorem rm13Section_realizes
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) :
    rm13RealizesConnection (I := I) cov
      (DifferentialGeometry.Geometry.Curvature.CovariantDerivative.rm13Section (I := I) (M := M)
        cov hcov) := by
  intro X Y Z x alpha
  exact
    DifferentialGeometry.Geometry.Curvature.CovariantDerivative.rm13Section_apply_smooth
      (I := I) (M := M) cov hcov X Y Z alpha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rm13Section_realizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rm13Section_realizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rm13Section_realizes ``Submission.DifferentialGeometry.Geometry.Curvature.rm13Section_realizes

theorem rm04Section_realizes
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) :
    rm04RealizesConnection (I := I) g cov
      (DifferentialGeometry.Geometry.Curvature.CovariantDerivative.rm04Section (I := I) g cov
        hcov) := by
  intro X Y Z W x
  exact
    DifferentialGeometry.Geometry.Curvature.CovariantDerivative.rm04Section_apply_smooth
      (I := I) (M := M) g cov hcov X Y Z W x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rm04Section_realizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rm04Section_realizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rm04Section_realizes ``Submission.DifferentialGeometry.Geometry.Curvature.rm04Section_realizes

end Producers

end DifferentialGeometry.Geometry.Curvature
