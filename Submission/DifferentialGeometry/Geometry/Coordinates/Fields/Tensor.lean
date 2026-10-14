import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.FieldComponents

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.Tensor.Coordinates

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Module
open scoped _root_.Manifold _root_.ContDiff

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {Idx : Type*}
  {n : WithTop ℕ∞}
  {u : Set M}


abbrev FrameTensor0SField (s : Nat) :=
  (x : M) -> Tensor0SBundle.Tensor0SSpace (𝕜 := 𝕜) s I x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.FrameTensor0SField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.FrameTensor0SField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.FrameTensor0SField ``Submission.DifferentialGeometry.Tensor.Coordinates.FrameTensor0SField


abbrev FrameTensorRSField (r s : Nat) :=
  (x : M) -> Tensor0SBundle.TensorRSSpace (𝕜 := 𝕜) r s I x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.FrameTensorRSField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.FrameTensorRSField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.FrameTensorRSField ``Submission.DifferentialGeometry.Tensor.Coordinates.FrameTensorRSField


def coframeInFrame
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (i : Idx) : TangentSpace I x →ₗ[𝕜] 𝕜 :=
  hframe.coeff i x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coframeInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coframeInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coframeInFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.coframeInFrame

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
@[simp] theorem coframeInFrame_apply
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (i : Idx) (v : TangentSpace I x) :
    coframeInFrame frame hframe x i v = hframe.coeff i x v := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coframeInFrame_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coframeInFrame_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coframeInFrame_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.coframeInFrame_apply


def tensor0SComponentInFrame {s : Nat}
    (T : FrameTensor0SField (I := I) (M := M) s)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M)
    (vectorSlots : Fin s -> Idx) : 𝕜 :=
  T x (fun a => frame (vectorSlots a) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tensor0SComponentInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tensor0SComponentInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tensor0SComponentInFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.tensor0SComponentInFrame

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
@[simp] theorem tensor0SComponentInFrame_eval {s : Nat}
    (T : FrameTensor0SField (I := I) (M := M) s)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M)
    (vectorSlots : Fin s -> Idx) :
    tensor0SComponentInFrame T frame x vectorSlots =
      T x (fun a => frame (vectorSlots a) x) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tensor0SComponentInFrame_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tensor0SComponentInFrame_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tensor0SComponentInFrame_eval ``Submission.DifferentialGeometry.Tensor.Coordinates.tensor0SComponentInFrame_eval

def tensor0SComponentInFrameAt {s : Nat}
    (T : FrameTensor0SField (I := I) (M := M) s)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u)
    (slots : Fin s -> Idx) : 𝕜 :=
  Tensor0SBundle.component0S (I := I) (hframe.toBasisAt hx) (T x) slots

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tensor0SComponentInFrameAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tensor0SComponentInFrameAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tensor0SComponentInFrameAt ``Submission.DifferentialGeometry.Tensor.Coordinates.tensor0SComponentInFrameAt

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
@[simp] theorem tensor0SComponentInFrameAt_eval {s : Nat}
    (T : FrameTensor0SField (I := I) (M := M) s)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u)
    (slots : Fin s -> Idx) :
    tensor0SComponentInFrameAt T frame hframe x hx slots =
      T x (fun a => hframe.toBasisAt hx (slots a)) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tensor0SComponentInFrameAt_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tensor0SComponentInFrameAt_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tensor0SComponentInFrameAt_eval ``Submission.DifferentialGeometry.Tensor.Coordinates.tensor0SComponentInFrameAt_eval


def tensorRSComponentFromCovariantInputInFrame {r s : Nat}
    (T : FrameTensorRSField (I := I) (M := M) r s)
    (input : (x : M) -> Tensor0SBundle.Tensor0SSpace (𝕜 := 𝕜) r I x)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M)
    (vectorSlots : Fin s -> Idx) : 𝕜 :=
  (T x (input x)) (fun a => frame (vectorSlots a) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tensorRSComponentFromCovariantInputInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tensorRSComponentFromCovariantInputInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tensorRSComponentFromCovariantInputInFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.tensorRSComponentFromCovariantInputInFrame

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
@[simp] theorem tensorRSComponentFromCovariantInputInFrame_eval {r s : Nat}
    (T : FrameTensorRSField (I := I) (M := M) r s)
    (input : (x : M) -> Tensor0SBundle.Tensor0SSpace (𝕜 := 𝕜) r I x)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M)
    (vectorSlots : Fin s -> Idx) :
    tensorRSComponentFromCovariantInputInFrame T input frame x vectorSlots =
      (T x (input x)) (fun a => frame (vectorSlots a) x) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tensorRSComponentFromCovariantInputInFrame_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tensorRSComponentFromCovariantInputInFrame_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tensorRSComponentFromCovariantInputInFrame_eval ``Submission.DifferentialGeometry.Tensor.Coordinates.tensorRSComponentFromCovariantInputInFrame_eval

noncomputable def tensorRSComponentInFrame {r s : Nat} [Finite Idx]
    (T : FrameTensorRSField (I := I) (M := M) r s)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) : 𝕜 := by
  letI := Fintype.ofFinite Idx
  classical
  exact Tensor0SBundle.componentRSField (I := I) (hframe.toBasisAt hx) (T x) upper lower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tensorRSComponentInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tensorRSComponentInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tensorRSComponentInFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.tensorRSComponentInFrame

@[simp] theorem tensorRSComponentInFrame_eval {r s : Nat} [Fintype Idx]
    (T : FrameTensorRSField (I := I) (M := M) r s)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) :
    tensorRSComponentInFrame T frame hframe x hx upper lower =
      Tensor0SBundle.componentRSField (I := I) (hframe.toBasisAt hx) (T x) upper lower := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tensorRSComponentInFrame_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tensorRSComponentInFrame_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tensorRSComponentInFrame_eval ``Submission.DifferentialGeometry.Tensor.Coordinates.tensorRSComponentInFrame_eval

theorem tensorRSComponentInFrame_apply {r s : Nat} [Fintype Idx]
    (T : FrameTensorRSField (I := I) (M := M) r s)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) :
    tensorRSComponentInFrame T frame hframe x hx upper lower =
      (T x
        (Tensor0SBundle.basisTensor0S (I := I) (hframe.toBasisAt hx) upper))
        (fun a => hframe.toBasisAt hx (lower a)) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tensorRSComponentInFrame_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tensorRSComponentInFrame_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tensorRSComponentInFrame_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.tensorRSComponentInFrame_apply


def slots2 (i j : Idx) : Fin 2 -> Idx :=
  fun q => if q = 0 then i else j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.slots2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.slots2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.slots2 ``Submission.DifferentialGeometry.Tensor.Coordinates.slots2


def slots3 (i j k : Idx) : Fin 3 -> Idx :=
  fun q => if q = 0 then i else if q = 1 then j else k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.slots3 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.slots3"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.slots3 ``Submission.DifferentialGeometry.Tensor.Coordinates.slots3


def slots4 (i j k l : Idx) : Fin 4 -> Idx :=
  fun q => if q = 0 then i else if q = 1 then j else if q = 2 then k else l

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.slots4 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.slots4"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.slots4 ``Submission.DifferentialGeometry.Tensor.Coordinates.slots4

@[simp] theorem slots2_zero (i j : Idx) :
    slots2 i j 0 = i := by
  simp [slots2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.slots2_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.slots2_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.slots2_zero ``Submission.DifferentialGeometry.Tensor.Coordinates.slots2_zero

@[simp] theorem slots2_one (i j : Idx) :
    slots2 i j 1 = j := by
  simp [slots2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.slots2_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.slots2_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.slots2_one ``Submission.DifferentialGeometry.Tensor.Coordinates.slots2_one

@[simp] theorem slots3_zero (i j k : Idx) :
    slots3 i j k 0 = i := by
  simp [slots3]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.slots3_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.slots3_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.slots3_zero ``Submission.DifferentialGeometry.Tensor.Coordinates.slots3_zero

@[simp] theorem slots3_one (i j k : Idx) :
    slots3 i j k 1 = j := by
  simp [slots3]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.slots3_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.slots3_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.slots3_one ``Submission.DifferentialGeometry.Tensor.Coordinates.slots3_one

@[simp] theorem slots3_two (i j k : Idx) :
    slots3 i j k 2 = k := by
  simp [slots3]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.slots3_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.slots3_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.slots3_two ``Submission.DifferentialGeometry.Tensor.Coordinates.slots3_two

@[simp] theorem slots4_zero (i j k l : Idx) :
    slots4 i j k l 0 = i := by
  simp [slots4]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.slots4_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.slots4_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.slots4_zero ``Submission.DifferentialGeometry.Tensor.Coordinates.slots4_zero

@[simp] theorem slots4_one (i j k l : Idx) :
    slots4 i j k l 1 = j := by
  simp [slots4]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.slots4_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.slots4_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.slots4_one ``Submission.DifferentialGeometry.Tensor.Coordinates.slots4_one

@[simp] theorem slots4_two (i j k l : Idx) :
    slots4 i j k l 2 = k := by
  simp [slots4]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.slots4_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.slots4_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.slots4_two ``Submission.DifferentialGeometry.Tensor.Coordinates.slots4_two

@[simp] theorem slots4_three (i j k l : Idx) :
    slots4 i j k l 3 = l := by
  simp [slots4]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.slots4_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.slots4_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.slots4_three ``Submission.DifferentialGeometry.Tensor.Coordinates.slots4_three


def upperIdx1 (k : Idx) : Fin 1 -> Idx :=
  fun a =>
    let _ := a
    k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.upperIdx1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.upperIdx1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.upperIdx1 ``Submission.DifferentialGeometry.Tensor.Coordinates.upperIdx1


def lowerIdx2 (i j : Idx) : Fin 2 -> Idx :=
  slots2 i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.lowerIdx2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.lowerIdx2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.lowerIdx2 ``Submission.DifferentialGeometry.Tensor.Coordinates.lowerIdx2

@[simp] theorem upperIdx1_apply (k : Idx) (q : Fin 1) :
    upperIdx1 k q = k := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.upperIdx1_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.upperIdx1_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.upperIdx1_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.upperIdx1_apply

@[simp] theorem lowerIdx2_zero (i j : Idx) :
    lowerIdx2 i j 0 = i := by
  simp [lowerIdx2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.lowerIdx2_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.lowerIdx2_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.lowerIdx2_zero ``Submission.DifferentialGeometry.Tensor.Coordinates.lowerIdx2_zero

@[simp] theorem lowerIdx2_one (i j : Idx) :
    lowerIdx2 i j 1 = j := by
  simp [lowerIdx2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.lowerIdx2_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.lowerIdx2_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.lowerIdx2_one ``Submission.DifferentialGeometry.Tensor.Coordinates.lowerIdx2_one

@[simp] theorem Function_update_upperIdx1
    (k m : Idx) (a : Fin 1) :
    Function.update (upperIdx1 k) a m = upperIdx1 m := by
  fin_cases a
  funext q
  fin_cases q
  simp [upperIdx1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.Function_update_upperIdx1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.Function_update_upperIdx1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.Function_update_upperIdx1 ``Submission.DifferentialGeometry.Tensor.Coordinates.Function_update_upperIdx1

@[simp] theorem Function_update_lowerIdx2_zero
    (i j m : Idx) :
    Function.update (lowerIdx2 i j) 0 m = lowerIdx2 m j := by
  funext q
  fin_cases q <;> simp [lowerIdx2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.Function_update_lowerIdx2_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.Function_update_lowerIdx2_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.Function_update_lowerIdx2_zero ``Submission.DifferentialGeometry.Tensor.Coordinates.Function_update_lowerIdx2_zero

@[simp] theorem Function_update_lowerIdx2_one
    (i j m : Idx) :
    Function.update (lowerIdx2 i j) 1 m = lowerIdx2 i m := by
  funext q
  fin_cases q <;> simp [lowerIdx2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.Function_update_lowerIdx2_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.Function_update_lowerIdx2_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.Function_update_lowerIdx2_one ``Submission.DifferentialGeometry.Tensor.Coordinates.Function_update_lowerIdx2_one


def tensor02CompInFrame (T : FrameTensor0SField (I := I) (M := M) 2)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u) (i j : Idx) : 𝕜 :=
  tensor0SComponentInFrameAt T frame hframe x hx (slots2 i j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tensor02CompInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tensor02CompInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tensor02CompInFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.tensor02CompInFrame

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
@[simp] theorem tensor02CompInFrame_eval
    (T : FrameTensor0SField (I := I) (M := M) 2)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u) (i j : Idx) :
    tensor02CompInFrame T frame hframe x hx i j =
      T x (fun a => hframe.toBasisAt hx (slots2 i j a)) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tensor02CompInFrame_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tensor02CompInFrame_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tensor02CompInFrame_eval ``Submission.DifferentialGeometry.Tensor.Coordinates.tensor02CompInFrame_eval


def tensor04CompInFrame (T : FrameTensor0SField (I := I) (M := M) 4)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u) (i j k l : Idx) : 𝕜 :=
  tensor0SComponentInFrameAt T frame hframe x hx (slots4 i j k l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tensor04CompInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tensor04CompInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tensor04CompInFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.tensor04CompInFrame

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
@[simp] theorem tensor04CompInFrame_eval
    (T : FrameTensor0SField (I := I) (M := M) 4)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u) (i j k l : Idx) :
    tensor04CompInFrame T frame hframe x hx i j k l =
      T x (fun a => hframe.toBasisAt hx (slots4 i j k l a)) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tensor04CompInFrame_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tensor04CompInFrame_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tensor04CompInFrame_eval ``Submission.DifferentialGeometry.Tensor.Coordinates.tensor04CompInFrame_eval


def tensor12CompInFrame [Fintype Idx] (T : FrameTensorRSField (I := I) (M := M) 1 2)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u) (k i j : Idx) : 𝕜 :=
  tensorRSComponentInFrame T frame hframe x hx (upperIdx1 k) (lowerIdx2 i j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tensor12CompInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tensor12CompInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tensor12CompInFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.tensor12CompInFrame

@[simp] theorem tensor12CompInFrame_eval [Fintype Idx]
    (T : FrameTensorRSField (I := I) (M := M) 1 2)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u) (k i j : Idx) :
    tensor12CompInFrame T frame hframe x hx k i j =
      (T x
        (Tensor0SBundle.basisTensor0S (I := I) (hframe.toBasisAt hx) (upperIdx1 k)))
        (fun a => hframe.toBasisAt hx (lowerIdx2 i j a)) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tensor12CompInFrame_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tensor12CompInFrame_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tensor12CompInFrame_eval ``Submission.DifferentialGeometry.Tensor.Coordinates.tensor12CompInFrame_eval


def tensor13CompInFrame [Fintype Idx] (T : FrameTensorRSField (I := I) (M := M) 1 3)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u) (a i j k : Idx) : 𝕜 :=
  tensorRSComponentInFrame T frame hframe x hx (upperIdx1 a) (slots3 i j k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tensor13CompInFrame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tensor13CompInFrame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tensor13CompInFrame ``Submission.DifferentialGeometry.Tensor.Coordinates.tensor13CompInFrame

@[simp] theorem tensor13CompInFrame_eval [Fintype Idx]
    (T : FrameTensorRSField (I := I) (M := M) 1 3)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u)
    (x : M) (hx : x ∈ u) (a i j k : Idx) :
    tensor13CompInFrame T frame hframe x hx a i j k =
      (T x
        (Tensor0SBundle.basisTensor0S (I := I) (hframe.toBasisAt hx) (upperIdx1 a)))
        (fun q => hframe.toBasisAt hx (slots3 i j k q)) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tensor13CompInFrame_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tensor13CompInFrame_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tensor13CompInFrame_eval ``Submission.DifferentialGeometry.Tensor.Coordinates.tensor13CompInFrame_eval

end

end DifferentialGeometry.Tensor.Coordinates
