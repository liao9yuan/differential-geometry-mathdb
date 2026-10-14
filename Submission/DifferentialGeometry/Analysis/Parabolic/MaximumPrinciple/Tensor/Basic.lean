import Submission.DifferentialGeometry.Geometry.Curvature.Sections.Trace
import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric
import Submission.DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit
import Submission.DifferentialGeometry.Geometry.Metric.QuadraticBounds.TimeSlab
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Connection.OneJet
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Connection.Tangent
import Submission.DifferentialGeometry.Geometry.Connection.RicciIdentity.Tensor0S.Realization
import Submission.DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Minimum
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.BallMonotonicity
import Submission.DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.IntermediateValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Set
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]

abbrev TwoTensorFamily : Type _ :=
  Real -> RawTwoTensorField (I := I) (M := M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TwoTensorFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TwoTensorFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TwoTensorFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.TwoTensorFamily

abbrev TimeDependentVectorField : Type _ :=
  Real -> (x : M) -> TangentSpace I x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TimeDependentVectorField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TimeDependentVectorField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TimeDependentVectorField ``Submission.DifferentialGeometry.PDE.RicciFlow.TimeDependentVectorField

abbrev TensorQuadraticFormFamily : Type _ :=
  Real -> (x : M) -> TangentSpace I x -> Real

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TensorQuadraticFormFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TensorQuadraticFormFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TensorQuadraticFormFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.TensorQuadraticFormFamily

abbrev TensorNabla1Family : Type _ :=
  Real -> (x : M) ->
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TensorNabla1Family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TensorNabla1Family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TensorNabla1Family ``Submission.DifferentialGeometry.PDE.RicciFlow.TensorNabla1Family

abbrev TensorNabla2Family : Type _ :=
  Real -> (x : M) ->
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TensorNabla2Family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TensorNabla2Family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TensorNabla2Family ``Submission.DifferentialGeometry.PDE.RicciFlow.TensorNabla2Family

abbrev TwoTensorReaction : Type _ :=
  Real -> SmoothRiemannianMetric I M -> RawTwoTensorField (I := I) (M := M) ->
    RawTwoTensorField (I := I) (M := M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TwoTensorReaction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TwoTensorReaction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TwoTensorReaction ``Submission.DifferentialGeometry.PDE.RicciFlow.TwoTensorReaction

def TwoTensorSymmetricAt (A : RawTwoTensorField (I := I) (M := M)) (x : M) : Prop :=
  ∀ X Y : TangentSpace I x, A x X Y = A x Y X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TwoTensorSymmetricAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TwoTensorSymmetricAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TwoTensorSymmetricAt ``Submission.DifferentialGeometry.PDE.RicciFlow.TwoTensorSymmetricAt

structure TwoTensorBilinearAt (A : RawTwoTensorField (I := I) (M := M)) (x : M) :
    Prop where
  add_left : ∀ X Y Z : TangentSpace I x,
    A x (X + Y) Z = A x X Z + A x Y Z
  smul_left : ∀ (c : Real) (X Z : TangentSpace I x),
    A x (c • X) Z = c * A x X Z
  add_right : ∀ X Y Z : TangentSpace I x,
    A x X (Y + Z) = A x X Y + A x X Z
  smul_right : ∀ (c : Real) (X Z : TangentSpace I x),
    A x X (c • Z) = c * A x X Z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TwoTensorBilinearAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TwoTensorBilinearAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TwoTensorBilinearAt ``Submission.DifferentialGeometry.PDE.RicciFlow.TwoTensorBilinearAt

def TwoTensorNonnegativeAt (A : RawTwoTensorField (I := I) (M := M)) (x : M) : Prop :=
  ∀ v : TangentSpace I x, 0 ≤ A x v v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TwoTensorNonnegativeAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TwoTensorNonnegativeAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TwoTensorNonnegativeAt ``Submission.DifferentialGeometry.PDE.RicciFlow.TwoTensorNonnegativeAt

def TwoTensorPositiveDefiniteAt (A : RawTwoTensorField (I := I) (M := M)) (x : M) : Prop :=
  ∀ v : TangentSpace I x, v ≠ 0 -> 0 < A x v v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TwoTensorPositiveDefiniteAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TwoTensorPositiveDefiniteAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TwoTensorPositiveDefiniteAt ``Submission.DifferentialGeometry.PDE.RicciFlow.TwoTensorPositiveDefiniteAt

def TwoTensorFamilySymmetricOn (S : TwoTensorFamily (I := I) (M := M))
    (U : Set Real) : Prop :=
  ∀ t, t ∈ U -> ∀ x, TwoTensorSymmetricAt (I := I) (M := M) (S t) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilySymmetricOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilySymmetricOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilySymmetricOn ``Submission.DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilySymmetricOn

def TwoTensorFamilyNonnegativeOn (S : TwoTensorFamily (I := I) (M := M))
    (U : Set Real) : Prop :=
  ∀ t, t ∈ U -> ∀ x, TwoTensorNonnegativeAt (I := I) (M := M) (S t) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilyNonnegativeOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilyNonnegativeOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilyNonnegativeOn ``Submission.DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilyNonnegativeOn


def TwoTensorFamilyPositiveDefiniteOn (S : TwoTensorFamily (I := I) (M := M))
    (U : Set Real) : Prop :=
  ∀ t, t ∈ U -> ∀ x, TwoTensorPositiveDefiniteAt (I := I) (M := M) (S t) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilyPositiveDefiniteOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilyPositiveDefiniteOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilyPositiveDefiniteOn ``Submission.DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilyPositiveDefiniteOn


def TwoTensorFamilyNonnegativeAtTime (S : TwoTensorFamily (I := I) (M := M))
    (t : Real) : Prop :=
  ∀ x, TwoTensorNonnegativeAt (I := I) (M := M) (S t) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilyNonnegativeAtTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilyNonnegativeAtTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilyNonnegativeAtTime ``Submission.DifferentialGeometry.PDE.RicciFlow.TwoTensorFamilyNonnegativeAtTime

def tensorBarrierFamily
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) : TwoTensorFamily (I := I) (M := M) :=
  fun t x v w => S t x v w + epsilon * (delta + t - t0) * (G t).inner x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.tensorBarrierFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.tensorBarrierFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.tensorBarrierFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.tensorBarrierFamily

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] in
@[simp] theorem tensorBarrierFamily_apply
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (x : M) (v w : TangentSpace I x) :
    tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t x v w =
      S t x v w + epsilon * (delta + t - t0) * (G t).inner x v w := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.tensorBarrierFamily_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.tensorBarrierFamily_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.tensorBarrierFamily_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.tensorBarrierFamily_apply

abbrev TwoTensorSecFamily : Type _ :=
  Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TwoTensorSecFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TwoTensorSecFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TwoTensorSecFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.TwoTensorSecFamily

abbrev TensorNabla1SecFamily : Type _ :=
  Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) 3

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TensorNabla1SecFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TensorNabla1SecFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TensorNabla1SecFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.TensorNabla1SecFamily

abbrev TensorNabla2SecFamily : Type _ :=
  Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) 4

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.TensorNabla2SecFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.TensorNabla2SecFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.TensorNabla2SecFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.TensorNabla2SecFamily

def twoTensorSecToFamily
    (S : TwoTensorSecFamily (I := I) (M := M)) :
    TwoTensorFamily (I := I) (M := M) :=
  fun t x v w => S t x (vec2 (I := I) v w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily

omit [IsManifold I ∞ M] [IsManifold I 2 M] in
@[simp]
theorem twoTensorSecToFamily_apply
    (S : TwoTensorSecFamily (I := I) (M := M))
    (t : Real) (x : M) (v w : TangentSpace I x) :
    twoTensorSecToFamily (I := I) (M := M) S t x v w =
      S t x (vec2 (I := I) v w) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily_apply

omit [IsManifold I ∞ M] [IsManifold I 2 M] in
theorem twoTensorSecToFamily_bilin
    (S : TwoTensorSecFamily (I := I) (M := M))
    (t : Real) (x : M) :
    TwoTensorBilinearAt (I := I) (M := M)
      (twoTensorSecToFamily (I := I) (M := M) S t) x := by
  constructor
  · intro X Y Z
    classical
    let m : Fin 2 -> TangentSpace I x := vec2 (I := I) X Z
    have hmap := (S t x).map_update_add m (0 : Fin 2) X Y
    have hleft :
        Function.update m (0 : Fin 2) (X + Y) = vec2 (I := I) (X + Y) Z := by
      funext i
      fin_cases i <;> simp [m, vec2, DifferentialGeometry.Geometry.Curvature.vec2, Function.update]
    have hX : Function.update m (0 : Fin 2) X = vec2 (I := I) X Z := by
      funext i
      fin_cases i <;> simp [m, vec2, DifferentialGeometry.Geometry.Curvature.vec2, Function.update]
    have hY : Function.update m (0 : Fin 2) Y = vec2 (I := I) Y Z := by
      funext i
      fin_cases i <;> simp [m, vec2, DifferentialGeometry.Geometry.Curvature.vec2, Function.update]
    simpa [twoTensorSecToFamily, hleft, hX, hY] using hmap
  · intro c X Z
    classical
    let m : Fin 2 -> TangentSpace I x := vec2 (I := I) X Z
    have hmap := (S t x).map_update_smul m (0 : Fin 2) c X
    have hleft :
        Function.update m (0 : Fin 2) (c • X) = vec2 (I := I) (c • X) Z := by
      funext i
      fin_cases i <;> simp [m, vec2, DifferentialGeometry.Geometry.Curvature.vec2, Function.update]
    have hX : Function.update m (0 : Fin 2) X = vec2 (I := I) X Z := by
      funext i
      fin_cases i <;> simp [m, vec2, DifferentialGeometry.Geometry.Curvature.vec2, Function.update]
    simpa [twoTensorSecToFamily, hleft, hX, smul_eq_mul] using hmap
  · intro X Y Z
    classical
    let m : Fin 2 -> TangentSpace I x := vec2 (I := I) X Y
    have hmap := (S t x).map_update_add m (1 : Fin 2) Y Z
    have hleft :
        Function.update m (1 : Fin 2) (Y + Z) = vec2 (I := I) X (Y + Z) := by
      funext i
      fin_cases i <;> simp [m, vec2, DifferentialGeometry.Geometry.Curvature.vec2, Function.update]
    have hY : Function.update m (1 : Fin 2) Y = vec2 (I := I) X Y := by
      funext i
      fin_cases i <;> simp [m, vec2, DifferentialGeometry.Geometry.Curvature.vec2, Function.update]
    have hZ : Function.update m (1 : Fin 2) Z = vec2 (I := I) X Z := by
      funext i
      fin_cases i <;> simp [m, vec2, DifferentialGeometry.Geometry.Curvature.vec2, Function.update]
    simpa [twoTensorSecToFamily, hleft, hY, hZ] using hmap
  · intro c X Z
    classical
    let m : Fin 2 -> TangentSpace I x := vec2 (I := I) X Z
    have hmap := (S t x).map_update_smul m (1 : Fin 2) c Z
    have hleft :
        Function.update m (1 : Fin 2) (c • Z) = vec2 (I := I) X (c • Z) := by
      funext i
      fin_cases i <;> simp [m, vec2, DifferentialGeometry.Geometry.Curvature.vec2, Function.update]
    have hZ : Function.update m (1 : Fin 2) Z = vec2 (I := I) X Z := by
      funext i
      fin_cases i <;> simp [m, vec2, DifferentialGeometry.Geometry.Curvature.vec2, Function.update]
    simpa [twoTensorSecToFamily, hleft, hZ, smul_eq_mul] using hmap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily_bilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily_bilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily_bilin ``Submission.DifferentialGeometry.PDE.RicciFlow.twoTensorSecToFamily_bilin

noncomputable def tensorBarrierSecFamily
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 : Real) :
    TwoTensorSecFamily (I := I) (M := M) :=
  fun t =>
    letI := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
    S t + (epsilon * (delta + t - t0)) •
      Tensor0SBundle.metricTensorField (I := I) (G t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.tensorBarrierSecFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.tensorBarrierSecFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.tensorBarrierSecFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.tensorBarrierSecFamily

omit [IsManifold I 2 M] in
theorem tensorBarrierSec_apply
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (x : M) (v w : TangentSpace I x) :
    twoTensorSecToFamily (I := I) (M := M)
        (tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0)
        t x v w =
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 t x v w := by
  simp only [twoTensorSecToFamily, tensorBarrierSecFamily, tensorBarrierFamily,
    ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_smul,
    Pi.smul_apply]
  change
    (S t x (vec2 (I := I) v w) +
        (epsilon * (delta + t - t0)) *
          (Tensor0SBundle.metricTensorField (I := I) (G t) x)
            (vec2 (I := I) v w)) =
      S t x (vec2 (I := I) v w) +
        epsilon * (delta + t - t0) * (G t).inner x v w
  rw [Tensor0SBundle.metricTensorField_apply]
  have h0 : vec2 (I := I) v w 0 = v := by
    simp [DifferentialGeometry.Geometry.Curvature.vec2]
  have h1 : vec2 (I := I) v w 1 = w := by
    simp [DifferentialGeometry.Geometry.Curvature.vec2]
  rw [h0, h1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.tensorBarrierSec_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.tensorBarrierSec_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.tensorBarrierSec_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.tensorBarrierSec_apply

omit [IsManifold I ∞ M] [IsManifold I 2 M] in
theorem eval02_sec_eq
    (S : TwoTensorSecFamily (I := I) (M := M))
    (t : Real) (x : M) (v w : TangentSpace I x) :
    eval02 (I := I) (M := M) (S t x) v w =
      twoTensorSecToFamily (I := I) (M := M) S t x v w := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.eval02_sec_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.eval02_sec_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.eval02_sec_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.eval02_sec_eq

omit [IsManifold I ∞ M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] [IsManifold I 2 M] in
theorem quad02_sec_eq
    (S : TwoTensorSecFamily (I := I) (M := M))
    (t : Real) (x : M) (v : TangentSpace I x) :
    quad02 (I := I) (M := M) (S t x) v =
      twoTensorSecToFamily (I := I) (M := M) S t x v v := by
  calc
    quad02 (I := I) (M := M) (S t x) v =
        eval02 (I := I) (M := M) (S t x) v v := by
          rw [eval02_self]
    _ = twoTensorSecToFamily (I := I) (M := M) S t x v v :=
          eval02_sec_eq (I := I) (M := M) S t x v v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.quad02_sec_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.quad02_sec_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.quad02_sec_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.quad02_sec_eq

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem barrierSymmAt
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {epsilon delta t0 t : Real} {x : M}
    (hS : TwoTensorSymmetricAt (I := I) (M := M) (S t) x) :
    TwoTensorSymmetricAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t) x := by
  intro v w
  simp [tensorBarrierFamily, hS v w, (G t).symm x v w]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.barrierSymmAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.barrierSymmAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.barrierSymmAt ``Submission.DifferentialGeometry.PDE.RicciFlow.barrierSymmAt

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem metricInner_bilinAt
    (G : Real -> SmoothRiemannianMetric I M)
    (t : Real) (x : M) :
    TwoTensorBilinearAt (I := I) (M := M)
      (fun y v w => (G t).inner y v w) x := by
  constructor <;> intros <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricInner_bilinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricInner_bilinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricInner_bilinAt ``Submission.DifferentialGeometry.PDE.RicciFlow.metricInner_bilinAt

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem barrierBilinearAt
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {epsilon delta t0 t : Real} {x : M}
    (hS : TwoTensorBilinearAt (I := I) (M := M) (S t) x) :
    TwoTensorBilinearAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t) x := by
  constructor
  · intro X Y Z
    simp [tensorBarrierFamily, hS.add_left X Y Z, add_assoc]
    ring
  · intro c X Z
    simp [tensorBarrierFamily, hS.smul_left c X Z, mul_assoc, mul_left_comm]
    ring
  · intro X Y Z
    simp [tensorBarrierFamily, hS.add_right X Y Z, mul_add, add_assoc]
    ring
  · intro c X Z
    simp [tensorBarrierFamily, hS.smul_right c X Z, mul_assoc, mul_left_comm]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.barrierBilinearAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.barrierBilinearAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.barrierBilinearAt ``Submission.DifferentialGeometry.PDE.RicciFlow.barrierBilinearAt

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem vec2_self_eq_const {x : M} (v : TangentSpace I x) :
    vec2 (I := I) v v = fun _ : Fin 2 => v := by
  funext i
  fin_cases i <;> simp [vec2, DifferentialGeometry.Geometry.Curvature.vec2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.vec2_self_eq_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.vec2_self_eq_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.vec2_self_eq_const ``Submission.DifferentialGeometry.PDE.RicciFlow.vec2_self_eq_const

omit [IsManifold I 2 M] in
omit [IsManifold I 2 M] in
theorem barrierSec_smul2
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (x : M) (a : Real)
    (v : TangentSpace I x) :
    twoTensorSecToFamily (I := I) (M := M)
        (tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0)
        t x (a • v) (a • v) =
      a * a *
        twoTensorSecToFamily (I := I) (M := M)
          (tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0)
          t x v v := by
  have hscale := tensor02_smul2 (I := I) (M := M)
    ((tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0) t x)
    a v
  simpa [quad02, twoTensorSecToFamily, vec2_self_eq_const] using hscale

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.barrierSec_smul2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.barrierSec_smul2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.barrierSec_smul2 ``Submission.DifferentialGeometry.PDE.RicciFlow.barrierSec_smul2

omit [IsManifold I 2 M] in
theorem barrierFamily_smul2
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (x : M) (a : Real)
    (v : TangentSpace I x) :
    tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 t x (a • v) (a • v) =
      a * a *
        tensorBarrierFamily (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S)
          epsilon delta t0 t x v v := by
  rw [← tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0 t x
      (a • v) (a • v),
    ← tensorBarrierSec_apply (I := I) (M := M) G S epsilon delta t0 t x v v]
  exact barrierSec_smul2 (I := I) (M := M) G S epsilon delta t0 t x a v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.barrierFamily_smul2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.barrierFamily_smul2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.barrierFamily_smul2 ``Submission.DifferentialGeometry.PDE.RicciFlow.barrierFamily_smul2

omit [IsManifold I 2 M] in
theorem negBarrier_unit
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (x : M) (v : TangentSpace I x)
    (hneg :
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 t x v v < 0) :
    ∃ u : TangentSpace I x,
      (G t).inner x u u = 1 ∧
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 t x u u < 0 := by
  let B : TwoTensorFamily (I := I) (M := M) :=
    tensorBarrierFamily (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0
  have hv : v ≠ 0 := by
    intro hv0
    have hzero : B t x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 := by
      have hscale := barrierFamily_smul2 (I := I) (M := M)
        G S epsilon delta t0 t x 0 (0 : TangentSpace I x)
      simpa [B] using hscale
    have hnegB : B t x v v < 0 := by
      simpa [B] using hneg
    have hvzero : B t x v v = 0 := by
      simpa [hv0] using hzero
    rw [hvzero] at hnegB
    linarith
  let r : Real := (G t).inner x v v
  have hrpos : 0 < r := (G t).pos x v hv
  let s : Real := Real.sqrt r
  have hspos : 0 < s := Real.sqrt_pos.mpr hrpos
  have hsne : s ≠ 0 := ne_of_gt hspos
  let a : Real := s⁻¹
  let u : TangentSpace I x := a • v
  have hss : s * s = r := by
    simpa [sq] using (Real.sq_sqrt (le_of_lt hrpos))
  have hunit : (G t).inner x u u = 1 := by
    have haa : a * a * r = 1 := by
      have hmul : (s * s) * (s⁻¹ * s⁻¹) = 1 := by
        field_simp [hsne]
      calc
        a * a * r = (s⁻¹ * s⁻¹) * (s * s) := by
          rw [hss]
        _ = (s * s) * (s⁻¹ * s⁻¹) := by ring
        _ = 1 := hmul
    calc
      (G t).inner x u u = a * a * r := by
        simpa [u, r] using metric_smul2 (I := I) (M := M) (G t) a v
      _ = 1 := haa
  have hcoeff_pos : 0 < a * a := mul_pos (inv_pos.mpr hspos) (inv_pos.mpr hspos)
  have hquad :
      B t x u u = a * a * B t x v v := by
    simpa [B, u, a] using
      barrierFamily_smul2 (I := I) (M := M) G S epsilon delta t0 t x a v
  refine ⟨u, hunit, ?_⟩
  change B t x u u < 0
  rw [hquad]
  have hnegB : B t x v v < 0 := by
    simpa [B] using hneg
  exact mul_neg_of_pos_of_neg hcoeff_pos hnegB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.negBarrier_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.negBarrier_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.negBarrier_unit ``Submission.DifferentialGeometry.PDE.RicciFlow.negBarrier_unit

def barrierUnitQuad
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 tA tB : Real)
    (p : MetricUnitTangentSlab (I := I) (M := M) G tA tB) : Real :=
  tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 p.1.1
    (MetricUnitTangent.base (I := I) (M := M) p.2)
    (MetricUnitTangent.vec (I := I) (M := M) p.2)
    (MetricUnitTangent.vec (I := I) (M := M) p.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.barrierUnitQuad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.barrierUnitQuad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.barrierUnitQuad ``Submission.DifferentialGeometry.PDE.RicciFlow.barrierUnitQuad

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] in
@[simp]
theorem barrierUnitQuad_mk
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 tA tB t : Real) (ht : t ∈ Set.Icc tA tB)
    (x : M) (v : TangentSpace I x)
    (hunit : (G t).inner x v v = 1) :
    barrierUnitQuad (I := I) (M := M) G S epsilon delta t0 tA tB
      (⟨⟨t, ht⟩,
        (⟨(⟨x, v⟩ : TangentBundle I M), hunit⟩ :
          MetricUnitTangent (I := I) (M := M) (G t))⟩ :
        MetricUnitTangentSlab (I := I) (M := M) G tA tB) =
      tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t x v v := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.barrierUnitQuad_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.barrierUnitQuad_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.barrierUnitQuad_mk ``Submission.DifferentialGeometry.PDE.RicciFlow.barrierUnitQuad_mk

omit [IsManifold I 2 M] in
theorem negBarrier_unitSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 tA tB t : Real) (ht : t ∈ Set.Icc tA tB)
    (x : M) (v : TangentSpace I x)
    (hneg :
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 t x v v < 0) :
    ∃ p : MetricUnitTangentSlab (I := I) (M := M) G tA tB,
      p.1.1 = t ∧
      barrierUnitQuad (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 tA tB p < 0 := by
  obtain ⟨u, hunit, hneg_u⟩ :=
    negBarrier_unit (I := I) (M := M) G S epsilon delta t0 t x v hneg
  refine ⟨⟨⟨t, ht⟩,
      (⟨(⟨x, u⟩ : TangentBundle I M), hunit⟩ :
        MetricUnitTangent (I := I) (M := M) (G t))⟩, rfl, ?_⟩
  simpa using hneg_u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.negBarrier_unitSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.negBarrier_unitSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.negBarrier_unitSlab ``Submission.DifferentialGeometry.PDE.RicciFlow.negBarrier_unitSlab

omit [IsManifold I 2 M] in
theorem failure_unitSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 tA tB : Real)
    (hfail :
      ¬ TwoTensorFamilyNonnegativeOn (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S)
          epsilon delta t0)
        (Set.Icc tA tB)) :
    ∃ p : MetricUnitTangentSlab (I := I) (M := M) G tA tB,
      barrierUnitQuad (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 tA tB p < 0 := by
  classical
  unfold TwoTensorFamilyNonnegativeOn TwoTensorNonnegativeAt at hfail
  push Not at hfail
  obtain ⟨t, ht, x, v, hneg⟩ := hfail
  obtain ⟨p, _hpt, hpneg⟩ :=
    negBarrier_unitSlab (I := I) (M := M) G S epsilon delta t0 tA tB
      t ht x v hneg
  exact ⟨p, hpneg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.failure_unitSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.failure_unitSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.failure_unitSlab ``Submission.DifferentialGeometry.PDE.RicciFlow.failure_unitSlab

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
private theorem metricUnitSlab_time_cont
    (G : Real -> SmoothRiemannianMetric I M) (tA tB : Real) :
    Continuous (fun p : MetricUnitTangentSlab (I := I) (M := M) G tA tB =>
      (p.1 : {t : Real // t ∈ Set.Icc tA tB})) := by
  change Continuous
    (fun p :
      (Σ t : {t : Real // t ∈ Set.Icc tA tB},
        MetricUnitTangent (I := I) (M := M) (G t.1)) => p.1)
  rw [continuous_def]
  intro s hs
  exact isOpen_sigma_fst_preimage s

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.metricUnitSlab_time_cont
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.metricUnitSlab_time_cont target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
theorem metricUnitSlab_timeVal_cont
    (G : Real -> SmoothRiemannianMetric I M) (tA tB : Real) :
    Continuous (fun p : MetricUnitTangentSlab (I := I) (M := M) G tA tB =>
      p.1.1) :=
  continuous_subtype_val.comp
    (metricUnitSlab_time_cont (I := I) (M := M) G tA tB)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricUnitSlab_timeVal_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricUnitSlab_timeVal_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricUnitSlab_timeVal_cont ``Submission.DifferentialGeometry.PDE.RicciFlow.metricUnitSlab_timeVal_cont

def metricBundleQuad
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (q : {t : Real // t ∈ K} × TangentBundle I M) : Real :=
  metricTimeBundleQuad (I := I) (M := M) G K q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricBundleQuad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricBundleQuad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricBundleQuad ``Submission.DifferentialGeometry.PDE.RicciFlow.metricBundleQuad

def tensorSecBundleQuad
    (S : TwoTensorSecFamily (I := I) (M := M)) (K : Set Real)
    (q : {t : Real // t ∈ K} × TangentBundle I M) : Real :=
  S q.1.1 q.2.proj (fun _ : Fin 2 => q.2.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.tensorSecBundleQuad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.tensorSecBundleQuad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.tensorSecBundleQuad ``Submission.DifferentialGeometry.PDE.RicciFlow.tensorSecBundleQuad

omit [IsManifold I 2 M] in
theorem metricFamQuadCont
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real)
    (hG :
      Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
        TotalSpace.mk' (Tensor0SModel 2 Real E)
          (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
          (metricTensorField (I := I) (G q.1.1) q.2.proj))) :
    Continuous (metricBundleQuad (I := I) (M := M) G K) := by
  let b : ({t : Real // t ∈ K} × TangentBundle I M) -> M := fun q => q.2.proj
  let T : (q : {t : Real // t ∈ K} × TangentBundle I M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (b q) :=
    fun q => metricTensorField (I := I) (G q.1.1) (b q)
  let v : Fin 2 -> (q : {t : Real // t ∈ K} × TangentBundle I M) ->
      TangentSpace I (b q) :=
    fun _ q => q.2.2
  have hb : Continuous b := by
    dsimp [b]
    exact (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_snd
  have hT : Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) (b q) (T q)) := by
    simpa [b, T] using hG
  have hv : ∀ i : Fin 2, Continuous
      (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b q) (v i q)) := by
    intro i
    simpa [b, v] using (continuous_snd :
      Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
        (q.2 : TangentBundle I M)))
  have hEval := TensorMultilinear.continuous_section_apply_base
    (𝕜 := Real) (I := I) (M := M)
    (P := {t : Real // t ∈ K} × TangentBundle I M) (n := 2)
    b hb T hT v hv
  let h : Continuous (metricBundleQuad (I := I) (M := M) G K) := hEval
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricFamQuadCont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricFamQuadCont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricFamQuadCont ``Submission.DifferentialGeometry.PDE.RicciFlow.metricFamQuadCont

omit [IsManifold I 2 M] in
theorem tensorQuadCont
    (S : TwoTensorSecFamily (I := I) (M := M)) (K : Set Real)
    (hS :
      Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
        TotalSpace.mk' (Tensor0SModel 2 Real E)
          (E := fun x : M => Tensor0SSpace 2 I x) q.2.proj
          (S q.1.1 q.2.proj))) :
    Continuous (tensorSecBundleQuad (I := I) (M := M) S K) := by
  let b : ({t : Real // t ∈ K} × TangentBundle I M) -> M := fun q => q.2.proj
  let T : (q : {t : Real // t ∈ K} × TangentBundle I M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 (b q) :=
    fun q => S q.1.1 (b q)
  let v : Fin 2 -> (q : {t : Real // t ∈ K} × TangentBundle I M) ->
      TangentSpace I (b q) :=
    fun _ q => q.2.2
  have hb : Continuous b := by
    dsimp [b]
    exact (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_snd
  have hT : Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      TotalSpace.mk' (Tensor0SModel 2 Real E)
        (E := fun x : M => Tensor0SSpace 2 I x) (b q) (T q)) := by
    simpa [b, T] using hS
  have hv : ∀ i : Fin 2, Continuous
      (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b q) (v i q)) := by
    intro i
    simpa [b, v] using (continuous_snd :
      Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
        (q.2 : TangentBundle I M)))
  have hEval := TensorMultilinear.continuous_section_apply_base
    (𝕜 := Real) (I := I) (M := M)
    (P := {t : Real // t ∈ K} × TangentBundle I M) (n := 2)
    b hb T hT v hv
  let h : Continuous (tensorSecBundleQuad (I := I) (M := M) S K) := hEval
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.tensorQuadCont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.tensorQuadCont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.tensorQuadCont ``Submission.DifferentialGeometry.PDE.RicciFlow.tensorQuadCont

def barrierBundleQuad
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) (K : Set Real)
    (q : {t : Real // t ∈ K} × TangentBundle I M) : Real :=
  tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
    q.1.1 q.2.proj q.2.2 q.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.barrierBundleQuad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.barrierBundleQuad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.barrierBundleQuad ``Submission.DifferentialGeometry.PDE.RicciFlow.barrierBundleQuad

omit [IsManifold I 2 M] in
omit [IsManifold I 2 M] in
theorem barrierBundleCont
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 : Real) (K : Set Real)
    (hS : Continuous (tensorSecBundleQuad (I := I) (M := M) S K))
    (hG : Continuous (metricBundleQuad (I := I) (M := M) G K)) :
    Continuous (barrierBundleQuad (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0 K) := by
  have htime :
      Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
        (q.1.1 : Real)) :=
    continuous_subtype_val.comp continuous_fst
  have hcoef :
      Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
        epsilon * (delta + q.1.1 - t0)) := by
    exact continuous_const.mul ((continuous_const.add htime).sub continuous_const)
  have hmain :
      Continuous (fun q : {t : Real // t ∈ K} × TangentBundle I M =>
        tensorSecBundleQuad (I := I) (M := M) S K q +
          (epsilon * (delta + q.1.1 - t0)) *
            metricBundleQuad (I := I) (M := M) G K q) :=
    hS.add (hcoef.mul hG)
  refine hmain.congr ?_
  intro q
  simp [barrierBundleQuad, tensorSecBundleQuad, metricBundleQuad,
    metricTimeBundleQuad, tensorBarrierFamily, twoTensorSecToFamily,
    vec2_self_eq_const, mul_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.barrierBundleCont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.barrierBundleCont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.barrierBundleCont ``Submission.DifferentialGeometry.PDE.RicciFlow.barrierBundleCont

def barrierTimeSlabQuad
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) (K : Set Real)
    (p : MetricUnitTangentTimeSlab (I := I) (M := M) G K) : Real :=
  tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
    (MetricUnitTangentTimeSlab.time (I := I) (M := M) p)
    (MetricUnitTangentTimeSlab.base (I := I) (M := M) p)
    (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p)
    (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.barrierTimeSlabQuad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.barrierTimeSlabQuad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.barrierTimeSlabQuad ``Submission.DifferentialGeometry.PDE.RicciFlow.barrierTimeSlabQuad

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem barrierTimeSlabQuad_apply
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) (K : Set Real)
    (p : MetricUnitTangentTimeSlab (I := I) (M := M) G K) :
    barrierTimeSlabQuad (I := I) (M := M) G S epsilon delta t0 K p =
      tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0
        (MetricUnitTangentTimeSlab.time (I := I) (M := M) p)
        (MetricUnitTangentTimeSlab.base (I := I) (M := M) p)
        (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p)
        (MetricUnitTangentTimeSlab.vec (I := I) (M := M) p) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.barrierTimeSlabQuad_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.barrierTimeSlabQuad_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.barrierTimeSlabQuad_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.barrierTimeSlabQuad_apply

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] in
@[simp]
theorem barrierTimeSlabQuad_mk
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (K : Set Real) (ht : t ∈ K)
    (x : M) (v : TangentSpace I x)
    (hunit : (G t).inner x v v = 1) :
    barrierTimeSlabQuad (I := I) (M := M) G S epsilon delta t0 K
      (⟨(⟨t, ht⟩, (⟨x, v⟩ : TangentBundle I M)), hunit⟩ :
        MetricUnitTangentTimeSlab (I := I) (M := M) G K) =
      tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t x v v := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.barrierTimeSlabQuad_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.barrierTimeSlabQuad_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.barrierTimeSlabQuad_mk ``Submission.DifferentialGeometry.PDE.RicciFlow.barrierTimeSlabQuad_mk

omit [IsManifold I 2 M] in
theorem barrierTimeCont
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 : Real) (K : Set Real)
    (hS : Continuous (tensorSecBundleQuad (I := I) (M := M) S K))
    (hG : Continuous (metricBundleQuad (I := I) (M := M) G K)) :
    Continuous
      (barrierTimeSlabQuad (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0 K) := by
  have hbundle := barrierBundleCont (I := I) (M := M)
    G S epsilon delta t0 K hS hG
  have hsub :
      Continuous (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G K =>
        (p.1 : {t : Real // t ∈ K} × TangentBundle I M)) :=
    continuous_subtype_val
  change Continuous (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G K =>
    barrierBundleQuad (I := I) (M := M) G
      (twoTensorSecToFamily (I := I) (M := M) S) epsilon delta t0 K p.1)
  exact hbundle.comp hsub

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.barrierTimeCont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.barrierTimeCont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.barrierTimeCont ``Submission.DifferentialGeometry.PDE.RicciFlow.barrierTimeCont

omit [IsManifold I 2 M] in
theorem negBarrier_timeSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) {K : Set Real} (ht : t ∈ K)
    (x : M) (v : TangentSpace I x)
    (hneg :
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 t x v v < 0) :
    ∃ p : MetricUnitTangentTimeSlab (I := I) (M := M) G K,
      MetricUnitTangentTimeSlab.time (I := I) (M := M) p = t ∧
      barrierTimeSlabQuad (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 K p < 0 := by
  obtain ⟨u, hunit, hneg_u⟩ :=
    negBarrier_unit (I := I) (M := M) G S epsilon delta t0 t x v hneg
  refine ⟨⟨(⟨t, ht⟩, (⟨x, u⟩ : TangentBundle I M)), hunit⟩, rfl, ?_⟩
  simpa using hneg_u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.negBarrier_timeSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.negBarrier_timeSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.negBarrier_timeSlab ``Submission.DifferentialGeometry.PDE.RicciFlow.negBarrier_timeSlab

omit [IsManifold I 2 M] in
theorem failure_timeSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 : Real) {K : Set Real}
    (hfail :
      ¬ TwoTensorFamilyNonnegativeOn (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G
          (twoTensorSecToFamily (I := I) (M := M) S)
          epsilon delta t0) K) :
    ∃ p : MetricUnitTangentTimeSlab (I := I) (M := M) G K,
      barrierTimeSlabQuad (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 K p < 0 := by
  classical
  unfold TwoTensorFamilyNonnegativeOn TwoTensorNonnegativeAt at hfail
  push Not at hfail
  obtain ⟨t, ht, x, v, hneg⟩ := hfail
  obtain ⟨p, _hpt, hpneg⟩ :=
    negBarrier_timeSlab (I := I) (M := M) G S epsilon delta t0 t ht x v hneg
  exact ⟨p, hpneg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.failure_timeSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.failure_timeSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.failure_timeSlab ``Submission.DifferentialGeometry.PDE.RicciFlow.failure_timeSlab

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
theorem metricUnitTimeSlab_timeVal_cont
    (G : Real -> SmoothRiemannianMetric I M) (K : Set Real) :
    Continuous (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G K =>
      MetricUnitTangentTimeSlab.time (I := I) (M := M) p) := by
  have htime :
      Continuous (fun p : MetricUnitTangentTimeSlab (I := I) (M := M) G K =>
        (p.1.1 : {t : Real // t ∈ K})) :=
    continuous_fst.comp continuous_subtype_val
  exact continuous_subtype_val.comp htime

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricUnitTimeSlab_timeVal_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricUnitTimeSlab_timeVal_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricUnitTimeSlab_timeVal_cont ``Submission.DifferentialGeometry.PDE.RicciFlow.metricUnitTimeSlab_timeVal_cont

theorem exists_left_neg_of_continuousOn
    {f : Real -> Real} {a b c : Real}
    (hab : a < b) (hbc : b ≤ c)
    (hcont : ContinuousOn f (Set.Icc a c)) (hneg : f b < 0) :
    ∃ s : Real, s ∈ Set.Icc a c ∧ s < b ∧ f s < 0 := by
  have hbmem : b ∈ Set.Icc a c := ⟨le_of_lt hab, hbc⟩
  have hpre :
      {s : Real | f s < 0} ∈ nhdsWithin b (Set.Icc a c) :=
    (hcont.continuousWithinAt hbmem).preimage_mem_nhdsWithin
      (isOpen_Iio.mem_nhds hneg)
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre with
    ⟨u, hu_nhds, hu_subset⟩
  rcases exists_Ioc_subset_of_mem_nhds' hu_nhds hab with
    ⟨l, hlb, hlu⟩
  let s : Real := (_root_.Max.max a l + b) / 2
  have hmax_lt : _root_.Max.max a l < b := max_lt hab hlb.2
  have hmax_lt_s : _root_.Max.max a l < s := by
    dsimp [s]
    linarith
  have hmax_le_s : _root_.Max.max a l ≤ s := le_of_lt hmax_lt_s
  have hs_lt : s < b := by
    dsimp [s]
    linarith
  have ha_le_s : a ≤ s := le_trans (le_max_left a l) hmax_le_s
  have hl_lt_s : l < s := lt_of_le_of_lt (le_max_right a l) hmax_lt_s
  have hs_mem_u : s ∈ u := hlu ⟨hl_lt_s, le_of_lt hs_lt⟩
  have hs_mem_Icc : s ∈ Set.Icc a c := ⟨ha_le_s, le_trans (le_of_lt hs_lt) hbc⟩
  exact ⟨s, hs_mem_Icc, hs_lt, hu_subset ⟨hs_mem_u, hs_mem_Icc⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_left_neg_of_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_left_neg_of_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_left_neg_of_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_left_neg_of_continuousOn

end

end DifferentialGeometry.PDE.RicciFlow
