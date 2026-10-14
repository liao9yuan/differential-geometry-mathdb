import Submission.DifferentialGeometry.Geometry.Coordinates.NablaComponents.Tensor0S
import Submission.DifferentialGeometry.Geometry.Coordinates.Fields.Tensor
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.FieldComponents
import Submission.DifferentialGeometry.Tensor.RSTensor.Field
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.BundleBasis
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Regularity.TensorRS
import Submission.DifferentialGeometry.Geometry.Operator.Scalar.Calculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Tensor.Multilinear
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.TensorLieDeriv
open scoped _root_.BigOperators _root_.Manifold _root_.ContDiff _root_.Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]

def coordDerivRSAt {r s : ℕ}
    (X : (x : M) -> TangentSpace I x) (x₀ : M)
    (T : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  let β₀ : Tensor0SModel r 𝕜 E :=
    (continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper
  let β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r x :=
    Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r x₀ β₀
  mvfderiv (I := I)
    (fun y : M =>
      (T y (β y))
        (fun b : Fin s => coordinateFrameAt (I := I) x₀ (lower b) y))
    x₀ (X x₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.coordDerivRSAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.coordDerivRSAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.coordDerivRSAt ``Submission.DifferentialGeometry.Tensor.Coordinates.coordDerivRSAt


def modelDerivRSAt {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (T : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  let X' : E → E := fun z =>
    tangentSpaceModelContinuousLinearEquiv z
      (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
        (fun x => X x) (Set.range I) z)
  let T' : E -> TensorRSModel r s 𝕜 E :=
    tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s x₀ T
  let β₀ : Tensor0SModel r 𝕜 E :=
    (continuousMultilinearMapBasis (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper
  (fderivWithin 𝕜 T'
      (((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I)
      (extChartAt I x₀ x₀)
      (X' (extChartAt I x₀ x₀))
    β₀)
    (fun b : Fin s => (Module.finBasis 𝕜 E) (lower b))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.modelDerivRSAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.modelDerivRSAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.modelDerivRSAt ``Submission.DifferentialGeometry.Tensor.Coordinates.modelDerivRSAt

def ModelDerivEqCoordDerivRSAt {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (T : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r s x) :
    Prop :=
  forall upper lower,
    modelDerivRSAt (I := I) X x₀ T upper lower =
      coordDerivRSAt (I := I) (fun x => X x) x₀ T upper lower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.ModelDerivEqCoordDerivRSAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.ModelDerivEqCoordDerivRSAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.ModelDerivEqCoordDerivRSAt ``Submission.DifferentialGeometry.Tensor.Coordinates.ModelDerivEqCoordDerivRSAt

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
private theorem mdifferentiableAt_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> 𝕜) {x : M}
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x) :
    MDifferentiableAt I 𝓘(𝕜, 𝕜) (t.sum f) x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      change MDifferentiableAt I 𝓘(𝕜, 𝕜) (fun _ : M => (0 : 𝕜)) x
      exact mdifferentiableAt_const
        (I := I) (I' := 𝓘(𝕜, 𝕜)) (c := (0 : 𝕜)) (x := x)
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(𝕜, 𝕜) (t.sum f) x := ih hft
      have hadd : MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i + t.sum f) x := hfi.add hsum
      simpa [Finset.sum_insert, hit] using hadd

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Coordinates.mdifferentiableAt_finset_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Coordinates.mdifferentiableAt_finset_sum target :: scope.openDecls } }

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
theorem mvfderiv_finset_sum
    {ι : Type*} (t : Finset ι) (f : ι -> M -> 𝕜)
    {x : M} (v : TangentSpace I x)
    (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x) :
    mvfderiv (I := I) (t.sum f) x v =
      t.sum (fun i => mvfderiv (I := I) (f i) x v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp
  | insert i t hit ih =>
      have hfi : MDifferentiableAt I 𝓘(𝕜, 𝕜) (f i) x := hf i (by simp [hit])
      have hft : ∀ j ∈ t, MDifferentiableAt I 𝓘(𝕜, 𝕜) (f j) x := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : MDifferentiableAt I 𝓘(𝕜, 𝕜) (t.sum f) x := by
        exact mdifferentiableAt_finset_sum (I := I) t f hft
      calc
        mvfderiv (I := I) ((_root_.Insert.insert i t).sum f) x v
            = mvfderiv (I := I)
                (f i + t.sum f) x v := by
              simp [Finset.sum_insert, hit]
        _ = mvfderiv (I := I) (f i) x v +
              mvfderiv (I := I) (t.sum f) x v := by
              have hadd := congr($(mvfderiv_add
                (I := I) (g := f i) (g' := t.sum f)
                (x := x) hfi hsum) v)
              simpa [Pi.add_apply] using hadd
        _ = (_root_.Insert.insert i t).sum (fun j => mvfderiv (I := I) (f j) x v) := by
              rw [ih hft]
              simp [Finset.sum_insert, hit]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.mvfderiv_finset_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.mvfderiv_finset_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.mvfderiv_finset_sum ``Submission.DifferentialGeometry.Tensor.Coordinates.mvfderiv_finset_sum

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
theorem mvfderiv_mul
    {f g : M -> 𝕜} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(𝕜, 𝕜) f x)
    (hg : MDifferentiableAt I 𝓘(𝕜, 𝕜) g x) :
    mvfderiv (I := I) (fun y : M => f y * g y) x v =
      f x * mvfderiv (I := I) g x v +
        mvfderiv (I := I) f x v * g x := by
  change mvfderiv (I := I) (f * g) x v =
      f x * mvfderiv (I := I) g x v +
        mvfderiv (I := I) f x v * g x
  have hprod := congr($(_root_.mvfderiv_mul (I := I) hf hg) v)
  simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hprod

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.mvfderiv_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.mvfderiv_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.mvfderiv_mul ``Submission.DifferentialGeometry.Tensor.Coordinates.mvfderiv_mul

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
theorem mvfderiv_congr_eventually
    {f g : M -> 𝕜} {x : M} (v : TangentSpace I x)
    (h : f =ᶠ[𝓝 x] g) :
    mvfderiv (I := I) f x v = mvfderiv (I := I) g x v := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(𝕜, 𝕜)) h
  have hx : f x = g x := h.eq_of_nhds
  unfold mvfderiv
  rw [hmf, hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.mvfderiv_congr_eventually then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.mvfderiv_congr_eventually"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.mvfderiv_congr_eventually ``Submission.DifferentialGeometry.Tensor.Coordinates.mvfderiv_congr_eventually

end DifferentialGeometry.Tensor.Coordinates
