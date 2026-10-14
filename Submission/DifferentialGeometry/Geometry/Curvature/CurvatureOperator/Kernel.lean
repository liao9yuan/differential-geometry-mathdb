import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import Submission.DifferentialGeometry.Tensor.RSTensor.Algebra.Product
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import Submission.DifferentialGeometry.Tensor.Alternating.Bundle.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

def twoFormTensorAt {x : M}
    (a : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    Tensor0SSpace 2 I x :=
  a.toContinuousMultilinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.twoFormTensorAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.twoFormTensorAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.twoFormTensorAt ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormTensorAt

omit [FiniteDimensional Real E] [CompleteSpace E] [T2Space M] in
@[simp] theorem twoFormTensorAt_apply {x : M}
    (a : TangentSpace I x [⋀^Fin 2]→L[Real] Real)
    (v : Fin 2 -> TangentSpace I x) :
    twoFormTensorAt (I := I) a v = a v :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.twoFormTensorAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.twoFormTensorAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.twoFormTensorAt_apply ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormTensorAt_apply

def curvatureOperatorPairingAt (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (a b : TangentSpace I x [⋀^Fin 2]→L[Real] Real) : Real :=
  -(1 / 2 : Real) * inner0S (I := I) g x 4 (A : Tensor04At (I := I) (M := M) x)
    (Tensor0SSpace.product (twoFormTensorAt (I := I) a) (twoFormTensorAt (I := I) b))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt

omit [FiniteDimensional Real E] [CompleteSpace E] [T2Space M] in
private theorem twoFormTensorProduct_zero_left {x : M}
    (b : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    Tensor0SSpace.product (twoFormTensorAt (I := I)
        (0 : TangentSpace I x [⋀^Fin 2]→L[Real] Real))
        (twoFormTensorAt (I := I) b) = 0 := by
  apply tensor0SSpace_ext 4 x
  intro v
  rw [Tensor0SSpace.product_apply]
  change (0 : TangentSpace I x [⋀^Fin 2]→L[Real] Real)
      (v ∘ Fin.castAdd 2) * b (v ∘ Fin.natAdd 2) = 0
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormTensorProduct_zero_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.twoFormTensorProduct_zero_left target :: scope.openDecls } }

omit [FiniteDimensional Real E] [CompleteSpace E] [T2Space M] in
private theorem twoFormTensorProduct_add_left {x : M}
    (a b c : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    Tensor0SSpace.product (twoFormTensorAt (I := I) (a + b))
        (twoFormTensorAt (I := I) c) =
      Tensor0SSpace.product (twoFormTensorAt (I := I) a) (twoFormTensorAt (I := I) c) +
        Tensor0SSpace.product (twoFormTensorAt (I := I) b) (twoFormTensorAt (I := I) c) := by
  apply tensor0SSpace_ext 4 x
  intro v
  rw [Tensor0SSpace.product_apply]
  change (a + b) (v ∘ Fin.castAdd 2) * c (v ∘ Fin.natAdd 2) = _
  rw [Tensor0SSpace.add_apply, Tensor0SSpace.product_apply,
    Tensor0SSpace.product_apply]
  change (a (v ∘ Fin.castAdd 2) + b (v ∘ Fin.castAdd 2)) *
      c (v ∘ Fin.natAdd 2) =
    a (v ∘ Fin.castAdd 2) * c (v ∘ Fin.natAdd 2) +
      b (v ∘ Fin.castAdd 2) * c (v ∘ Fin.natAdd 2)
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormTensorProduct_add_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.twoFormTensorProduct_add_left target :: scope.openDecls } }

omit [FiniteDimensional Real E] [CompleteSpace E] [T2Space M] in
private theorem twoFormTensorProduct_smul_left {x : M}
    (c : Real) (a b : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    Tensor0SSpace.product (twoFormTensorAt (I := I) (c • a))
        (twoFormTensorAt (I := I) b) =
      c • Tensor0SSpace.product (twoFormTensorAt (I := I) a)
        (twoFormTensorAt (I := I) b) := by
  apply tensor0SSpace_ext 4 x
  intro v
  rw [Tensor0SSpace.product_apply]
  change (c • a) (v ∘ Fin.castAdd 2) * b (v ∘ Fin.natAdd 2) = _
  rw [Tensor0SSpace.smul_apply, Tensor0SSpace.product_apply]
  change (c * a (v ∘ Fin.castAdd 2)) * b (v ∘ Fin.natAdd 2) =
    c * (a (v ∘ Fin.castAdd 2) * b (v ∘ Fin.natAdd 2))
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormTensorProduct_smul_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.twoFormTensorProduct_smul_left target :: scope.openDecls } }

omit [CompleteSpace E] [T2Space M] in
@[simp] theorem curvatureOperatorPairingAt_zero_left
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (b : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    curvatureOperatorPairingAt (I := I) g x A 0 b = 0 := by
  rw [curvatureOperatorPairingAt, twoFormTensorProduct_zero_left]
  simp [inner0S, MetricFiberData.inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_zero_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_zero_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_zero_left ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_zero_left

omit [CompleteSpace E] [T2Space M] in
theorem curvatureOperatorPairingAt_add_left
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (a b c : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    curvatureOperatorPairingAt (I := I) g x A (a + b) c =
      curvatureOperatorPairingAt (I := I) g x A a c +
        curvatureOperatorPairingAt (I := I) g x A b c := by
  rw [curvatureOperatorPairingAt, twoFormTensorProduct_add_left, inner0S_add_right]
  unfold curvatureOperatorPairingAt
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_add_left ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_add_left

omit [CompleteSpace E] [T2Space M] in
theorem curvatureOperatorPairingAt_smul_left
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (c : Real) (a b : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    curvatureOperatorPairingAt (I := I) g x A (c • a) b =
      c * curvatureOperatorPairingAt (I := I) g x A a b := by
  rw [curvatureOperatorPairingAt, twoFormTensorProduct_smul_left]
  rw [Tensor0SBundle.inner0S_smul_right]
  unfold curvatureOperatorPairingAt
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_smul_left ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_smul_left

omit [FiniteDimensional Real E] [CompleteSpace E] [T2Space M] in
private theorem twoFormTensorProduct_zero_right {x : M}
    (a : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    Tensor0SSpace.product (twoFormTensorAt (I := I) a)
        (twoFormTensorAt (I := I)
          (0 : TangentSpace I x [⋀^Fin 2]→L[Real] Real)) = 0 := by
  apply tensor0SSpace_ext 4 x
  intro v
  rw [Tensor0SSpace.product_apply]
  change a (v ∘ Fin.castAdd 2) *
      (0 : TangentSpace I x [⋀^Fin 2]→L[Real] Real) (v ∘ Fin.natAdd 2) = 0
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormTensorProduct_zero_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.twoFormTensorProduct_zero_right target :: scope.openDecls } }

omit [FiniteDimensional Real E] [CompleteSpace E] [T2Space M] in
private theorem twoFormTensorProduct_add_right {x : M}
    (a b c : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    Tensor0SSpace.product (twoFormTensorAt (I := I) a)
        (twoFormTensorAt (I := I) (b + c)) =
      Tensor0SSpace.product (twoFormTensorAt (I := I) a) (twoFormTensorAt (I := I) b) +
        Tensor0SSpace.product (twoFormTensorAt (I := I) a) (twoFormTensorAt (I := I) c) := by
  apply tensor0SSpace_ext 4 x
  intro v
  rw [Tensor0SSpace.product_apply]
  change a (v ∘ Fin.castAdd 2) * (b + c) (v ∘ Fin.natAdd 2) = _
  rw [Tensor0SSpace.add_apply, Tensor0SSpace.product_apply,
    Tensor0SSpace.product_apply]
  change a (v ∘ Fin.castAdd 2) *
      (b (v ∘ Fin.natAdd 2) + c (v ∘ Fin.natAdd 2)) =
    a (v ∘ Fin.castAdd 2) * b (v ∘ Fin.natAdd 2) +
      a (v ∘ Fin.castAdd 2) * c (v ∘ Fin.natAdd 2)
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormTensorProduct_add_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.twoFormTensorProduct_add_right target :: scope.openDecls } }

omit [FiniteDimensional Real E] [CompleteSpace E] [T2Space M] in
private theorem twoFormTensorProduct_smul_right {x : M}
    (c : Real) (a b : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    Tensor0SSpace.product (twoFormTensorAt (I := I) a)
        (twoFormTensorAt (I := I) (c • b)) =
      c • Tensor0SSpace.product (twoFormTensorAt (I := I) a)
        (twoFormTensorAt (I := I) b) := by
  apply tensor0SSpace_ext 4 x
  intro v
  rw [Tensor0SSpace.product_apply]
  change a (v ∘ Fin.castAdd 2) * (c • b) (v ∘ Fin.natAdd 2) = _
  rw [Tensor0SSpace.smul_apply, Tensor0SSpace.product_apply]
  change a (v ∘ Fin.castAdd 2) * (c * b (v ∘ Fin.natAdd 2)) =
    c * (a (v ∘ Fin.castAdd 2) * b (v ∘ Fin.natAdd 2))
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormTensorProduct_smul_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.twoFormTensorProduct_smul_right target :: scope.openDecls } }

omit [CompleteSpace E] [T2Space M] in
@[simp] theorem curvatureOperatorPairingAt_zero_right
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (a : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    curvatureOperatorPairingAt (I := I) g x A a 0 = 0 := by
  rw [curvatureOperatorPairingAt, twoFormTensorProduct_zero_right]
  simp [inner0S, MetricFiberData.inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_zero_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_zero_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_zero_right ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_zero_right

omit [CompleteSpace E] [T2Space M] in
theorem curvatureOperatorPairingAt_add_right
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (a b c : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    curvatureOperatorPairingAt (I := I) g x A a (b + c) =
      curvatureOperatorPairingAt (I := I) g x A a b +
        curvatureOperatorPairingAt (I := I) g x A a c := by
  rw [curvatureOperatorPairingAt, twoFormTensorProduct_add_right, inner0S_add_right]
  unfold curvatureOperatorPairingAt
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_add_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_add_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_add_right ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_add_right

omit [CompleteSpace E] [T2Space M] in
theorem curvatureOperatorPairingAt_smul_right
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (c : Real) (a b : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    curvatureOperatorPairingAt (I := I) g x A a (c • b) =
      c * curvatureOperatorPairingAt (I := I) g x A a b := by
  rw [curvatureOperatorPairingAt, twoFormTensorProduct_smul_right]
  rw [Tensor0SBundle.inner0S_smul_right]
  unfold curvatureOperatorPairingAt
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_smul_right ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_smul_right

def curvatureOperatorPairingRightAt (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (a : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    (TangentSpace I x [⋀^Fin 2]→L[Real] Real) →ₗ[Real] Real where
  toFun := curvatureOperatorPairingAt (I := I) g x A a
  map_add' := curvatureOperatorPairingAt_add_right (I := I) g x A a
  map_smul' := by
    intro c b
    simpa [smul_eq_mul] using curvatureOperatorPairingAt_smul_right
      (I := I) g x A c a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingRightAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingRightAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingRightAt ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingRightAt

omit [CompleteSpace E] [T2Space M] in
@[simp] theorem curvatureOperatorPairingRightAt_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (a b : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    curvatureOperatorPairingRightAt (I := I) g x A a b =
      curvatureOperatorPairingAt (I := I) g x A a b :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingRightAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingRightAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingRightAt_apply ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingRightAt_apply

def curvatureOperatorKernelAt (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    Submodule Real (TangentSpace I x [⋀^Fin 2]→L[Real] Real) where
  carrier := {a | ∀ b, curvatureOperatorPairingAt (I := I) g x A a b = 0}
  zero_mem' := curvatureOperatorPairingAt_zero_left (I := I) g x A
  add_mem' := by
    intro a b ha hb c
    rw [curvatureOperatorPairingAt_add_left, ha c, hb c, add_zero]
  smul_mem' := by
    intro c a ha b
    rw [curvatureOperatorPairingAt_smul_left, ha b, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorKernelAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorKernelAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorKernelAt ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorKernelAt

omit [CompleteSpace E] [T2Space M] in
@[simp] theorem curvatureOperatorKernelAt_zero
    (g : SmoothRiemannianMetric I M) (x : M) :
    curvatureOperatorKernelAt (I := I) g x
        (0 : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) = ⊤ := by
  ext a
  simp only [Submodule.mem_top, iff_true]
  intro b
  simp [curvatureOperatorPairingAt, inner0S, MetricFiberData.inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorKernelAt_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorKernelAt_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorKernelAt_zero ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorKernelAt_zero

end DifferentialGeometry.Geometry.Curvature
