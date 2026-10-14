import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Kernel
import Submission.DifferentialGeometry.Tensor.Alternating.Coordinates.Basis
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricCongr

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

noncomputable local instance twoFormFiniteDimensional (x : M) :
    FiniteDimensional Real
      (TangentSpace I x [⋀^Fin 2]→L[Real] Real) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
    (Module.finBasis Real (TangentSpace I x))).finiteDimensional_of_finite

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.twoFormFiniteDimensional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.twoFormFiniteDimensional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.twoFormFiniteDimensional ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormFiniteDimensional

def twoFormTensorLinearAt {x : M} :
    (TangentSpace I x [⋀^Fin 2]→L[Real] Real) →ₗ[Real]
      Tensor0SSpace 2 I x where
  toFun := twoFormTensorAt (I := I)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.twoFormTensorLinearAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.twoFormTensorLinearAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.twoFormTensorLinearAt ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormTensorLinearAt

omit [FiniteDimensional Real E] [CompleteSpace E] [T2Space M] in
@[simp] theorem twoFormTensorLinearAt_apply {x : M}
    (a : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    twoFormTensorLinearAt (I := I) a = twoFormTensorAt (I := I) a :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.twoFormTensorLinearAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.twoFormTensorLinearAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.twoFormTensorLinearAt_apply ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormTensorLinearAt_apply

def twoFormFlatLinearAt (g : SmoothRiemannianMetric I M) (x : M) :
    (TangentSpace I x [⋀^Fin 2]→L[Real] Real) →ₗ[Real]
      Module.Dual Real (TangentSpace I x [⋀^Fin 2]→L[Real] Real) :=
  (twoFormTensorLinearAt (I := I) (x := x)).dualMap.comp
    ((flat0S (I := I) g x 2).toLinearMap.comp
      (twoFormTensorLinearAt (I := I) (x := x)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.twoFormFlatLinearAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.twoFormFlatLinearAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.twoFormFlatLinearAt ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormFlatLinearAt

omit [CompleteSpace E] [T2Space M] in
@[simp] theorem twoFormFlatLinearAt_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (a b : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    twoFormFlatLinearAt (I := I) g x a b =
      inner0S (I := I) g x 2
        (twoFormTensorAt (I := I) a) (twoFormTensorAt (I := I) b) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.twoFormFlatLinearAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.twoFormFlatLinearAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.twoFormFlatLinearAt_apply ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormFlatLinearAt_apply

omit [CompleteSpace E] [T2Space M] in
theorem twoFormFlatLinearAt_injective
    (g : SmoothRiemannianMetric I M) (x : M) :
    Function.Injective (twoFormFlatLinearAt (I := I) g x) := by
  intro a b hab
  have hzero : inner0S (I := I) g x 2
      (twoFormTensorAt (I := I) (a - b))
      (twoFormTensorAt (I := I) (a - b)) = 0 := by
    have hflat : twoFormFlatLinearAt (I := I) g x (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    have happly := congrArg
      (fun f : Module.Dual Real
          (TangentSpace I x [⋀^Fin 2]→L[Real] Real) => f (a - b)) hflat
    simpa only [twoFormFlatLinearAt_apply, LinearMap.zero_apply] using happly
  have htensor : twoFormTensorAt (I := I) (a - b) = 0 :=
    ((tensor0SMetricData (I := I) g x 2).inner_self_eq_zero_iff _).mp hzero
  have hform : a - b = 0 := by
    apply ContinuousAlternatingMap.ext
    intro v
    have h := congrArg (fun T : Tensor0SSpace 2 I x => T v) htensor
    simpa using h
  exact sub_eq_zero.mp hform

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.twoFormFlatLinearAt_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.twoFormFlatLinearAt_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.twoFormFlatLinearAt_injective ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormFlatLinearAt_injective

def twoFormMetricData (g : SmoothRiemannianMetric I M) (x : M) :
    MetricFiberData (TangentSpace I x [⋀^Fin 2]→L[Real] Real) :=
  MetricFiberData.ofFlat
    (twoFormFlatLinearAt (I := I) g x)
    (twoFormFlatLinearAt_injective (I := I) g x)
    (fun a b => inner0S_symm (I := I) g x
      (twoFormTensorAt (I := I) a) (twoFormTensorAt (I := I) b))
    (fun a => (tensor0SMetricData (I := I) g x 2).inner_nonneg
      (twoFormTensorAt (I := I) a))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.twoFormMetricData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.twoFormMetricData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.twoFormMetricData ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormMetricData

omit [CompleteSpace E] [T2Space M] in
@[simp] theorem twoFormMetricData_inner
    (g : SmoothRiemannianMetric I M) (x : M)
    (a b : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    (twoFormMetricData (I := I) g x).inner a b =
      inner0S (I := I) g x 2
        (twoFormTensorAt (I := I) a) (twoFormTensorAt (I := I) b) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.twoFormMetricData_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.twoFormMetricData_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.twoFormMetricData_inner ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormMetricData_inner

def curvatureOperatorBilinearAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (TangentSpace I x [⋀^Fin 2]→L[Real] Real) →ₗ[Real]
      Module.Dual Real (TangentSpace I x [⋀^Fin 2]→L[Real] Real) where
  toFun := curvatureOperatorPairingRightAt (I := I) g x A
  map_add' a b := by
    ext c
    exact curvatureOperatorPairingAt_add_left (I := I) g x A a b c
  map_smul' r a := by
    ext b
    exact curvatureOperatorPairingAt_smul_left (I := I) g x A r a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorBilinearAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorBilinearAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorBilinearAt ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorBilinearAt

omit [CompleteSpace E] [T2Space M] in
@[simp] theorem curvatureOperatorBilinearAt_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (a b : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    curvatureOperatorBilinearAt (I := I) g x A a b =
      curvatureOperatorPairingAt (I := I) g x A a b :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorBilinearAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorBilinearAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorBilinearAt_apply ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorBilinearAt_apply

private def curvaturePairSwap : Fin 4 ≃ Fin 4 where
  toFun i := if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 0 else 1
  invFun i := if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 0 else 1
  left_inv i := by fin_cases i <;> simp
  right_inv i := by fin_cases i <;> simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.curvaturePairSwap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.curvaturePairSwap target :: scope.openDecls } }

omit [FiniteDimensional Real E] [CompleteSpace E] [T2Space M] in
private theorem algebraicCurvatureTensor_domDomCongr_curvaturePairSwap
    {x : M}
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (A : Tensor04At (I := I) (M := M) x).domDomCongr curvaturePairSwap = A := by
  apply tensor0SSpace_ext 4 x
  intro v
  rw [Tensor0SSpace.domDomCongr_apply]
  have hpair := tensor04StandardAt_pair_swap_of_mem_algebraicCurvatureTensorSubmodule
    A.2 (v 0) (v 1) (v 2) (v 3)
  change (A : Tensor04At (I := I) (M := M) x)
      (fun i => v (curvaturePairSwap i)) =
    (A : Tensor04At (I := I) (M := M) x) v
  have hswap : (fun i => v (curvaturePairSwap i)) =
      vec4 (v 2) (v 3) (v 0) (v 1) := by
    funext i
    fin_cases i <;> simp [curvaturePairSwap, vec4]
  have hv : v = vec4 (v 0) (v 1) (v 2) (v 3) := by
    funext i
    fin_cases i <;> simp [vec4]
  rw [hswap, hv]
  exact hpair.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensor_domDomCongr_curvaturePairSwap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensor_domDomCongr_curvaturePairSwap target :: scope.openDecls } }

omit [FiniteDimensional Real E] [CompleteSpace E] [T2Space M] in
private theorem twoFormTensorProduct_domDomCongr_curvaturePairSwap
    {x : M}
    (a b : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    (Tensor0SSpace.product (twoFormTensorAt (I := I) a)
        (twoFormTensorAt (I := I) b)).domDomCongr curvaturePairSwap =
      Tensor0SSpace.product (twoFormTensorAt (I := I) b)
        (twoFormTensorAt (I := I) a) := by
  apply tensor0SSpace_ext 4 x
  intro v
  rw [Tensor0SSpace.domDomCongr_apply, Tensor0SSpace.product_apply,
    Tensor0SSpace.product_apply]
  have hfirst :
      ((fun i => v (curvaturePairSwap i)) ∘ Fin.castAdd 2) =
        v ∘ Fin.natAdd 2 := by
    funext i
    fin_cases i <;> simp [curvaturePairSwap]
  have hlast :
      ((fun i => v (curvaturePairSwap i)) ∘ Fin.natAdd 2) =
        v ∘ Fin.castAdd 2 := by
    funext i
    fin_cases i <;> simp [curvaturePairSwap]
  rw [hfirst, hlast]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormTensorProduct_domDomCongr_curvaturePairSwap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.twoFormTensorProduct_domDomCongr_curvaturePairSwap target :: scope.openDecls } }

omit [CompleteSpace E] [T2Space M] in
private theorem inner0S_domDomCongr_curvaturePairSwap
    (g : SmoothRiemannianMetric I M) (x : M)
    (A B : Tensor0SSpace 4 I x) :
    inner0S (I := I) g x 4 (A.domDomCongr curvaturePairSwap)
        (B.domDomCongr curvaturePairSwap) =
      inner0S (I := I) g x 4 A B := by
  let addV : AddCommGroup (TangentSpace I x) := inferInstance
  let modV : Module Real (TangentSpace I x) := inferInstance
  let D := (tangentMetricData (I := I) g x).metric
  let : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ addV modV D.toCore
  let : AddCommGroup (TangentSpace I x) := addV
  let : Module Real (TangentSpace I x) := modV
  let : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let basis := stdOrthonormalBasis Real (TangentSpace I x)
  have horth : ∀ i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0 := by
    intro i j
    change D.inner (basis i) (basis j) = if i = j then (1 : Real) else 0
    rw [← D.toCore_inner]
    exact basis.inner_eq_ite i j
  have hinv := metricInverseInBasis_identity_of_orthonormal
    (I := I) g basis.toBasis horth
  exact Tensor0SBundle.inner0S_domDomCongr
    (I := I) g x basis.toBasis hinv curvaturePairSwap A B

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.inner0S_domDomCongr_curvaturePairSwap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.inner0S_domDomCongr_curvaturePairSwap target :: scope.openDecls } }

omit [CompleteSpace E] [T2Space M] in
theorem curvatureOperatorPairingAt_comm
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (a b : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    curvatureOperatorPairingAt (I := I) g x A a b =
      curvatureOperatorPairingAt (I := I) g x A b a := by
  have hinner := inner0S_domDomCongr_curvaturePairSwap
    (I := I) g x (A : Tensor04At (I := I) (M := M) x)
      (Tensor0SSpace.product (twoFormTensorAt (I := I) a)
        (twoFormTensorAt (I := I) b))
  rw [algebraicCurvatureTensor_domDomCongr_curvaturePairSwap,
    twoFormTensorProduct_domDomCongr_curvaturePairSwap] at hinner
  unfold curvatureOperatorPairingAt
  rw [hinner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_comm ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorPairingAt_comm

def curvatureOperatorEndomorphismAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (TangentSpace I x [⋀^Fin 2]→L[Real] Real) →L[Real]
      TangentSpace I x [⋀^Fin 2]→L[Real] Real :=
  LinearMap.toContinuousLinearMap
    ((twoFormMetricData (I := I) g x).sharp.toLinearMap.comp
      (curvatureOperatorBilinearAt (I := I) g x A))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt

omit [CompleteSpace E] [T2Space M] in
theorem twoFormMetricData_inner_curvatureOperatorEndomorphismAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (a b : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    (twoFormMetricData (I := I) g x).inner
        (curvatureOperatorEndomorphismAt (I := I) g x A a) b =
      curvatureOperatorPairingAt (I := I) g x A a b := by
  change (twoFormMetricData (I := I) g x).flat
      ((twoFormMetricData (I := I) g x).flat.symm
        (curvatureOperatorBilinearAt (I := I) g x A a)) b = _
  rw [(twoFormMetricData (I := I) g x).flat.apply_symm_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.twoFormMetricData_inner_curvatureOperatorEndomorphismAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.twoFormMetricData_inner_curvatureOperatorEndomorphismAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.twoFormMetricData_inner_curvatureOperatorEndomorphismAt ``Submission.DifferentialGeometry.Geometry.Curvature.twoFormMetricData_inner_curvatureOperatorEndomorphismAt

omit [CompleteSpace E] [T2Space M] in
theorem curvatureOperatorEndomorphismAt_isSymmetric
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (twoFormMetricData (I := I) g x).IsSymmetric
      (curvatureOperatorEndomorphismAt (I := I) g x A).toLinearMap := by
  intro a b
  calc
    (twoFormMetricData (I := I) g x).inner
        ((curvatureOperatorEndomorphismAt (I := I) g x A).toLinearMap a) b =
      curvatureOperatorPairingAt (I := I) g x A a b := by
        exact twoFormMetricData_inner_curvatureOperatorEndomorphismAt
          (I := I) g x A a b
    _ = curvatureOperatorPairingAt (I := I) g x A b a :=
      curvatureOperatorPairingAt_comm (I := I) g x A a b
    _ = (twoFormMetricData (I := I) g x).inner
        ((curvatureOperatorEndomorphismAt (I := I) g x A).toLinearMap b) a := by
          exact (twoFormMetricData_inner_curvatureOperatorEndomorphismAt
            (I := I) g x A b a).symm
    _ = (twoFormMetricData (I := I) g x).inner a
        ((curvatureOperatorEndomorphismAt (I := I) g x A).toLinearMap b) :=
      (twoFormMetricData (I := I) g x).inner_comm _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt_isSymmetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt_isSymmetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt_isSymmetric ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt_isSymmetric

omit [CompleteSpace E] [T2Space M] in
theorem curvatureOperatorEndomorphismAt_ker
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (curvatureOperatorEndomorphismAt (I := I) g x A).ker =
      curvatureOperatorKernelAt (I := I) g x A := by
  ext a
  constructor
  · intro ha b
    rw [← twoFormMetricData_inner_curvatureOperatorEndomorphismAt]
    have ha0 : curvatureOperatorEndomorphismAt (I := I) g x A a = 0 :=
      LinearMap.mem_ker.mp ha
    rw [ha0]
    simp [MetricFiberData.inner]
  · intro ha
    apply LinearMap.mem_ker.mpr
    apply (twoFormMetricData (I := I) g x).flat.injective
    ext b
    change (twoFormMetricData (I := I) g x).inner
        (curvatureOperatorEndomorphismAt (I := I) g x A a) b =
      (twoFormMetricData (I := I) g x).inner 0 b
    rw [twoFormMetricData_inner_curvatureOperatorEndomorphismAt, ha b]
    simp [MetricFiberData.inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt_ker then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt_ker"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt_ker ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorEndomorphismAt_ker

def curvatureOperatorImageAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    Submodule Real (TangentSpace I x [⋀^Fin 2]→L[Real] Real) :=
  (curvatureOperatorEndomorphismAt (I := I) g x A).range

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt

omit [CompleteSpace E] [T2Space M] in
@[simp] theorem curvatureOperatorImageAt_eq_range
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    curvatureOperatorImageAt (I := I) g x A =
      (curvatureOperatorEndomorphismAt (I := I) g x A).range :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt_eq_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt_eq_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt_eq_range ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt_eq_range

omit [CompleteSpace E] [T2Space M] in
theorem curvatureOperatorImageAt_eq_orthogonal_kernel
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    curvatureOperatorImageAt (I := I) g x A =
      (twoFormMetricData (I := I) g x).orthogonal
        (curvatureOperatorKernelAt (I := I) g x A) := by
  rw [curvatureOperatorImageAt_eq_range, ← curvatureOperatorEndomorphismAt_ker]
  exact (curvatureOperatorEndomorphismAt_isSymmetric (I := I) g x A).range_eq_orthogonal_ker

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt_eq_orthogonal_kernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt_eq_orthogonal_kernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt_eq_orthogonal_kernel ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorImageAt_eq_orthogonal_kernel

end DifferentialGeometry.Geometry.Curvature
