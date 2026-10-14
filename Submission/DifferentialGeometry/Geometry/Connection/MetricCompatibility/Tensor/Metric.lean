import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Defs
import Submission.DifferentialGeometry.Geometry.Metric.RiemannianMetricTensor
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.Expansion
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Basic
import Submission.DifferentialGeometry.Bundle.Section
import Submission.DifferentialGeometry.Bundle.PartialMfderiv.Basic
import Submission.DifferentialGeometry.Bundle.PartialMfderiv.ModelMixed
import Submission.DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor

set_option autoImplicit false

namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section


open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def metricTensorField
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 := by
  let gInf : Bundle.ContMDiffRiemannianMetric I (∞ : WithTop ℕ∞) E
      (TangentSpace I : M -> Type _) :=
    { inner := Bundle.ContMDiffRiemannianMetric.inner g
      symm := g.symm
      pos := g.pos
      isVonNBounded := g.isVonNBounded
      contMDiff := g.contMDiff.of_le (by simp) }
  exact gInf.toTensor0S (I := I) (M := M) (n := (∞ : WithTop ℕ∞))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.metricTensorField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.metricTensorField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.metricTensorField ``Submission.DifferentialGeometry.Tensor0SBundle.metricTensorField

@[simp]
theorem metricTensorField_apply
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 -> TangentSpace I x) :
    metricTensorField (I := I) g x v = g.inner x (v 0) (v 1) := by
  simp [metricTensorField]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.metricTensorField_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.metricTensorField_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.metricTensorField_apply ``Submission.DifferentialGeometry.Tensor0SBundle.metricTensorField_apply

@[simp]
theorem metricTensorField_eval
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.eval (metricTensorField (I := I) g x) v = g.inner x (v 0) (v 1) := by
  exact metricTensorField_apply g x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.metricTensorField_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.metricTensorField_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.metricTensorField_eval ``Submission.DifferentialGeometry.Tensor0SBundle.metricTensorField_eval

theorem nabla_metric_eval
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 cov X
      (metricTensorField (I := I) g) x)
        (fun a : Fin 2 => V a x) = 0 := by
  classical
  let A : Real :=
    g.inner x ((cov (fun y : M => V 0 y) x) (X x)) (V 1 x)
  let B : Real :=
    g.inner x (V 0 x) ((cov (fun y : M => V 1 y) x) (X x))
  have hV0 : MDiffAt (T% (fun y : M => V 0 y)) x :=
    (V 0).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hV1 : MDiffAt (T% (fun y : M => V 1 y)) x :=
    (V 1).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hmc_apply :=
    DifferentialGeometry.Geometry.Connection.IsMetricCompatible.mvfderiv_inner (I := I) hmc
      (X x) hV0 hV1
  have hderiv :
      mvfderiv (I := I)
          (fun p : M =>
            metricTensorField (I := I) g p (fun a : Fin 2 => V a p))
          x (X x) = A + B := by
    have hderiv' :
        mvfderiv (I := I)
            (fun p : M => g.inner p (V 0 p) (V 1 p)) x (X x) = A + B := by
      simpa [A, B] using hmc_apply
    simpa using hderiv'
  have hsum :
      (∑ a : Fin 2,
        metricTensorField (I := I) g x
          (Function.update (fun b : Fin 2 => V b x) a
            ((cov (fun p : M => V a p) x) (X x)))) = A + B := by
    rw [Fin.sum_univ_two]
    simp [A, B]
  have heval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov X V
      (metricTensorField (I := I) g) x
  rw [heval, hsum, hderiv]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.nabla_metric_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.nabla_metric_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.nabla_metric_eval ``Submission.DifferentialGeometry.Tensor0SBundle.nabla_metric_eval

theorem nabla_metric_zero
    [T2Space M] [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 cov X
      (metricTensorField (I := I) g) x = 0 := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro slots
  let V : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (slots a))).choose
  have hV : ∀ a : Fin 2, V a x = basis (slots a) := by
    intro a
    exact
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (slots a))).choose_spec
  have hzero := nabla_metric_eval (I := I) cov g hmc X V x
  simp only [component0S_apply]
  convert hzero using 2
  · ext a
    exact (hV a).symm
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.nabla_metric_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.nabla_metric_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.nabla_metric_zero ``Submission.DifferentialGeometry.Tensor0SBundle.nabla_metric_zero

theorem nabla_zero
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov X
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) s) x = 0 := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro slots
  let V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (slots a))).choose
  have hV : ∀ a : Fin s, V a x = basis (slots a) := by
    intro a
    exact
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (slots a))).choose_spec
  have hzero :
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov X
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) s) x)
          (fun a : Fin s => V a x) = 0 := by
    have heval :=
      nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) cov X V
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) s) x
    rw [heval]
    change mvfderiv (I := I) (fun _ : M => (0 : Real)) x (X x) -
      ∑ _ : Fin s, (0 : Real) = 0
    simp [mvfderiv]
  simp only [component0S_apply]
  convert hzero using 2
  · ext a
    exact (hV a).symm
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.nabla_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.nabla_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.nabla_zero ``Submission.DifferentialGeometry.Tensor0SBundle.nabla_zero

theorem zero_realizes_nabla
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _)) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) s)
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + 1)) := by
  intro X x slots
  rw [nabla_zero (I := I) s cov X x]
  change (0 : Real) = 0
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.zero_realizes_nabla then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.zero_realizes_nabla"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.zero_realizes_nabla ``Submission.DifferentialGeometry.Tensor0SBundle.zero_realizes_nabla

theorem zero_realizes_metric
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov (metricTensorField (I := I) g)
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3) := by
  intro X x slots
  rw [nabla_metric_zero (I := I) cov g hmc X x]
  change (0 : Real) = 0
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.zero_realizes_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.zero_realizes_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.zero_realizes_metric ``Submission.DifferentialGeometry.Tensor0SBundle.zero_realizes_metric

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem mvfderiv_mul_real
    {f h : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    mvfderiv (I := I) (fun y : M => f y * h y) x v =
      f x * mvfderiv (I := I) h x v +
        mvfderiv (I := I) f x v * h x := by
  have hfun : (fun y : M => f y * h y) = f * h := by
    funext y
    rfl
  rw [hfun]
  have hprod := congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v)
    (mvfderiv_mul (I := I) hf hh)
  simpa only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, mul_comm] using hprod

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor0SBundle.mvfderiv_mul_real
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor0SBundle.mvfderiv_mul_real target :: scope.openDecls } }

theorem nabla_smul_metric
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (f : M -> Real)
    (hf : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞) f)
    (df : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1)
    (hdf : ∀ x : M, ∀ v : TangentSpace I x,
      df x (fun _ : Fin 1 => v) = mvfderiv (I := I) f x v) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov
      (tensor0SFieldSmulByFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
        f hf (metricTensorField (I := I) g))
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
        df (metricTensorField (I := I) g)) := by
  intro X x slots
  classical
  let V : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (slots a)).choose
  have hV : ∀ a : Fin 2, V a x = slots a := by
    intro a
    exact
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (slots a)).choose_spec
  let metricSec : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2 :=
    metricTensorField (I := I) g
  let mfun : M -> Real := fun y : M => metricSec y (fun a : Fin 2 => V a y)
  have hf_at : MDifferentiableAt I 𝓘(Real, Real) f x :=
    hf.contMDiffAt.mdifferentiableAt (by simp)
  have hm : MDifferentiableAt I 𝓘(Real, Real) mfun x := by
    exact (tensor0SField_eval_smooth_slots_contMDiffAt
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      metricSec V x).mdifferentiableAt (by simp)
  have hprod :
      mvfderiv (I := I) (fun y : M => f y * mfun y) x (X x) =
        f x * mvfderiv (I := I) mfun x (X x) +
          mvfderiv (I := I) f x (X x) * mfun x := by
    exact mvfderiv_mul_real (I := I) (f := f) (h := mfun) (X x) hf_at hm
  have hmetricReal :
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov metricSec
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) 3) := by
    simpa [metricSec] using zero_realizes_metric (I := I) cov g hmc
  have hmetricEval :=
    TotalNabla0SRealizes.eval_smooth_slots (I := I) hmetricReal X V x
  have hnabla :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov X V
      (tensor0SFieldSmulByFun (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
        f hf metricSec) x
  have hslots :
      (fun a : Fin 2 => V a x) = slots := by
    funext a
    exact hV a
  have hmetric_zero :
      mvfderiv (I := I) mfun x (X x) -
          ∑ a : Fin 2,
            metricSec x
              (Function.update (fun b : Fin 2 => V b x) a
                ((cov (fun p : M => V a p) x) (X x))) =
        0 := by
    simpa [metricSec, mfun] using hmetricEval.symm
  calc
    (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
        df metricSec) x (Fin.cons (X x) slots)
        =
          mvfderiv (I := I) f x (X x) * metricSec x slots := by
          change (Bundle.continuousMultilinearMap.productFun
              (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 1 x (df x))
              (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x (metricSec x)))
                (Fin.cons (X x) slots) =
            mvfderiv (I := I) f x (X x) * metricSec x slots
          rw [Bundle.continuousMultilinearMap.product_fun_apply]
          have hleft :
              Fin.cons (X x) slots ∘ Fin.castAdd 2 =
                fun _ : Fin 1 => X x := by
            funext a
            fin_cases a
            rfl
          have hright :
              Fin.cons (X x) slots ∘ Fin.natAdd 1 = slots := by
            funext a
            fin_cases a <;> rfl
          rw [hleft, hright,
            tensor0SSpaceFiberContinuousLinearEquiv_apply_apply,
            tensor0SSpaceFiberContinuousLinearEquiv_apply_apply,
            hdf x (X x)]
      _ =
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            2 cov X
            (tensor0SFieldSmulByFun (𝕜 := Real) (E := E) (H := H)
              (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
              f hf metricSec) x slots := by
          rw [← hslots]
          rw [hnabla]
          have hfun :
              (fun p : M =>
                (tensor0SFieldSmulByFun (𝕜 := Real) (E := E) (H := H)
                    (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
                    f hf metricSec p) (fun a : Fin 2 => V a p)) =
                fun p : M => f p * mfun p := by
            funext p
            rfl
          have hcorr :
              (∑ a : Fin 2,
                (tensor0SFieldSmulByFun (𝕜 := Real) (E := E) (H := H)
                    (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s := 2)
                    f hf metricSec x)
                  (Function.update (fun b : Fin 2 => V b x) a
                    ((cov (fun p : M => V a p) x) (X x)))) =
                ∑ a : Fin 2, f x *
                  metricSec x
                    (Function.update (fun b : Fin 2 => V b x) a
                      ((cov (fun p : M => V a p) x) (X x))) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rfl
          rw [hfun, hprod, hcorr]
          have hsum :
              (∑ a : Fin 2,
                f x *
                  metricSec x
                    (Function.update (fun b : Fin 2 => V b x) a
                      ((cov (fun p : M => V a p) x) (X x)))) =
                f x *
                  ∑ a : Fin 2,
                    metricSec x
                      (Function.update (fun b : Fin 2 => V b x) a
                        ((cov (fun p : M => V a p) x) (X x))) := by
            rw [Finset.mul_sum]
          rw [hsum]
          have hdm :
              mvfderiv (I := I) mfun x (X x) =
                ∑ a : Fin 2,
                  metricSec x
                    (Function.update (fun b : Fin 2 => V b x) a
                      ((cov (fun p : M => V a p) x) (X x))) := by
            linarith [hmetric_zero]
          rw [show mfun x = metricSec x (fun a : Fin 2 => V a x) from rfl, hdm]
          ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.nabla_smul_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.nabla_smul_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.nabla_smul_metric ``Submission.DifferentialGeometry.Tensor0SBundle.nabla_smul_metric

noncomputable def metricDerivsZero
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g) :
    CanonicalSpatialDerivs0S (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) cov (metricTensorField (I := I) g) where
  nablaA := 0
  nabla2A := 0
  first := zero_realizes_metric (I := I) cov g hmc
  second := zero_realizes_nabla (I := I) 3 cov

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.metricDerivsZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.metricDerivsZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.metricDerivsZero ``Submission.DifferentialGeometry.Tensor0SBundle.metricDerivsZero

@[simp]
theorem metricDerivsZero_nabla
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (x : M) (slots : Fin 3 -> TangentSpace I x) :
    (metricDerivsZero (I := I) cov g hmc).nablaA x slots = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.metricDerivsZero_nabla then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.metricDerivsZero_nabla"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.metricDerivsZero_nabla ``Submission.DifferentialGeometry.Tensor0SBundle.metricDerivsZero_nabla

@[simp]
theorem metricDerivsZero_nabla2
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible (I := I) cov g)
    (x : M) (slots : Fin 4 -> TangentSpace I x) :
    (metricDerivsZero (I := I) cov g hmc).nabla2A x slots = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.metricDerivsZero_nabla2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.metricDerivsZero_nabla2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.metricDerivsZero_nabla2 ``Submission.DifferentialGeometry.Tensor0SBundle.metricDerivsZero_nabla2

end

end Tensor0SBundle
end DifferentialGeometry
