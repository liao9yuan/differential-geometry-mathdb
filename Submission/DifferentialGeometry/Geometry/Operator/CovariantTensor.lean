import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Linearity
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Regularity.TotalNabla0S
import Submission.DifferentialGeometry.Geometry.Connection.MetricTrace.CovariantDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]

private theorem sub_of_add_smul {A B : Type*}
    [AddCommGroup A] [Module Real A] [AddCommGroup B] [Module Real B]
    (f : A -> B) (hadd : ∀ a b : A, f (a + b) = f a + f b)
    (hsmul : ∀ (c : Real) (a : A), f (c • a) = c • f a) (a b : A) :
    f (a - b) = f a - f b := by
  have hab : a - b = a + (-1 : Real) • b := by
    rw [neg_one_smul, ← sub_eq_add_neg]
  rw [hab, hadd, hsmul, neg_one_smul, ← sub_eq_add_neg]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.sub_of_add_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.sub_of_add_smul target :: scope.openDecls } }

section Operators

variable {s : ℕ}

def metricNabla0S (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1) :=
  totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
    (metricCov (I := I) g) T
    (totalNabla0S_regularity (E := E) (H := H) (I := I) (M := M) s
      (metricCov (I := I) g) (metricCov_smooth (I := I) g) T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricNabla0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricNabla0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricNabla0S ``Submission.DifferentialGeometry.PDE.RicciFlow.metricNabla0S

omit [SigmaCompactSpace M] in
@[simp] theorem metricNabla0S_apply (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    metricNabla0S (I := I) g T x =
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s
        (metricCov (I := I) g) T x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricNabla0S_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricNabla0S_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricNabla0S_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.metricNabla0S_apply

omit [SigmaCompactSpace M] in
theorem metricNabla0S_add (g : SmoothRiemannianMetric I M)
    (T U : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    metricNabla0S (I := I) g (T + U) =
      metricNabla0S (I := I) g T + metricNabla0S (I := I) g U := by
  refine DFunLike.ext _ _ fun x => ?_
  have hsplit :
      (metricNabla0S (I := I) g T + metricNabla0S (I := I) g U) x
        = metricNabla0S (I := I) g T x + metricNabla0S (I := I) g U x := rfl
  rw [hsplit]
  exact totalNabla0SFun_add (I := I) (M := M) (metricCov (I := I) g) T U x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricNabla0S_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricNabla0S_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricNabla0S_add ``Submission.DifferentialGeometry.PDE.RicciFlow.metricNabla0S_add

omit [SigmaCompactSpace M] in
theorem metricNabla0S_smul (g : SmoothRiemannianMetric I M) (c : Real)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    metricNabla0S (I := I) g (c • T) = c • metricNabla0S (I := I) g T := by
  refine DFunLike.ext _ _ fun x => ?_
  have hsplit :
      (c • metricNabla0S (I := I) g T) x = c • (metricNabla0S (I := I) g T x) := rfl
  rw [hsplit]
  exact totalNabla0SFun_smul (I := I) (M := M) (metricCov (I := I) g) c T x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricNabla0S_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricNabla0S_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricNabla0S_smul ``Submission.DifferentialGeometry.PDE.RicciFlow.metricNabla0S_smul

omit [SigmaCompactSpace M] in
theorem metricNabla0S_sub (g : SmoothRiemannianMetric I M)
    (T U : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    metricNabla0S (I := I) g (T - U) =
      metricNabla0S (I := I) g T - metricNabla0S (I := I) g U :=
  sub_of_add_smul (metricNabla0S (I := I) g) (metricNabla0S_add (I := I) g)
    (fun c a => metricNabla0S_smul (I := I) g c a) T U

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricNabla0S_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricNabla0S_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricNabla0S_sub ``Submission.DifferentialGeometry.PDE.RicciFlow.metricNabla0S_sub

omit [SigmaCompactSpace M] [T2Space M] in
theorem traceFirstTwo_sub (g : SmoothRiemannianMetric I M)
    (A B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2)) :
    metricTraceFirstTwoField (I := I) (M := M) g (A - B) =
      metricTraceFirstTwoField (I := I) (M := M) g A -
        metricTraceFirstTwoField (I := I) (M := M) g B :=
  sub_of_add_smul (metricTraceFirstTwoField (I := I) (M := M) (s := s) g)
    (metricTraceFirstTwoField_add (I := I) (M := M) g)
    (fun c a => metricTraceFirstTwoField_smul (I := I) (M := M) g c a) A B

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.traceFirstTwo_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.traceFirstTwo_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.traceFirstTwo_sub ``Submission.DifferentialGeometry.PDE.RicciFlow.traceFirstTwo_sub

omit [SigmaCompactSpace M] [T2Space M] in
theorem traceFirstTwo_zero (g : SmoothRiemannianMetric I M) :
    metricTraceFirstTwoField (I := I) (M := M) g
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (s + 2)) = 0 := by
  simpa using traceFirstTwo_sub (I := I) (M := M) (s := s) g 0 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.traceFirstTwo_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.traceFirstTwo_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.traceFirstTwo_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.traceFirstTwo_zero

def covDiv0SField (g : SmoothRiemannianMetric I M)
    (V : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
  metricTraceFirstTwoField (I := I) (M := M) g (metricNabla0S (I := I) g V)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covDiv0SField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covDiv0SField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covDiv0SField ``Submission.DifferentialGeometry.PDE.RicciFlow.covDiv0SField

def roughLap0SField (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
  covDiv0SField (I := I) g (metricNabla0S (I := I) g T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.roughLap0SField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.roughLap0SField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.roughLap0SField ``Submission.DifferentialGeometry.PDE.RicciFlow.roughLap0SField

omit [SigmaCompactSpace M] in
theorem roughLap0SField_apply (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    roughLap0SField (I := I) g T x =
      roughLap0STensor (I := I) g
        (metricNabla0S (I := I) g (metricNabla0S (I := I) g T) x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.roughLap0SField_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.roughLap0SField_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.roughLap0SField_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.roughLap0SField_apply

omit [SigmaCompactSpace M] in
theorem covDiv0SField_sub (g : SmoothRiemannianMetric I M)
    (V W : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) :
    covDiv0SField (I := I) g (V - W) =
      covDiv0SField (I := I) g V - covDiv0SField (I := I) g W := by
  rw [covDiv0SField, covDiv0SField, covDiv0SField, metricNabla0S_sub,
    traceFirstTwo_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.covDiv0SField_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.covDiv0SField_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.covDiv0SField_sub ``Submission.DifferentialGeometry.PDE.RicciFlow.covDiv0SField_sub

end Operators

end DifferentialGeometry.PDE.RicciFlow
