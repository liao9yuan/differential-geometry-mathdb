import Submission.DifferentialGeometry.Geometry.Curvature.Sections.Connection
import Submission.DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse
import Submission.DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Covariant
import Submission.DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Coordinate
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.LinearAlgebra
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.Expansion
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.Product
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Calculus.CovariantDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Operator

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def metricTraceInput {x : M} {s : ℕ}
    (X Y : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    Fin (s + 2) -> TangentSpace I x :=
  Fin.cases X (Fin.cases Y tail)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTraceInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTraceInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTraceInput ``Submission.DifferentialGeometry.Geometry.Operator.metricTraceInput

def metricTensor0S (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  (((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm.toContinuousLinearMap).comp
    (g.inner x)).uncurryLeft

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTensor0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTensor0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTensor0S ``Submission.DifferentialGeometry.Geometry.Operator.metricTensor0S

@[simp]
theorem metricTensor0S_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 -> TangentSpace I x) :
    metricTensor0S (I := I) g x v = g.inner x (v 0) (v 1) := by
  unfold metricTensor0S
  change
    ((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
      (g.inner x (v 0))) (fun i : Fin 1 => v i.succ) =
      g.inner x (v 0) (v 1)
  have htail : (fun i : Fin 1 => v i.succ) = fun _ : Fin 1 => v 1 := by
    funext i
    fin_cases i
    rfl
  rw [htail]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTensor0S_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTensor0S_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTensor0S_apply ``Submission.DifferentialGeometry.Geometry.Operator.metricTensor0S_apply

def metricTracePair0SAt (g : SmoothRiemannianMetric I M)
    {x : M}
    (B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    Real :=
  inner0S (I := I) g x 2 (metricTensor0S (I := I) g x) B

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTracePair0SAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTracePair0SAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTracePair0SAt ``Submission.DifferentialGeometry.Geometry.Operator.metricTracePair0SAt

omit [FiniteDimensional ℝ E] in
private theorem tensor0S_curry_apply_cons_local
    {x : M} (s : ℕ)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (X : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    (tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x A X) tail =
      A (Fin.cons X tail) := by
  change
    (((continuousMultilinearCurryLeftEquiv Real
        (fun _ : Fin (s + 1) => TangentSpace I x) Real)
        ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) (M := M) (s + 1) x) A)
        X)
        tail) =
      ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) (M := M) (s + 1) x) A)
        (Fin.cons X tail)
  rw [continuousMultilinearCurryLeftEquiv_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.tensor0S_curry_apply_cons_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.tensor0S_curry_apply_cons_local target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem tensor0SSpace_sum_apply {ι : Type*} [Fintype ι] {x : M} {s : ℕ}
    (T : ι -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (v : Fin s -> TangentSpace I x) :
    ((∑ i : ι, T i) v) = ∑ i : ι, (T i) v := by
  classical
  let S : Finset ι := Finset.univ
  change ((∑ i ∈ S, T i) v) = ∑ i ∈ S, (T i) v
  induction S using Finset.induction_on with
  | empty =>
      change
        (0 : ContinuousMultilinearMap Real
          (fun _ : Fin s => TangentSpace I x) Real) v = 0
      simp
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change T a v + (∑ i ∈ S, T i) v = T a v + ∑ i ∈ S, T i v
      rw [ih]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.tensor0SSpace_sum_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.tensor0SSpace_sum_apply target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem tensor0SSpace_smul_apply {x : M} {s : ℕ}
    (c : Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (v : Fin s -> TangentSpace I x) :
    (c • T) v = c * T v := by
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.tensor0SSpace_smul_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.tensor0SSpace_smul_apply target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem metricTraceInput_update_first {x : M} {s : ℕ}
    (v : Fin 2 -> TangentSpace I x) (tail : Fin s -> TangentSpace I x)
    (X : TangentSpace I x) :
    metricTraceInput (I := I) X (v 1) tail =
      Function.update (metricTraceInput (I := I) (v 0) (v 1) tail)
        (0 : Fin (s + 2)) X := by
  funext a
  rcases Fin.eq_zero_or_eq_succ a with h | ⟨b, rfl⟩
  · subst h
    simp [metricTraceInput, Function.update]
  · simp [metricTraceInput, Function.update]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.metricTraceInput_update_first
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.metricTraceInput_update_first target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem metricTraceInput_update_second {x : M} {s : ℕ}
    (v : Fin 2 -> TangentSpace I x) (tail : Fin s -> TangentSpace I x)
    (Y : TangentSpace I x) :
    metricTraceInput (I := I) (v 0) Y tail =
      Function.update (metricTraceInput (I := I) (v 0) (v 1) tail)
        (1 : Fin (s + 2)) Y := by
  funext a
  rcases Fin.eq_zero_or_eq_succ a with h | ⟨b, rfl⟩
  · subst h
    simp [metricTraceInput, Function.update]
  · rcases Fin.eq_zero_or_eq_succ b with hb | ⟨c, rfl⟩
    · subst hb
      exact rfl
    · have hne : (c.succ.succ : Fin (s + 2)) ≠ (1 : Fin (s + 2)) := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      simp [metricTraceInput, Function.update, hne]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.metricTraceInput_update_second
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.metricTraceInput_update_second target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
theorem exists_freezeFirstTwo0S {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    ∃ B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x,
      ∀ X Y : TangentSpace I x,
        B (vec2 (I := I) X Y) = T (metricTraceInput (I := I) X Y tail) := by
  classical
  let Traw :
      ContinuousMultilinearMap Real (fun _ : Fin (s + 2) => TangentSpace I x) Real :=
    (tensor0SSpaceContinuousLinearEquiv (I := I) (M := M) (s + 2) x) T
  let L : MultilinearMap Real (fun _ : Fin 2 => TangentSpace I x) Real :=
    { toFun := fun v => Traw (metricTraceInput (I := I) (v 0) (v 1) tail)
      map_update_add' := by
        intro _ v i X Y
        fin_cases i
        · have h :=
            Traw.map_update_add (metricTraceInput (I := I) (v 0) (v 1) tail)
              (0 : Fin (s + 2)) X Y
          rw [← metricTraceInput_update_first (I := I) v tail (X + Y),
            ← metricTraceInput_update_first (I := I) v tail X,
            ← metricTraceInput_update_first (I := I) v tail Y] at h
          simpa [Function.update] using h
        · have h :=
            Traw.map_update_add (metricTraceInput (I := I) (v 0) (v 1) tail)
              (1 : Fin (s + 2)) X Y
          rw [← metricTraceInput_update_second (I := I) v tail (X + Y),
            ← metricTraceInput_update_second (I := I) v tail X,
            ← metricTraceInput_update_second (I := I) v tail Y] at h
          simpa [Function.update] using h
      map_update_smul' := by
        intro _ v i c X
        fin_cases i
        · have h :=
            Traw.map_update_smul (metricTraceInput (I := I) (v 0) (v 1) tail)
              (0 : Fin (s + 2)) c X
          rw [← metricTraceInput_update_first (I := I) v tail (c • X),
            ← metricTraceInput_update_first (I := I) v tail X] at h
          simpa [Function.update] using h
        · have h :=
            Traw.map_update_smul (metricTraceInput (I := I) (v 0) (v 1) tail)
              (1 : Fin (s + 2)) c X
          rw [← metricTraceInput_update_second (I := I) v tail (c • X),
            ← metricTraceInput_update_second (I := I) v tail X] at h
          simpa [Function.update] using h }
  let C : Real := ‖Traw‖ * ∏ a : Fin s, ‖tail a‖
  have hbound :
      ∀ v : Fin 2 -> TangentSpace I x, ‖L v‖ ≤ C * ∏ i : Fin 2, ‖v i‖ := by
    intro v
    have hT := Traw.le_opNorm (metricTraceInput (I := I) (v 0) (v 1) tail)
    have hprod :
        (∏ a : Fin (s + 2), ‖metricTraceInput (I := I) (v 0) (v 1) tail a‖)
          = ‖v 0‖ * ‖v 1‖ * ∏ a : Fin s, ‖tail a‖ := by
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp only [metricTraceInput, Fin.cases_zero, Fin.cases_succ]
      ring
    have hprod2 : (∏ i : Fin 2, ‖v i‖) = ‖v 0‖ * ‖v 1‖ := by
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp
    calc
      ‖L v‖
          ≤ ‖Traw‖ * (∏ a : Fin (s + 2),
              ‖metricTraceInput (I := I) (v 0) (v 1) tail a‖) := hT
      _ = C * ∏ i : Fin 2, ‖v i‖ := by
        rw [hprod, hprod2]
        simp [C]
        ring
  let Braw : ContinuousMultilinearMap Real (fun _ : Fin 2 => TangentSpace I x) Real :=
    L.mkContinuous C hbound
  refine ⟨(tensor0SSpaceContinuousLinearEquiv (I := I) (M := M) 2 x).symm
    Braw, ?_⟩
  intro X Y
  change Braw (vec2 (I := I) X Y) =
    Traw (metricTraceInput (I := I) X Y tail)
  change L (vec2 (I := I) X Y) =
    Traw (metricTraceInput (I := I) X Y tail)
  simp [L, DifferentialGeometry.Geometry.Curvature.vec2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.exists_freezeFirstTwo0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.exists_freezeFirstTwo0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.exists_freezeFirstTwo0S ``Submission.DifferentialGeometry.Geometry.Operator.exists_freezeFirstTwo0S

def freezeFirstTwo0S {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  Classical.choose (exists_freezeFirstTwo0S (I := I) T tail)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S ``Submission.DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S

omit [FiniteDimensional ℝ E] in
@[simp]
theorem freezeFirstTwo0S_apply {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) (X Y : TangentSpace I x) :
    freezeFirstTwo0S (I := I) T tail (vec2 (I := I) X Y) =
      T (metricTraceInput (I := I) X Y tail) := by
  exact Classical.choose_spec (exists_freezeFirstTwo0S (I := I) T tail) X Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S_apply ``Submission.DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S_apply

def freezeFirstTwoArgs0S {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (X Y : TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
    (tensor0SCurry (I := I) (𝕜 := Real) (M := M) (s + 1) x T X) Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.freezeFirstTwoArgs0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.freezeFirstTwoArgs0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.freezeFirstTwoArgs0S ``Submission.DifferentialGeometry.Geometry.Operator.freezeFirstTwoArgs0S

omit [FiniteDimensional ℝ E] in
@[simp]
theorem freezeFirstTwoArgs0S_apply {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (X Y : TangentSpace I x) (tail : Fin s -> TangentSpace I x) :
    freezeFirstTwoArgs0S (I := I) T X Y tail =
      T (metricTraceInput (I := I) X Y tail) := by
  unfold freezeFirstTwoArgs0S
  rw [tensor0S_curry_apply_cons_local, tensor0S_curry_apply_cons_local]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.freezeFirstTwoArgs0S_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.freezeFirstTwoArgs0S_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.freezeFirstTwoArgs0S_apply ``Submission.DifferentialGeometry.Geometry.Operator.freezeFirstTwoArgs0S_apply

omit [FiniteDimensional ℝ E] in
theorem exists_freezeLastTwo0S3 {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) :
    ∃ B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x,
      ∀ X Z : TangentSpace I x,
        B (vec2 (I := I) X Z) = T (vec3 (I := I) Y X Z) := by
  refine ⟨tensor0SCurry (I := I) (𝕜 := Real) (M := M) 2 x T Y, ?_⟩
  intro X Z
  rw [tensor0S_curry_apply_cons_local]
  congr 1
  funext a
  fin_cases a
  · norm_num [DifferentialGeometry.Geometry.Curvature.vec2,
    DifferentialGeometry.Geometry.Curvature.vec3]
  · norm_num [DifferentialGeometry.Geometry.Curvature.vec2,
    DifferentialGeometry.Geometry.Curvature.vec3]
  · change (vec2 (I := I) X Z) 1 = Z
    norm_num [DifferentialGeometry.Geometry.Curvature.vec2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.exists_freezeLastTwo0S3 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.exists_freezeLastTwo0S3"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.exists_freezeLastTwo0S3 ``Submission.DifferentialGeometry.Geometry.Operator.exists_freezeLastTwo0S3

def freezeLastTwo0S3 {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  Classical.choose (exists_freezeLastTwo0S3 (I := I) T Y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.freezeLastTwo0S3 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.freezeLastTwo0S3"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.freezeLastTwo0S3 ``Submission.DifferentialGeometry.Geometry.Operator.freezeLastTwo0S3

omit [FiniteDimensional ℝ E] in
@[simp]
theorem freezeLastTwo0S3_apply {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y X Z : TangentSpace I x) :
    freezeLastTwo0S3 (I := I) T Y (vec2 (I := I) X Z) =
      T (vec3 (I := I) Y X Z) := by
  exact Classical.choose_spec (exists_freezeLastTwo0S3 (I := I) T Y) X Z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.freezeLastTwo0S3_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.freezeLastTwo0S3_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.freezeLastTwo0S3_apply ``Submission.DifferentialGeometry.Geometry.Operator.freezeLastTwo0S3_apply

def metricTraceFirstTwo0SAt (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) : Real :=
  metricTracePair0SAt (I := I) g (freezeFirstTwo0S (I := I) T tail)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt ``Submission.DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt

theorem freezeFirstTwo0S_neg {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    freezeFirstTwo0S (I := I) (-T) tail = -(freezeFirstTwo0S (I := I) T tail) := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro slots
  simp only [component0S_apply]
  have hslots :
      (fun a : Fin 2 => basis (slots a)) =
        vec2 (I := I) (basis (slots 0)) (basis (slots 1)) := by
    funext a
    fin_cases a <;> rfl
  rw [hslots, freezeFirstTwo0S_apply]
  change (-T) (metricTraceInput (I := I) (basis (slots 0)) (basis (slots 1)) tail) =
    -((freezeFirstTwo0S (I := I) T tail) (vec2 (I := I) (basis (slots 0)) (basis (slots 1))))
  have h2 :
      (freezeFirstTwo0S (I := I) T tail) (vec2 (I := I) (basis (slots 0)) (basis (slots 1))) =
        T (metricTraceInput (I := I) (basis (slots 0)) (basis (slots 1)) tail) :=
    freezeFirstTwo0S_apply (I := I) T tail (basis (slots 0)) (basis (slots 1))
  calc
    (-T) (metricTraceInput (I := I) (basis (slots 0)) (basis (slots 1)) tail)
        = -(T (metricTraceInput (I := I) (basis (slots 0)) (basis (slots 1)) tail)) := by rfl
    _ = -((freezeFirstTwo0S (I := I) T tail) (vec2 (I := I) (basis (slots 0)) (basis
      (slots 1)))) := by
          congr 1
          exact h2.symm
    _ = (-freezeFirstTwo0S (I := I) T tail) (vec2 (I := I) (basis (slots 0)) (basis
      (slots 1))) := by rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S_neg ``Submission.DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S_neg

theorem freezeFirstTwo0S_add {x : M} {s : ℕ}
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    freezeFirstTwo0S (I := I) (A + B) tail =
      freezeFirstTwo0S (I := I) A tail + freezeFirstTwo0S (I := I) B tail := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro slots
  simp only [component0S_apply]
  have hslots :
      (fun a : Fin 2 => basis (slots a)) =
        vec2 (I := I) (basis (slots 0)) (basis (slots 1)) := by
    funext a
    fin_cases a <;> rfl
  rw [hslots, freezeFirstTwo0S_apply]
  change (A + B) (metricTraceInput (I := I) (basis (slots 0)) (basis (slots 1)) tail) =
    (freezeFirstTwo0S (I := I) A tail) (vec2 (I := I) (basis (slots 0)) (basis (slots 1))) +
      (freezeFirstTwo0S (I := I) B tail) (vec2 (I := I) (basis (slots 0)) (basis (slots 1)))
  have hA :
      (freezeFirstTwo0S (I := I) A tail) (vec2 (I := I) (basis (slots 0)) (basis (slots 1))) =
        A (metricTraceInput (I := I) (basis (slots 0)) (basis (slots 1)) tail) :=
    freezeFirstTwo0S_apply (I := I) A tail (basis (slots 0)) (basis (slots 1))
  have hB :
      (freezeFirstTwo0S (I := I) B tail) (vec2 (I := I) (basis (slots 0)) (basis (slots 1))) =
        B (metricTraceInput (I := I) (basis (slots 0)) (basis (slots 1)) tail) :=
    freezeFirstTwo0S_apply (I := I) B tail (basis (slots 0)) (basis (slots 1))
  calc
    (A + B) (metricTraceInput (I := I) (basis (slots 0)) (basis (slots 1)) tail)
        = A (metricTraceInput (I := I) (basis (slots 0)) (basis (slots 1)) tail) +
            B (metricTraceInput (I := I) (basis (slots 0)) (basis (slots 1)) tail) := by rfl
    _ = (freezeFirstTwo0S (I := I) A tail) (vec2 (I := I) (basis (slots 0)) (basis (slots 1))) +
          (freezeFirstTwo0S (I := I) B tail) (vec2 (I := I) (basis (slots 0)) (basis
            (slots 1))) := by
          rw [hA, hB]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S_add ``Submission.DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S_add

theorem freezeFirstTwo0S_smul {x : M} {s : ℕ} (c : Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    freezeFirstTwo0S (I := I) (c • T) tail = c • freezeFirstTwo0S (I := I) T tail := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro slots
  simp only [component0S_apply]
  have hslots :
      (fun a : Fin 2 => basis (slots a)) =
        vec2 (I := I) (basis (slots 0)) (basis (slots 1)) := by
    funext a
    fin_cases a <;> rfl
  rw [hslots, freezeFirstTwo0S_apply]
  change (c • T) (metricTraceInput (I := I) (basis (slots 0)) (basis (slots 1)) tail) =
    c • (freezeFirstTwo0S (I := I) T tail) (vec2 (I := I) (basis (slots 0)) (basis (slots 1)))
  have hT :
      (freezeFirstTwo0S (I := I) T tail) (vec2 (I := I) (basis (slots 0)) (basis (slots 1))) =
        T (metricTraceInput (I := I) (basis (slots 0)) (basis (slots 1)) tail) :=
    freezeFirstTwo0S_apply (I := I) T tail (basis (slots 0)) (basis (slots 1))
  calc
    (c • T) (metricTraceInput (I := I) (basis (slots 0)) (basis (slots 1)) tail)
        = c • T (metricTraceInput (I := I) (basis (slots 0)) (basis (slots 1)) tail) := by rfl
    _ = c • (freezeFirstTwo0S (I := I) T tail) (vec2 (I := I) (basis (slots 0)) (basis
      (slots 1))) := by
          rw [hT]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S_smul ``Submission.DifferentialGeometry.Geometry.Operator.freezeFirstTwo0S_smul

theorem metricTracePair0SAt_neg (g : SmoothRiemannianMetric I M) {x : M}
    (B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    metricTracePair0SAt (I := I) g (-B) = -metricTracePair0SAt (I := I) g B := by
  unfold metricTracePair0SAt
  exact (tensor0SMetricData (I := I) g x 2).flat (metricTensor0S (I := I) g x) |>.map_neg B

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_neg ``Submission.DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_neg

theorem metricTracePair0SAt_add (g : SmoothRiemannianMetric I M) {x : M}
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    metricTracePair0SAt (I := I) g (A + B) =
      metricTracePair0SAt (I := I) g A + metricTracePair0SAt (I := I) g B := by
  unfold metricTracePair0SAt
  change (tensor0SMetricData (I := I) g x 2).flat (metricTensor0S (I := I) g x) (A + B) =
    (tensor0SMetricData (I := I) g x 2).flat (metricTensor0S (I := I) g x) A +
      (tensor0SMetricData (I := I) g x 2).flat (metricTensor0S (I := I) g x) B
  rw [map_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_add ``Submission.DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_add

theorem metricTracePair0SAt_smul (g : SmoothRiemannianMetric I M) {x : M} (c : Real)
    (B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    metricTracePair0SAt (I := I) g (c • B) = c * metricTracePair0SAt (I := I) g B := by
  unfold metricTracePair0SAt
  change (tensor0SMetricData (I := I) g x 2).flat (metricTensor0S (I := I) g x) (c • B) = _
  rw [map_smul]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_smul ``Submission.DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_smul

theorem metricTracePair0SAt_sub (g : SmoothRiemannianMetric I M) {x : M}
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    metricTracePair0SAt (I := I) g (A - B) =
      metricTracePair0SAt (I := I) g A - metricTracePair0SAt (I := I) g B := by
  calc
    metricTracePair0SAt (I := I) g (A - B)
        = metricTracePair0SAt (I := I) g (A + -B) := by rfl
    _ = metricTracePair0SAt (I := I) g A + metricTracePair0SAt (I := I) g (-B) :=
          metricTracePair0SAt_add (I := I) g A (-B)
    _ = metricTracePair0SAt (I := I) g A - metricTracePair0SAt (I := I) g B := by
          rw [metricTracePair0SAt_neg (I := I) g B]
          rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_sub ``Submission.DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_sub

theorem metricTraceFirstTwo0SAt_neg (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g (-T) tail = -metricTraceFirstTwo0SAt (I := I) g T tail := by
  unfold metricTraceFirstTwo0SAt
  rw [freezeFirstTwo0S_neg (I := I) T tail]
  exact metricTracePair0SAt_neg (I := I) g (freezeFirstTwo0S (I := I) T tail)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_neg ``Submission.DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_neg

theorem metricTraceFirstTwo0SAt_add (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g (A + B) tail =
      metricTraceFirstTwo0SAt (I := I) g A tail +
        metricTraceFirstTwo0SAt (I := I) g B tail := by
  unfold metricTraceFirstTwo0SAt
  rw [freezeFirstTwo0S_add (I := I) A B tail]
  exact metricTracePair0SAt_add (I := I) g (freezeFirstTwo0S (I := I) A tail)
    (freezeFirstTwo0S (I := I) B tail)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_add ``Submission.DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_add

theorem metricTraceFirstTwo0SAt_smul (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ} (c : Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g (c • T) tail = c * metricTraceFirstTwo0SAt
      (I := I) g T tail := by
  unfold metricTraceFirstTwo0SAt
  rw [freezeFirstTwo0S_smul (I := I) c T tail]
  exact metricTracePair0SAt_smul (I := I) g c (freezeFirstTwo0S (I := I) T tail)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_smul ``Submission.DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_smul

theorem metricTraceFirstTwo0SAt_sub (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g (A - B) tail =
      metricTraceFirstTwo0SAt (I := I) g A tail -
        metricTraceFirstTwo0SAt (I := I) g B tail := by
  calc
    metricTraceFirstTwo0SAt (I := I) g (A - B) tail
        = metricTraceFirstTwo0SAt (I := I) g (A + -B) tail := by rfl
    _ = metricTraceFirstTwo0SAt (I := I) g A tail + metricTraceFirstTwo0SAt (I := I) g (-B) tail :=
          metricTraceFirstTwo0SAt_add (I := I) g A (-B) tail
    _ = metricTraceFirstTwo0SAt (I := I) g A tail - metricTraceFirstTwo0SAt (I := I) g B tail := by
          rw [metricTraceFirstTwo0SAt_neg (I := I) g B tail]
          rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_sub ``Submission.DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_sub

def metricTraceLastTwo0SAt3 (g : SmoothRiemannianMetric I M)
    {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) : Real :=
  metricTracePair0SAt (I := I) g (freezeLastTwo0S3 (I := I) T Y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTraceLastTwo0SAt3 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTraceLastTwo0SAt3"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTraceLastTwo0SAt3 ``Submission.DifferentialGeometry.Geometry.Operator.metricTraceLastTwo0SAt3

def metricTrace0S2InBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    gInv i j * T (metricTraceInput (I := I) (basis i) (basis j) tail)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTrace0S2InBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTrace0S2InBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTrace0S2InBasis ``Submission.DifferentialGeometry.Geometry.Operator.metricTrace0S2InBasis

def metricTrace0S2TensorInBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  ∑ i : Idx, ∑ j : Idx,
    gInv i j • freezeFirstTwoArgs0S (I := I) T (basis i) (basis j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTrace0S2TensorInBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTrace0S2TensorInBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTrace0S2TensorInBasis ``Submission.DifferentialGeometry.Geometry.Operator.metricTrace0S2TensorInBasis

omit [FiniteDimensional ℝ E] in
@[simp]
theorem metricTrace0S2TensorInBasis_apply
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTrace0S2TensorInBasis (I := I) basis gInv T tail =
      metricTrace0S2InBasis (I := I) basis gInv T tail := by
  rw [metricTrace0S2TensorInBasis, metricTrace0S2InBasis]
  rw [tensor0SSpace_sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [tensor0SSpace_sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [tensor0SSpace_smul_apply, freezeFirstTwoArgs0S_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTrace0S2TensorInBasis_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTrace0S2TensorInBasis_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTrace0S2TensorInBasis_apply ``Submission.DifferentialGeometry.Geometry.Operator.metricTrace0S2TensorInBasis_apply

omit [FiniteDimensional ℝ E] in
private theorem metricInverseInBasis_contract_left
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (j k : Idx) :
    (∑ i : Idx, gInv i k * g.inner x (basis i) (basis j)) =
      (if j = k then 1 else 0) := by
  calc
    (∑ i : Idx, gInv i k * g.inner x (basis i) (basis j))
        = ∑ i : Idx, g.inner x (basis j) (basis i) * gInv i k := by
          apply Finset.sum_congr rfl
          intro i _
          rw [g.symm x (basis i) (basis j)]
          ring
    _ = (if j = k then 1 else 0) := (hinv j k).2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.metricInverseInBasis_contract_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.metricInverseInBasis_contract_left target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem metricInverseInBasis_contract_metric
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (k l : Idx) :
    (∑ i : Idx, ∑ j : Idx,
      gInv i k * gInv j l * g.inner x (basis i) (basis j)) =
        gInv k l := by
  calc
    (∑ i : Idx, ∑ j : Idx,
      gInv i k * gInv j l * g.inner x (basis i) (basis j))
        = ∑ j : Idx,
            (∑ i : Idx, gInv i k * g.inner x (basis i) (basis j)) *
              gInv j l := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ j : Idx, (if j = k then 1 else 0) * gInv j l := by
          apply Finset.sum_congr rfl
          intro j _
          rw [metricInverseInBasis_contract_left (I := I) g basis gInv hinv j k]
    _ = gInv k l := by
          rw [Finset.sum_eq_single k]
          · simp
          · intro b _ hb
            simp [hb]
          · intro hk
            simp at hk

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.metricInverseInBasis_contract_metric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.metricInverseInBasis_contract_metric target :: scope.openDecls } }

theorem metricTracePair0SAt_eq_sum_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    metricTracePair0SAt (I := I) g B =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * B (vec2 (I := I) (basis i) (basis j)) := by
  classical
  rw [metricTracePair0SAt]
  rw [inner0S_two_eq_coord_direct (I := I) g x basis gInv hinv
    (metricTensor0S (I := I) g x) B]
  simp only [metricTensor0S_apply]
  calc
    (∑ i : Idx, ∑ j : Idx, ∑ k : Idx, ∑ l : Idx,
      gInv i k * gInv j l * g.inner x (basis i) (basis j) *
        B (fun a : Fin 2 => if a = 0 then basis k else basis l))
        =
      ∑ i : Idx, ∑ k : Idx, ∑ j : Idx, ∑ l : Idx,
        gInv i k * gInv j l * g.inner x (basis i) (basis j) *
          B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
    _ =
      ∑ k : Idx, ∑ i : Idx, ∑ j : Idx, ∑ l : Idx,
        gInv i k * gInv j l * g.inner x (basis i) (basis j) *
          B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          rw [Finset.sum_comm]
    _ =
      ∑ k : Idx, ∑ i : Idx, ∑ l : Idx, ∑ j : Idx,
        gInv i k * gInv j l * g.inner x (basis i) (basis j) *
          B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
    _ =
      ∑ k : Idx, ∑ l : Idx, ∑ i : Idx, ∑ j : Idx,
        gInv i k * gInv j l * g.inner x (basis i) (basis j) *
          B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_comm]
    _ =
      ∑ k : Idx, ∑ l : Idx,
        (∑ i : Idx, ∑ j : Idx,
          gInv i k * gInv j l * g.inner x (basis i) (basis j)) *
          B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
    _ = ∑ k : Idx, ∑ l : Idx,
        gInv k l * B (fun a : Fin 2 => if a = 0 then basis k else basis l) := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          rw [metricInverseInBasis_contract_metric (I := I) g basis gInv hinv k l]
    _ = ∑ k : Idx, ∑ l : Idx,
        gInv k l * B (vec2 (I := I) (basis k) (basis l)) := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_eq_sum_basis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_eq_sum_basis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_eq_sum_basis ``Submission.DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_eq_sum_basis

theorem normSq0S_metricTensor0S_eq_card
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv) :
    normSq0S (I := I) g x 2 (metricTensor0S (I := I) g x) =
      (Fintype.card Idx : Real) := by
  classical
  rw [normSq0S_eq_inner]
  change metricTracePair0SAt (I := I) g (metricTensor0S (I := I) g x) =
    (Fintype.card Idx : Real)
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis gInv hinv]
  calc
    (∑ i : Idx, ∑ j : Idx,
        gInv i j * metricTensor0S (I := I) g x (vec2 (I := I) (basis i) (basis j)))
        =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * g.inner x (basis j) (basis i) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          simp [metricTensor0S_apply, vec2, DifferentialGeometry.Geometry.Curvature.vec2,
            g.symm x (basis i) (basis j)]
    _ = ∑ i : Idx, (if i = i then (1 : Real) else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          exact (hinv i i).1
    _ = (Fintype.card Idx : Real) := by
          simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.normSq0S_metricTensor0S_eq_card then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.normSq0S_metricTensor0S_eq_card"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.normSq0S_metricTensor0S_eq_card ``Submission.DifferentialGeometry.Geometry.Operator.normSq0S_metricTensor0S_eq_card

theorem metricTracePair0SAt_metric
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricTracePair0SAt (I := I) g (metricTensor0S (I := I) g x) =
      (Module.finrank Real E : Real) := by
  classical
  have h := normSq0S_metricTensor0S_eq_card (I := I) g
    (Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x)
    (fun i j => Tensor.Coordinates.inverseMetricFlatModelInChartComponent
      (I := I) g x i j (extChartAt I x x))
    (Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) g x)
  simpa only [normSq0S_eq_inner, metricTracePair0SAt, Fintype.card_fin] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_metric ``Submission.DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_metric

theorem metricTracePair0SAt_sq_le_card_mul_normSq0S
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    (metricTracePair0SAt (I := I) g A) ^ 2 <=
      (Fintype.card Idx : Real) * normSq0S (I := I) g x 2 A := by
  let D := tensor0SMetricData (I := I) g x 2
  let : PreInnerProductSpace.Core Real
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
    D.toCore.toCore
  let : Inner Real
      (Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :=
    D.toCore.toCore.toInner
  have hcs :=
    InnerProductSpace.Core.inner_mul_inner_self_le
      (𝕜 := Real)
      (F := Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
      (metricTensor0S (I := I) g x) A
  have hmetric :
      Inner.inner Real (metricTensor0S (I := I) g x)
          (metricTensor0S (I := I) g x) =
        (Fintype.card Idx : Real) := by
    change D.inner (metricTensor0S (I := I) g x)
        (metricTensor0S (I := I) g x) = (Fintype.card Idx : Real)
    exact normSq0S_metricTensor0S_eq_card (I := I) g basis gInv hinv
  have hA :
      Inner.inner Real A A = normSq0S (I := I) g x 2 A := by
    change D.inner A A = normSq0S (I := I) g x 2 A
    rfl
  have htrace :
      Inner.inner Real (metricTensor0S (I := I) g x) A =
        metricTracePair0SAt (I := I) g A := by
    change D.inner (metricTensor0S (I := I) g x) A =
      metricTracePair0SAt (I := I) g A
    rfl
  have htrace_comm :
      Inner.inner Real A (metricTensor0S (I := I) g x) =
        metricTracePair0SAt (I := I) g A := by
    change D.inner A (metricTensor0S (I := I) g x) =
      metricTracePair0SAt (I := I) g A
    rw [D.inner_comm]
    rfl
  have habs :
      ‖Inner.inner Real (metricTensor0S (I := I) g x) A‖ *
          ‖Inner.inner Real A (metricTensor0S (I := I) g x)‖ =
        (metricTracePair0SAt (I := I) g A) ^ 2 := by
    rw [htrace, htrace_comm]
    simp [Real.norm_eq_abs, pow_two]
  rw [habs, hmetric, hA] at hcs
  exact hcs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_sq_le_card_mul_normSq0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_sq_le_card_mul_normSq0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_sq_le_card_mul_normSq0S ``Submission.DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_sq_le_card_mul_normSq0S

theorem trace_sub_le_c0
    (g h : SmoothRiemannianMetric I M) (x : M)
    {C : Real} (hC : 1 ≤ C)
    (hequiv : ∀ v : TangentSpace I x,
      C⁻¹ * g.inner x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ C * g.inner x v v)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 x) :
    |metricTracePair0SAt (I := I) h A -
        metricTracePair0SAt (I := I) g A| ≤
      (Module.finrank Real (TangentSpace I x) : Real) * C *
        Real.sqrt
          (normSq0S (I := I) g x 2
            (metricTensor0S (I := I) h x -
              metricTensor0S (I := I) g x)) *
        Real.sqrt (normSq0S (I := I) g x 2 A) := by
  classical
  obtain ⟨μ, basis, hginv, hhinv, hμ0, hμC⟩ :=
    exists_diagInv_of_equiv (I := I) g h x hC hequiv
  have hgON : ∀ i j, g.inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0 := by
    intro i j
    have hsum :
        (∑ k, identityInvMetric i k * g.inner x (basis k) (basis j)) =
          g.inner x (basis i) (basis j) := by
      rw [Finset.sum_eq_single i]
      · rw [identityInvMetric_apply_self, one_mul]
      · intro k _ hki
        rw [show identityInvMetric i k = 0 from
          diagonalInvMetric_eq_zero_of_ne hki.symm, _root_.MulZeroClass.zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [← hsum]
    exact (hginv i j).1
  have htrace_g :
      metricTracePair0SAt (I := I) g A =
        ∑ i, A (vec2 (I := I) (basis i) (basis i)) := by
    rw [metricTracePair0SAt_eq_sum_basis
      (I := I) g basis identityInvMetric hginv]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · rw [identityInvMetric_apply_self, one_mul]
    · intro j _ hji
      rw [show identityInvMetric i j = 0 from
        diagonalInvMetric_eq_zero_of_ne hji.symm, _root_.MulZeroClass.zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have htrace_h :
      metricTracePair0SAt (I := I) h A =
        ∑ i, μ i * A (vec2 (I := I) (basis i) (basis i)) := by
    rw [metricTracePair0SAt_eq_sum_basis
      (I := I) h basis (diagonalInvMetric μ) hhinv]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · rw [diagonalInvMetric_apply_self]
    · intro j _ hji
      rw [diagonalInvMetric_eq_zero_of_ne hji.symm, _root_.MulZeroClass.zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hμinv (i) :
      μ i * h.inner x (basis i) (basis i) = 1 := by
    have hsum :
        (∑ k, diagonalInvMetric μ i k *
            h.inner x (basis k) (basis i)) =
          μ i * h.inner x (basis i) (basis i) := by
      rw [Finset.sum_eq_single i]
      · rw [diagonalInvMetric_apply_self]
      · intro k _ hki
        rw [diagonalInvMetric_eq_zero_of_ne hki.symm, _root_.MulZeroClass.zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [← hsum]
    simpa only [if_pos] using (hhinv i i).1
  let c0 :=
    Real.sqrt
      (normSq0S (I := I) g x 2
        (metricTensor0S (I := I) h x -
          metricTensor0S (I := I) g x))
  let a0 := Real.sqrt (normSq0S (I := I) g x 2 A)
  have hmetricComp (i) :
      |h.inner x (basis i) (basis i) - 1| ≤ c0 := by
    have hb := abs_apply_le_sqrt_normSq0S
      (I := I) g x 2 basis hgON
      (metricTensor0S (I := I) h x -
        metricTensor0S (I := I) g x)
      (vec2 (I := I) (basis i) (basis i))
    have hsub :
        (metricTensor0S (I := I) h x - metricTensor0S (I := I) g x)
            (vec2 (I := I) (basis i) (basis i)) =
          h.inner x (basis i) (basis i) - g.inner x (basis i) (basis i) := by
      rfl
    rw [hsub] at hb
    simpa [c0, metricTensor0S_apply, vec2, hgON] using hb
  have hAComp (i) :
      |A (vec2 (I := I) (basis i) (basis i))| ≤ a0 := by
    have hb := abs_apply_le_sqrt_normSq0S
      (I := I) g x 2 basis hgON A
      (vec2 (I := I) (basis i) (basis i))
    simpa [a0, vec2, hgON] using hb
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hμdiff (i) : |μ i - 1| ≤ C * c0 := by
    have hid :
        μ i - 1 =
          μ i * (1 - h.inner x (basis i) (basis i)) := by
      calc
        μ i - 1 =
            μ i - μ i * h.inner x (basis i) (basis i) := by
              rw [hμinv i]
        _ = μ i * (1 - h.inner x (basis i) (basis i)) := by
              ring
    rw [hid, abs_mul, abs_of_nonneg (hμ0 i), abs_sub_comm]
    exact mul_le_mul (hμC i) (hmetricComp i) (abs_nonneg _) hC0
  have htrace :
      metricTracePair0SAt (I := I) h A -
          metricTracePair0SAt (I := I) g A =
        ∑ i, (μ i - 1) * A (vec2 (I := I) (basis i) (basis i)) := by
    rw [htrace_h, htrace_g, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [htrace]
  calc
    |∑ i, (μ i - 1) * A (vec2 (I := I) (basis i) (basis i))|
        ≤ ∑ i, |(μ i - 1) *
            A (vec2 (I := I) (basis i) (basis i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank Real (TangentSpace I x)),
          C * c0 * a0 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (hμdiff i) (hAComp i) (abs_nonneg _)
        (mul_nonneg hC0 (Real.sqrt_nonneg _))
    _ = (Module.finrank Real (TangentSpace I x) : Real) * C * c0 * a0 := by
      simp [mul_assoc]
    _ = (Module.finrank Real (TangentSpace I x) : Real) * C *
          Real.sqrt
            (normSq0S (I := I) g x 2
              (metricTensor0S (I := I) h x -
                metricTensor0S (I := I) g x)) *
          Real.sqrt (normSq0S (I := I) g x 2 A) := by
      rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.trace_sub_le_c0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.trace_sub_le_c0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.trace_sub_le_c0 ``Submission.DifferentialGeometry.Geometry.Operator.trace_sub_le_c0

theorem metricTracePair0SAt_sq_div_rank_le_normSq0S
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] [Nonempty Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x) :
    (1 / (Fintype.card Idx : Real)) *
        (metricTracePair0SAt (I := I) g A) ^ 2 <=
      normSq0S (I := I) g x 2 A := by
  classical
  have hcard : 0 < (Fintype.card Idx : Real) := by
    exact Nat.cast_pos.mpr Fintype.card_pos
  have h :=
    metricTracePair0SAt_sq_le_card_mul_normSq0S
      (I := I) g basis gInv hinv A
  have hdiv :
      (metricTracePair0SAt (I := I) g A) ^ 2 /
          (Fintype.card Idx : Real) <=
        normSq0S (I := I) g x 2 A := by
    rw [div_le_iff₀ hcard]
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hdiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_sq_div_rank_le_normSq0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_sq_div_rank_le_normSq0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_sq_div_rank_le_normSq0S ``Submission.DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_sq_div_rank_le_normSq0S

theorem metricTraceFirstTwo0SAt_eq_sum_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g T tail =
      metricTrace0S2InBasis (I := I) basis gInv T tail := by
  rw [metricTraceFirstTwo0SAt, metricTracePair0SAt_eq_sum_basis
    (I := I) g basis gInv hinv]
  unfold metricTrace0S2InBasis
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_eq_sum_basis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_eq_sum_basis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_eq_sum_basis ``Submission.DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_eq_sum_basis

theorem metricTraceLastTwo0SAt3_eq_sum_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) :
    metricTraceLastTwo0SAt3 (I := I) g T Y =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j * T (vec3 (I := I) Y (basis i) (basis j)) := by
  rw [metricTraceLastTwo0SAt3, metricTracePair0SAt_eq_sum_basis
    (I := I) g basis gInv hinv]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTraceLastTwo0SAt3_eq_sum_basis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTraceLastTwo0SAt3_eq_sum_basis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTraceLastTwo0SAt3_eq_sum_basis ``Submission.DifferentialGeometry.Geometry.Operator.metricTraceLastTwo0SAt3_eq_sum_basis

theorem metricTrace0S2InBasis_eq_metricTrace
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTrace0S2InBasis (I := I) basis gInv T tail =
      metricTraceFirstTwo0SAt (I := I) g T tail :=
  (metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv T tail).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTrace0S2InBasis_eq_metricTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTrace0S2InBasis_eq_metricTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTrace0S2InBasis_eq_metricTrace ``Submission.DifferentialGeometry.Geometry.Operator.metricTrace0S2InBasis_eq_metricTrace

theorem metricTrace0S2InBasis_eq_metricTrace0S2InBasis
    (g : SmoothRiemannianMetric I M)
    {Idx₁ Idx₂ : Type*} [Fintype Idx₁] [DecidableEq Idx₁]
    [Fintype Idx₂] [DecidableEq Idx₂]
    {x : M}
    (basis₁ : Module.Basis Idx₁ Real (TangentSpace I x))
    (gInv₁ : Idx₁ -> Idx₁ -> Real)
    (hinv₁ : MetricInverseInBasis (I := I) g x basis₁ gInv₁)
    (basis₂ : Module.Basis Idx₂ Real (TangentSpace I x))
    (gInv₂ : Idx₂ -> Idx₂ -> Real)
    (hinv₂ : MetricInverseInBasis (I := I) g x basis₂ gInv₂)
    {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTrace0S2InBasis (I := I) basis₁ gInv₁ T tail =
      metricTrace0S2InBasis (I := I) basis₂ gInv₂ T tail := by
  rw [metricTrace0S2InBasis_eq_metricTrace (I := I) g basis₁ gInv₁ hinv₁ T tail,
    metricTrace0S2InBasis_eq_metricTrace (I := I) g basis₂ gInv₂ hinv₂ T tail]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTrace0S2InBasis_eq_metricTrace0S2InBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTrace0S2InBasis_eq_metricTrace0S2InBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTrace0S2InBasis_eq_metricTrace0S2InBasis ``Submission.DifferentialGeometry.Geometry.Operator.metricTrace0S2InBasis_eq_metricTrace0S2InBasis

def metricTraceFirstTwo0STensor
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  metricTrace0S2TensorInBasis (I := I)
    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x)
    (fun k l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent (I := I) g x k
        l
        (extChartAt I x x))
    T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0STensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0STensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0STensor ``Submission.DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0STensor

@[simp]
theorem metricTraceFirstTwo0STensor_apply
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0STensor (I := I) g T tail =
      metricTraceFirstTwo0SAt (I := I) g T tail := by
  rw [metricTraceFirstTwo0STensor, metricTrace0S2TensorInBasis_apply]
  exact metricTrace0S2InBasis_eq_metricTrace (I := I) g
    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x)
    (fun k l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent (I := I) g x k
        l
        (extChartAt I x x))
    (Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) g x)
    T tail

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0STensor_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0STensor_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0STensor_apply ``Submission.DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0STensor_apply

def roughLap0STensor
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  metricTraceFirstTwo0STensor (I := I) g nabla2A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.roughLap0STensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.roughLap0STensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.roughLap0STensor ``Submission.DifferentialGeometry.Geometry.Operator.roughLap0STensor

@[simp]
theorem roughLap0STensor_apply
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    roughLap0STensor (I := I) g nabla2A tail =
      metricTraceFirstTwo0SAt (I := I) g nabla2A tail := by
  exact metricTraceFirstTwo0STensor_apply (I := I) g nabla2A tail

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.roughLap0STensor_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.roughLap0STensor_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.roughLap0STensor_apply ``Submission.DifferentialGeometry.Geometry.Operator.roughLap0STensor_apply

theorem trace_smul_leibniz
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    {s : ℕ}
    (f : Real)
    (df : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hessF : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (nabla2A nabla2fA :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) x)
    (tail : Fin s -> TangentSpace I x)
    (hleib :
      ∀ X Y : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
        nabla2fA (metricTraceInput (I := I) X Y tail) =
          hessF (metricTraceInput (I := I) X Y Fin.elim0) * A tail +
            df (fun _ : Fin 1 => X) * nablaA (Fin.cons Y tail) +
            df (fun _ : Fin 1 => Y) * nablaA (Fin.cons X tail) +
            f * nabla2A (metricTraceInput (I := I) X Y tail)) :
    metricTraceFirstTwo0SAt (I := I) g nabla2fA tail =
      metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0 * A tail +
        (∑ i : Idx, ∑ j : Idx,
          gInv i j *
            (df (fun _ : Fin 1 => basis i) *
                nablaA (Fin.cons (basis j) tail) +
              df (fun _ : Fin 1 => basis j) *
                nablaA (Fin.cons (basis i) tail))) +
        f * metricTraceFirstTwo0SAt (I := I) g nabla2A tail := by
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv
      nabla2fA tail,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv
      hessF Fin.elim0,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv
      nabla2A tail]
  simp only [metricTrace0S2InBasis]
  simp_rw [hleib]
  simp_rw [mul_add]
  simp_rw [Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum]
  ring_nf
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  ring_nf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.trace_smul_leibniz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.trace_smul_leibniz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.trace_smul_leibniz ``Submission.DifferentialGeometry.Geometry.Operator.trace_smul_leibniz

theorem trace_smul_parallel
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    {s : ℕ}
    (f : Real)
    (df : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hessF : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (nabla2A nabla2fA :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) x)
    (tail : Fin s -> TangentSpace I x)
    (hfirst : ∀ X : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
      nablaA (Fin.cons X tail) = 0)
    (hsecond : ∀ X Y : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
      nabla2A (metricTraceInput (I := I) X Y tail) = 0)
    (hleib :
      ∀ X Y : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
        nabla2fA (metricTraceInput (I := I) X Y tail) =
          hessF (metricTraceInput (I := I) X Y Fin.elim0) * A tail +
            df (fun _ : Fin 1 => X) * nablaA (Fin.cons Y tail) +
            df (fun _ : Fin 1 => Y) * nablaA (Fin.cons X tail) +
            f * nabla2A (metricTraceInput (I := I) X Y tail)) :
    metricTraceFirstTwo0SAt (I := I) g nabla2fA tail =
      metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0 * A tail := by
  rw [trace_smul_leibniz (I := I) g basis gInv hinv f
    df hessF A nablaA nabla2A nabla2fA tail hleib]
  simp only [hfirst, _root_.MulZeroClass.mul_zero, add_zero]
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis gInv hinv
      nabla2A tail]
  simp only [metricTrace0S2InBasis, hsecond, _root_.MulZeroClass.mul_zero, Finset.sum_const_zero]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.trace_smul_parallel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.trace_smul_parallel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.trace_smul_parallel ``Submission.DifferentialGeometry.Geometry.Operator.trace_smul_parallel

theorem roughLap_smul_leib
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    {s : ℕ}
    (f : Real)
    (df : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hessF : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (nabla2A nabla2fA :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) x)
    (tail : Fin s -> TangentSpace I x)
    (hleib :
      ∀ X Y : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
        nabla2fA (metricTraceInput (I := I) X Y tail) =
          hessF (metricTraceInput (I := I) X Y Fin.elim0) * A tail +
            df (fun _ : Fin 1 => X) * nablaA (Fin.cons Y tail) +
            df (fun _ : Fin 1 => Y) * nablaA (Fin.cons X tail) +
            f * nabla2A (metricTraceInput (I := I) X Y tail)) :
    roughLap0STensor (I := I) g nabla2fA tail =
      metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0 * A tail +
        (∑ i : Idx, ∑ j : Idx,
          gInv i j *
            (df (fun _ : Fin 1 => basis i) *
                nablaA (Fin.cons (basis j) tail) +
              df (fun _ : Fin 1 => basis j) *
                nablaA (Fin.cons (basis i) tail))) +
        f * roughLap0STensor (I := I) g nabla2A tail := by
  rw [roughLap0STensor_apply, roughLap0STensor_apply]
  exact trace_smul_leibniz (I := I) g basis gInv hinv
    f df hessF A nablaA nabla2A nabla2fA tail hleib

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.roughLap_smul_leib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.roughLap_smul_leib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.roughLap_smul_leib ``Submission.DifferentialGeometry.Geometry.Operator.roughLap_smul_leib

theorem roughLap_smul_par
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    {s : ℕ}
    (f : Real)
    (df : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (hessF : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (nabla2A nabla2fA :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 2) x)
    (tail : Fin s -> TangentSpace I x)
    (hfirst : ∀ X : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
      nablaA (Fin.cons X tail) = 0)
    (hsecond : ∀ X Y : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
      nabla2A (metricTraceInput (I := I) X Y tail) = 0)
    (hleib :
      ∀ X Y : TangentSpace I x, ∀ tail : Fin s -> TangentSpace I x,
        nabla2fA (metricTraceInput (I := I) X Y tail) =
          hessF (metricTraceInput (I := I) X Y Fin.elim0) * A tail +
            df (fun _ : Fin 1 => X) * nablaA (Fin.cons Y tail) +
            df (fun _ : Fin 1 => Y) * nablaA (Fin.cons X tail) +
            f * nabla2A (metricTraceInput (I := I) X Y tail)) :
    roughLap0STensor (I := I) g nabla2fA tail =
      metricTraceFirstTwo0SAt (I := I) g hessF Fin.elim0 * A tail := by
  rw [roughLap0STensor_apply]
  exact trace_smul_parallel (I := I) g basis gInv hinv
    f df hessF A nablaA nabla2A nabla2fA tail hfirst hsecond hleib

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.roughLap_smul_par then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.roughLap_smul_par"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.roughLap_smul_par ``Submission.DifferentialGeometry.Geometry.Operator.roughLap_smul_par

def roughLap0SAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) : Real :=
  metricTrace0S2InBasis (I := I) basis gInv nabla2A tail

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.roughLap0SAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.roughLap0SAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.roughLap0SAt ``Submission.DifferentialGeometry.Geometry.Operator.roughLap0SAt

def roughLap1FormAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (Y : TangentSpace I x) : Real :=
  roughLap0SAt (I := I) basis gInv (s := 1) nabla2α (fun _ : Fin 1 => Y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.roughLap1FormAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.roughLap1FormAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.roughLap1FormAt ``Submission.DifferentialGeometry.Geometry.Operator.roughLap1FormAt

def RoughLap0SRealizesMetricTraceInBasis
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) : Prop :=
  ∀ tail : Fin s -> TangentSpace I x,
    roughA tail = roughLap0SAt (I := I) basis gInv nabla2A tail

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.RoughLap0SRealizesMetricTraceInBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.RoughLap0SRealizesMetricTraceInBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.RoughLap0SRealizesMetricTraceInBasis ``Submission.DifferentialGeometry.Geometry.Operator.RoughLap0SRealizesMetricTraceInBasis

omit [FiniteDimensional ℝ E] in
theorem roughLap0SAt_eq_of_realizes
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real) {s : ℕ}
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (h : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv roughA nabla2A)
    (tail : Fin s -> TangentSpace I x) :
    roughA tail = roughLap0SAt (I := I) basis gInv nabla2A tail :=
  h tail

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.roughLap0SAt_eq_of_realizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.roughLap0SAt_eq_of_realizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.roughLap0SAt_eq_of_realizes ``Submission.DifferentialGeometry.Geometry.Operator.roughLap0SAt_eq_of_realizes

omit [FiniteDimensional ℝ E] in
theorem roughLap1FormAt_eq_of_realizes
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv (s := 1) roughα nabla2α)
    (Y : TangentSpace I x) :
    roughα (fun _ : Fin 1 => Y) =
      roughLap1FormAt (I := I) basis gInv nabla2α Y :=
  h (fun _ : Fin 1 => Y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.roughLap1FormAt_eq_of_realizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.roughLap1FormAt_eq_of_realizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.roughLap1FormAt_eq_of_realizes ``Submission.DifferentialGeometry.Geometry.Operator.roughLap1FormAt_eq_of_realizes

def metricTrace0s
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (traceT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x) : Prop :=
  ∀ tail : Fin s -> TangentSpace I x,
    traceT tail = metricTraceFirstTwo0SAt (I := I) g T tail

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metricTrace0s then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metricTrace0s"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metricTrace0s ``Submission.DifferentialGeometry.Geometry.Operator.metricTrace0s

def RoughLap0SRealizesMetricTrace
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) : Prop :=
  metricTrace0s (I := I) g nabla2A roughA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.RoughLap0SRealizesMetricTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.RoughLap0SRealizesMetricTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.RoughLap0SRealizesMetricTrace ``Submission.DifferentialGeometry.Geometry.Operator.RoughLap0SRealizesMetricTrace

def roughLap0s
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x) : Prop :=
  RoughLap0SRealizesMetricTrace (I := I) g roughA nabla2A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.roughLap0s then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.roughLap0s"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.roughLap0s ``Submission.DifferentialGeometry.Geometry.Operator.roughLap0s

theorem metric_trace_0s_iff_eq_tensor
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (traceT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x) :
    metricTrace0s (I := I) g T traceT ↔
      traceT = metricTraceFirstTwo0STensor (I := I) g T := by
  constructor
  · intro htrace
    ext tail
    rw [htrace tail, metricTraceFirstTwo0STensor_apply]
  · intro htrace tail
    rw [htrace, metricTraceFirstTwo0STensor_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metric_trace_0s_iff_eq_tensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metric_trace_0s_iff_eq_tensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metric_trace_0s_iff_eq_tensor ``Submission.DifferentialGeometry.Geometry.Operator.metric_trace_0s_iff_eq_tensor

theorem rough_lap_0s_iff_eq_tensor
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x) :
    roughLap0s (I := I) g nabla2A roughA ↔
      roughA = roughLap0STensor (I := I) g nabla2A := by
  simpa [roughLap0s, RoughLap0SRealizesMetricTrace, roughLap0STensor] using
    metric_trace_0s_iff_eq_tensor (I := I) g nabla2A roughA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.rough_lap_0s_iff_eq_tensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.rough_lap_0s_iff_eq_tensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.rough_lap_0s_iff_eq_tensor ``Submission.DifferentialGeometry.Geometry.Operator.rough_lap_0s_iff_eq_tensor

theorem roughLap0STensor_realizes
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) :
    roughLap0s (I := I) g nabla2A
      (roughLap0STensor (I := I) g nabla2A) := by
  rw [rough_lap_0s_iff_eq_tensor]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.roughLap0STensor_realizes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.roughLap0STensor_realizes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.roughLap0STensor_realizes ``Submission.DifferentialGeometry.Geometry.Operator.roughLap0STensor_realizes

def roughLapOneForm
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 x) : Prop :=
  roughLap0s (I := I) g (s := 1) nabla2α roughα

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.roughLapOneForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.roughLapOneForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.roughLapOneForm ``Submission.DifferentialGeometry.Geometry.Operator.roughLapOneForm

theorem metric_trace_0s_apply_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} {s : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (T : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (traceT : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x)
    (htrace : metricTrace0s (I := I) g T traceT)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (tail : Fin s -> TangentSpace I x) :
    traceT tail = metricTrace0S2InBasis (I := I) basis gInv T tail :=
  by
    rw [htrace tail]
    exact (metricTrace0S2InBasis_eq_metricTrace (I := I) g basis gInv hinv T tail).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.metric_trace_0s_apply_basis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.metric_trace_0s_apply_basis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.metric_trace_0s_apply_basis ``Submission.DifferentialGeometry.Geometry.Operator.metric_trace_0s_apply_basis

theorem rough_lap_0s_apply_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} {s : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (roughA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s x)
    (hrough : roughLap0s (I := I) g nabla2A roughA)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (tail : Fin s -> TangentSpace I x) :
    roughA tail = roughLap0SAt (I := I) basis gInv nabla2A tail :=
  by
    simpa [roughLap0s, roughLap0SAt] using
      metric_trace_0s_apply_basis (I := I) g basis gInv nabla2A roughA hrough hinv tail

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.rough_lap_0s_apply_basis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.rough_lap_0s_apply_basis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.rough_lap_0s_apply_basis ``Submission.DifferentialGeometry.Geometry.Operator.rough_lap_0s_apply_basis

theorem rough_lap_one_form_apply_basis
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 x)
    (hrough : roughLapOneForm (I := I) g nabla2α roughα)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv)
    (Y : TangentSpace I x) :
    roughα (fun _ : Fin 1 => Y) =
      roughLap1FormAt (I := I) basis gInv nabla2α Y :=
  by
    simpa [roughLapOneForm, roughLap0s, roughLap1FormAt, roughLap0SAt] using
      rough_lap_0s_apply_basis (I := I) g basis gInv nabla2α roughα hrough hinv
        (fun _ : Fin 1 => Y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.rough_lap_one_form_apply_basis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.rough_lap_one_form_apply_basis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.rough_lap_one_form_apply_basis ``Submission.DifferentialGeometry.Geometry.Operator.rough_lap_one_form_apply_basis

theorem rough_lap_one_form_realizes_metric_trace
    (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (roughα : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      1 x)
    (hrough : roughLapOneForm (I := I) g nabla2α roughα)
    (hinv : MetricInverseInBasis (I := I) g x basis gInv) :
    RoughLap0SRealizesMetricTraceInBasis (I := I) basis gInv
      (s := 1) roughα nabla2α := by
  intro tail
  simpa [roughLapOneForm, roughLap0s, roughLap0SAt] using
    rough_lap_0s_apply_basis (I := I) g basis gInv nabla2α roughα hrough hinv tail

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.rough_lap_one_form_realizes_metric_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.rough_lap_one_form_realizes_metric_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.rough_lap_one_form_realizes_metric_trace ``Submission.DifferentialGeometry.Geometry.Operator.rough_lap_one_form_realizes_metric_trace

end

end DifferentialGeometry.Geometry.Operator
