import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Rough
import Submission.DifferentialGeometry.Geometry.Metric.Family.Basic
import Submission.DifferentialGeometry.Geometry.Operator.Scalar.Calculus

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
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

private theorem metricTraceFirstTwo0SAt_zero
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (tail : Fin s -> TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g
        (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (s + 2) x)
        tail = 0 := by
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g
    (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x)
    (fun k l : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent (I := I) g x k
        l
        (extChartAt I x x))
    (Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) g x)
    (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    tail]
  simp [metricTrace0S2InBasis]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Operator.metricTraceFirstTwo0SAt_zero target :: scope.openDecls } }

def tensorHeat0SMetricAt
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  roughLap0STensor (I := I) g nabla2A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorHeat0SMetricAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorHeat0SMetricAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorHeat0SMetricAt ``Submission.DifferentialGeometry.Geometry.Operator.tensorHeat0SMetricAt

@[simp]
theorem tensorHeat0SMetricAt_apply
    (g : SmoothRiemannianMetric I M)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    tensorHeat0SMetricAt (I := I) g nabla2A tail =
      metricTraceFirstTwo0SAt (I := I) g nabla2A tail := by
  exact roughLap0STensor_apply (I := I) g nabla2A tail

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorHeat0SMetricAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorHeat0SMetricAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorHeat0SMetricAt_apply ``Submission.DifferentialGeometry.Geometry.Operator.tensorHeat0SMetricAt_apply

def tensorHeat0SAt
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  tensorHeat0SMetricAt (I := I) (G.metric t) nabla2A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorHeat0SAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorHeat0SAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorHeat0SAt ``Submission.DifferentialGeometry.Geometry.Operator.tensorHeat0SAt

@[simp]
theorem tensorHeat0SAt_apply
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (tail : Fin s -> TangentSpace I x) :
    tensorHeat0SAt (I := I) G t nabla2A tail =
      metricTraceFirstTwo0SAt (I := I) (G.metric t) nabla2A tail := by
  exact tensorHeat0SMetricAt_apply (I := I) (G.metric t) nabla2A tail

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorHeat0SAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorHeat0SAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorHeat0SAt_apply ``Submission.DifferentialGeometry.Geometry.Operator.tensorHeat0SAt_apply

def tensorDrift0SAt
    (X : (x : M) -> TangentSpace I x)
    {x : M} {s : ℕ}
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x nablaA (X x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorDrift0SAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorDrift0SAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorDrift0SAt ``Submission.DifferentialGeometry.Geometry.Operator.tensorDrift0SAt

omit [FiniteDimensional ℝ E] in
@[simp]
theorem tensorDrift0SAt_apply
    (X : (x : M) -> TangentSpace I x)
    {x : M} {s : ℕ}
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (tail : Fin s -> TangentSpace I x) :
    tensorDrift0SAt (I := I) X nablaA tail =
      nablaA (Fin.cons (X x) tail) := by
  exact Tensor0SBundle.tensor0S_curry_apply_cons (I := I) s nablaA (X x) tail

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorDrift0SAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorDrift0SAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorDrift0SAt_apply ``Submission.DifferentialGeometry.Geometry.Operator.tensorDrift0SAt_apply

def tensorHeatWithDrift0SMetricAt
    (g : SmoothRiemannianMetric I M)
    (X : (x : M) -> TangentSpace I x)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  tensorHeat0SMetricAt (I := I) g nabla2A + tensorDrift0SAt (I := I) X nablaA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift0SMetricAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift0SMetricAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift0SMetricAt ``Submission.DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift0SMetricAt

@[simp]
theorem tensorHeatWithDrift0SMetricAt_apply
    (g : SmoothRiemannianMetric I M)
    (X : (x : M) -> TangentSpace I x)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (tail : Fin s -> TangentSpace I x) :
    tensorHeatWithDrift0SMetricAt (I := I) g X nabla2A nablaA tail =
      metricTraceFirstTwo0SAt (I := I) g nabla2A tail +
        nablaA (Fin.cons (X x) tail) := by
  simp [tensorHeatWithDrift0SMetricAt]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift0SMetricAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift0SMetricAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift0SMetricAt_apply ``Submission.DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift0SMetricAt_apply

def tensorHeatWithDrift0SAt
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x :=
  tensorHeatWithDrift0SMetricAt (I := I) (G.metric t) X nabla2A nablaA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift0SAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift0SAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift0SAt ``Submission.DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift0SAt

@[simp]
theorem tensorHeatWithDrift0SAt_apply
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {x : M} {s : ℕ}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 2) x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) x)
    (tail : Fin s -> TangentSpace I x) :
    tensorHeatWithDrift0SAt (I := I) G t X nabla2A nablaA tail =
      metricTraceFirstTwo0SAt (I := I) (G.metric t) nabla2A tail +
        nablaA (Fin.cons (X x) tail) := by
  exact tensorHeatWithDrift0SMetricAt_apply (I := I) (G.metric t) X nabla2A nablaA tail

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift0SAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift0SAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift0SAt_apply ``Submission.DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift0SAt_apply

def tensorHeatWithDrift2MetricAt
    (g : SmoothRiemannianMetric I M)
    (X : (x : M) -> TangentSpace I x)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  tensorHeatWithDrift0SMetricAt (I := I) (s := 2) g X nabla2A nablaA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2MetricAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2MetricAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2MetricAt ``Submission.DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2MetricAt

@[simp]
theorem tensorHeatWithDrift2MetricAt_apply
    (g : SmoothRiemannianMetric I M)
    (X : (x : M) -> TangentSpace I x)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (v : Fin 2 -> TangentSpace I x) :
    tensorHeatWithDrift2MetricAt (I := I) g X nabla2A nablaA v =
      metricTraceFirstTwo0SAt (I := I) g nabla2A v +
        nablaA (Fin.cons (X x) v) := by
  simp [tensorHeatWithDrift2MetricAt]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2MetricAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2MetricAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2MetricAt_apply ``Submission.DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2MetricAt_apply

def tensorHeatWithDrift2At
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  tensorHeatWithDrift2MetricAt (I := I) (G.metric t) X nabla2A nablaA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2At then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2At"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2At ``Submission.DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2At

@[simp]
theorem tensorHeatWithDrift2At_apply
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (v : Fin 2 -> TangentSpace I x) :
    tensorHeatWithDrift2At (I := I) G t X nabla2A nablaA v =
      metricTraceFirstTwo0SAt (I := I) (G.metric t) nabla2A v +
        nablaA (Fin.cons (X x) v) := by
  exact tensorHeatWithDrift2MetricAt_apply (I := I) (G.metric t) X nabla2A nablaA v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2At_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2At_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2At_apply ``Submission.DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2At_apply

def tensorHeatWithDrift2QuadMetricAt
    (g : SmoothRiemannianMetric I M)
    (X : (x : M) -> TangentSpace I x)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (v : TangentSpace I x) : Real :=
  tensorHeatWithDrift2MetricAt (I := I) g X nabla2A nablaA (vec2 v v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadMetricAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadMetricAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadMetricAt ``Submission.DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadMetricAt

@[simp]
theorem tensorHeatWithDrift2QuadMetricAt_eq
    (g : SmoothRiemannianMetric I M)
    (X : (x : M) -> TangentSpace I x)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (v : TangentSpace I x) :
    tensorHeatWithDrift2QuadMetricAt (I := I) g X nabla2A nablaA v =
      metricTraceFirstTwo0SAt (I := I) g nabla2A (vec2 v v) +
        nablaA (Fin.cons (X x) (vec2 v v)) := by
  simp [tensorHeatWithDrift2QuadMetricAt]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadMetricAt_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadMetricAt_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadMetricAt_eq ``Submission.DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadMetricAt_eq

theorem tensorHeatWithDrift2QuadMetricAt_zero_drift
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (v : TangentSpace I x) :
    tensorHeatWithDrift2QuadMetricAt (I := I) g
        (fun _y : M => 0) nabla2A nablaA v =
      metricTraceFirstTwo0SAt (I := I) g nabla2A (vec2 v v) := by
  rw [tensorHeatWithDrift2QuadMetricAt_eq]
  have hzero :
      nablaA (Fin.cons (n := 2)
          (α := fun _ : Fin 3 => TangentSpace I x)
          (0 : TangentSpace I x) (vec2 (I := I) v v)) = 0 := by
    simpa using
      Tensor0SSpace.map_update_smul nablaA
        (Fin.cons (n := 2) (α := fun _ : Fin 3 => TangentSpace I x)
          (0 : TangentSpace I x) (vec2 (I := I) v v))
        (0 : Fin 3) (0 : Real) (0 : TangentSpace I x)
  simpa using hzero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadMetricAt_zero_drift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadMetricAt_zero_drift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadMetricAt_zero_drift ``Submission.DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadMetricAt_zero_drift

theorem heatQuad_eq_parts
    (g : SmoothRiemannianMetric I M)
    (X : (x : M) -> TangentSpace I x)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (v : TangentSpace I x)
    (laplacian drift : Real)
    (hlap :
      metricTraceFirstTwo0SAt (I := I) g nabla2A (vec2 v v) = laplacian)
    (hdrift : nablaA (Fin.cons (X x) (vec2 v v)) = drift) :
    tensorHeatWithDrift2QuadMetricAt (I := I) g X nabla2A nablaA v =
      laplacian + drift := by
  rw [tensorHeatWithDrift2QuadMetricAt_eq, hlap, hdrift]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.heatQuad_eq_parts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.heatQuad_eq_parts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.heatQuad_eq_parts ``Submission.DifferentialGeometry.Geometry.Operator.heatQuad_eq_parts

theorem tensorHeatWithDrift2QuadMetricAt_zero
    (g : SmoothRiemannianMetric I M)
    (X : (x : M) -> TangentSpace I x)
    {x : M} (v : TangentSpace I x) :
    tensorHeatWithDrift2QuadMetricAt (I := I) g X
        (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          4 x)
        (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          3 x)
        v = 0 := by
  rw [tensorHeatWithDrift2QuadMetricAt_eq]
  rw [metricTraceFirstTwo0SAt_zero]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadMetricAt_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadMetricAt_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadMetricAt_zero ``Submission.DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadMetricAt_zero

def tensorHeatWithDrift2QuadAt
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (v : TangentSpace I x) : Real :=
  tensorHeatWithDrift2QuadMetricAt (I := I) (G.metric t) X nabla2A nablaA v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadAt ``Submission.DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadAt

@[simp]
theorem tensorHeatWithDrift2QuadAt_eq
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {x : M}
    (nabla2A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 x)
    (nablaA : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 x)
    (v : TangentSpace I x) :
    tensorHeatWithDrift2QuadAt (I := I) G t X nabla2A nablaA v =
      metricTraceFirstTwo0SAt (I := I) (G.metric t) nabla2A (vec2 v v) +
        nablaA (Fin.cons (X x) (vec2 v v)) := by
  exact tensorHeatWithDrift2QuadMetricAt_eq (I := I) (G.metric t) X nabla2A nablaA v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadAt_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadAt_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadAt_eq ``Submission.DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadAt_eq

theorem tensorHeatWithDrift2QuadAt_zero
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {x : M} (v : TangentSpace I x) :
    tensorHeatWithDrift2QuadAt (I := I) G t X
        (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          4 x)
        (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          3 x)
        v = 0 := by
  rw [tensorHeatWithDrift2QuadAt_eq]
  rw [metricTraceFirstTwo0SAt_zero]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadAt_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadAt_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadAt_zero ``Submission.DifferentialGeometry.Geometry.Operator.tensorHeatWithDrift2QuadAt_zero

end

end DifferentialGeometry.Geometry.Operator
