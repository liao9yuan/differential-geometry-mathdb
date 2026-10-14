import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric
import Mathlib.LinearAlgebra.Trace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section


open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

def adjointRS
    {g : SmoothRiemannianMetric I M} {x : M}
    (r s : Nat) (A : TensorRSSpace r s I x) :
    Tensor0SSpace s I x →ₗ[Real] Tensor0SSpace r I x :=
  MetricFiberData.adjoint
    (tensor0SMetricData (I := I) g x r)
    (tensor0SMetricData (I := I) g x s)
    A.toLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.adjointRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.adjointRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.adjointRS ``Submission.DifferentialGeometry.Tensor0SBundle.adjointRS

theorem adjointRS_inner
    {g : SmoothRiemannianMetric I M} {x : M}
    (r s : Nat) (A : TensorRSSpace r s I x)
    (Y : Tensor0SSpace s I x) (X : Tensor0SSpace r I x) :
    inner0S (I := I) g x r (adjointRS (I := I) (g := g) (x := x) r s A Y) X =
      inner0S (I := I) g x s Y (A X) := by
  change (tensor0SMetricData (I := I) g x r).flat
      (((tensor0SMetricData (I := I) g x r).adjoint
        (tensor0SMetricData (I := I) g x s) A.toLinearMap) Y) X =
    (tensor0SMetricData (I := I) g x s).flat Y (A.toLinearMap X)
  exact MetricFiberData.adjoint_inner
    (tensor0SMetricData (I := I) g x r)
    (tensor0SMetricData (I := I) g x s)
    A.toLinearMap Y X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.adjointRS_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.adjointRS_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.adjointRS_inner ``Submission.DifferentialGeometry.Tensor0SBundle.adjointRS_inner

def innerRS
    {g : SmoothRiemannianMetric I M} {x : M}
    (r s : Nat) (A B : TensorRSSpace r s I x) : Real :=
  LinearMap.trace Real (Tensor0SSpace r I x)
    ((adjointRS (I := I) (g := g) (x := x) r s A).comp B.toLinearMap)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.innerRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.innerRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.innerRS ``Submission.DifferentialGeometry.Tensor0SBundle.innerRS

@[simp] theorem innerRS_eq_trace
    {g : SmoothRiemannianMetric I M} {x : M}
    (r s : Nat) (A B : TensorRSSpace r s I x) :
    innerRS (I := I) (g := g) (x := x) r s A B =
      LinearMap.trace Real (Tensor0SSpace r I x)
        ((adjointRS (I := I) (g := g) (x := x) r s A).comp B.toLinearMap) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.innerRS_eq_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.innerRS_eq_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.innerRS_eq_trace ``Submission.DifferentialGeometry.Tensor0SBundle.innerRS_eq_trace

def normSqRS
    {g : SmoothRiemannianMetric I M} {x : M}
    (r s : Nat) (A : TensorRSSpace r s I x) : Real :=
  innerRS (I := I) (g := g) (x := x) r s A A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.normSqRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.normSqRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.normSqRS ``Submission.DifferentialGeometry.Tensor0SBundle.normSqRS

@[simp] theorem normSqRS_eq_inner
    {g : SmoothRiemannianMetric I M} {x : M}
    (r s : Nat) (A : TensorRSSpace r s I x) :
    normSqRS (I := I) (g := g) (x := x) r s A =
      innerRS (I := I) (g := g) (x := x) r s A A := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.normSqRS_eq_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.normSqRS_eq_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.normSqRS_eq_inner ``Submission.DifferentialGeometry.Tensor0SBundle.normSqRS_eq_inner

abbrev TensorRSTimeField
    (I : ModelWithCorners Real E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (Time : Type*) (r s : Nat) :=
  Time -> (x : M) -> TensorRSSpace r s I x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TensorRSTimeField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TensorRSTimeField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TensorRSTimeField ``Submission.DifferentialGeometry.Tensor0SBundle.TensorRSTimeField

def tensorNormSqRS
    (g : Time -> SmoothRiemannianMetric I M)
    {r s : Nat}
    (A : TensorRSTimeField I M Time r s) :
    Time -> M -> Real :=
  fun t x => normSqRS (I := I) (g := g t) (x := x) r s (A t x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.tensorNormSqRS then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.tensorNormSqRS"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.tensorNormSqRS ``Submission.DifferentialGeometry.Tensor0SBundle.tensorNormSqRS

end

end Tensor0SBundle
end DifferentialGeometry
