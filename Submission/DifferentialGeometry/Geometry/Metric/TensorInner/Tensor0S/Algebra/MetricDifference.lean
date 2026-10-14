import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M]

def metricDiffAt (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x :=
  metricTensorField (I := I) g₁ x - metricTensorField (I := I) g₂ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricDiffAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricDiffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricDiffAt ``Submission.DifferentialGeometry.PDE.RicciFlow.metricDiffAt

omit [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem metricDiffAt_apply (g₁ g₂ : SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 -> TangentSpace I x) :
    metricDiffAt (I := I) g₁ g₂ x v =
      g₁.inner x (v 0) (v 1) - g₂.inner x (v 0) (v 1) := by
  have h : metricDiffAt (I := I) g₁ g₂ x v =
      metricTensorField (I := I) g₁ x v - metricTensorField (I := I) g₂ x v :=
    Tensor0SSpace.sub_apply (I := I) 2 x
      (metricTensorField (I := I) g₁ x) (metricTensorField (I := I) g₂ x) v
  rw [h, metricTensorField_apply, metricTensorField_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricDiffAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricDiffAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricDiffAt_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.metricDiffAt_apply

omit [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem metricDiffAt_self (g : SmoothRiemannianMetric I M) (x : M) :
    metricDiffAt (I := I) g g x = 0 :=
  sub_self _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricDiffAt_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricDiffAt_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricDiffAt_self ``Submission.DifferentialGeometry.PDE.RicciFlow.metricDiffAt_self

def metricDiffSq (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) : Real :=
  normSq0S (I := I) g₁ x 2 (metricDiffAt (I := I) g₁ g₂ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricDiffSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricDiffSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricDiffSq ``Submission.DifferentialGeometry.PDE.RicciFlow.metricDiffSq

omit [SigmaCompactSpace M] [T2Space M] in
theorem metricDiffSq_def (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    metricDiffSq (I := I) g₁ g₂ x =
      normSq0S (I := I) g₁ x 2 (metricDiffAt (I := I) g₁ g₂ x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricDiffSq_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricDiffSq_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricDiffSq_def ``Submission.DifferentialGeometry.PDE.RicciFlow.metricDiffSq_def


end DifferentialGeometry.PDE.RicciFlow

end
