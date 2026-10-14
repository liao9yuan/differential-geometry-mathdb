import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Family.Basic
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.FieldComponents

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Connection

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def metricVariationComponent
    (v : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x : M) (X Y : TangentSpace I x) : Real :=
  v x (fun q : Fin 2 => if q = 0 then X else Y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.metricVariationComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.metricVariationComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.metricVariationComponent ``Submission.DifferentialGeometry.Geometry.Connection.metricVariationComponent

structure MetricPotentialVariationPath
    (g : SmoothRiemannianMetric I M) (potential : M -> Real) where
  connectionFamily :
    DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real
  potentialPath : Real -> M -> Real
  base : Real
  metricBase : connectionFamily.metric base = g
  potentialBase : potentialPath base = potential

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.MetricPotentialVariationPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.MetricPotentialVariationPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.MetricPotentialVariationPath ``Submission.DifferentialGeometry.Geometry.Connection.MetricPotentialVariationPath

namespace MetricPotentialVariationPath

variable {g : SmoothRiemannianMetric I M} {potential : M -> Real}

omit [FiniteDimensional ℝ E] in
@[simp] theorem metric_base
    (path : MetricPotentialVariationPath (I := I) g potential) :
    path.connectionFamily.metric path.base = g :=
  path.metricBase

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.MetricPotentialVariationPath.metric_base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.MetricPotentialVariationPath.metric_base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.MetricPotentialVariationPath.metric_base ``Submission.DifferentialGeometry.Geometry.Connection.MetricPotentialVariationPath.metric_base

omit [FiniteDimensional ℝ E] in
@[simp] theorem potential_base
    (path : MetricPotentialVariationPath (I := I) g potential) :
    path.potentialPath path.base = potential :=
  path.potentialBase

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.MetricPotentialVariationPath.potential_base then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.MetricPotentialVariationPath.potential_base"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.MetricPotentialVariationPath.potential_base ``Submission.DifferentialGeometry.Geometry.Connection.MetricPotentialVariationPath.potential_base

end MetricPotentialVariationPath

structure IsMetricPotentialVariationPath
    {g : SmoothRiemannianMetric I M} {potential : M -> Real}
    (path : MetricPotentialVariationPath (I := I) g potential)
    (metricVariation :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2)
    (potentialVariation : M -> Real) : Prop where
  leviCivita :
    ∀ s : Real,
      DifferentialGeometry.Geometry.Connection.IsLeviCivita (I := I) (path.connectionFamily.connection s)
        (path.connectionFamily.metric s)
  metric_deriv :
    ∀ x : M, ∀ X Y : TangentSpace I x,
      HasDerivAt
        (fun s : Real => (path.connectionFamily.metric s).inner x X Y)
        (metricVariationComponent (I := I) metricVariation x X Y)
        path.base
  potential_deriv :
    ∀ x : M,
      HasDerivAt (fun s : Real => path.potentialPath s x)
        (potentialVariation x) path.base

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.IsMetricPotentialVariationPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.IsMetricPotentialVariationPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.IsMetricPotentialVariationPath ``Submission.DifferentialGeometry.Geometry.Connection.IsMetricPotentialVariationPath

end DifferentialGeometry.Geometry.Connection
