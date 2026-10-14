import Submission.DifferentialGeometry.Geometry.Curvature.Sections.Connection
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Sectional

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

def positiveRicciMetric (g : SmoothRiemannianMetric I M) : Prop :=
  ∀ x : M, ∀ v : TangentSpace I x, v ≠ 0 →
    0 < metricRicciAt (I := I) (M := M) g x (vec2 (I := I) v v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.positiveRicciMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.positiveRicciMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.positiveRicciMetric ``Submission.DifferentialGeometry.Geometry.Curvature.positiveRicciMetric

def admitsPositiveRicci : Prop :=
  ∃ g : SmoothRiemannianMetric I M, positiveRicciMetric (I := I) (M := M) g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.admitsPositiveRicci then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.admitsPositiveRicci"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.admitsPositiveRicci ``Submission.DifferentialGeometry.Geometry.Curvature.admitsPositiveRicci

def constantPositiveSectionalCurvatureMetric
    (g : SmoothRiemannianMetric I M) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StandardAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.constantPositiveSectionalCurvatureMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.constantPositiveSectionalCurvatureMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.constantPositiveSectionalCurvatureMetric ``Submission.DifferentialGeometry.Geometry.Curvature.constantPositiveSectionalCurvatureMetric

def admitsConstantPositiveSectionalCurvature : Prop :=
  ∃ g : SmoothRiemannianMetric I M,
    constantPositiveSectionalCurvatureMetric (I := I) (M := M) g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.admitsConstantPositiveSectionalCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.admitsConstantPositiveSectionalCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.admitsConstantPositiveSectionalCurvature ``Submission.DifferentialGeometry.Geometry.Curvature.admitsConstantPositiveSectionalCurvature

end DifferentialGeometry.Geometry.Curvature
