import Batteries.Tactic.Alias
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.SectionalCone
import Submission.DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Analysis.Convex
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M]

def hasNonnegativeSectionalCurvature
    (g : SmoothRiemannianMetric I M) : Prop :=
  ∀ x : M, metricRm04At (I := I) (M := M) g x ∈
    tensor04SectionalNonnegativeCone (I := I) (M := M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.hasNonnegativeSectionalCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.hasNonnegativeSectionalCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.hasNonnegativeSectionalCurvature ``Submission.DifferentialGeometry.Geometry.hasNonnegativeSectionalCurvature

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
theorem hasNonnegativeSectionalCurvature_iff
    (g : SmoothRiemannianMetric I M) :
    hasNonnegativeSectionalCurvature (I := I) g ↔
      ∀ x : M, ∀ W T : TangentSpace I x,
        0 ≤ metricRm04StandardAt (I := I) (M := M) g x W T T W := by
  constructor
  · intro h x
    exact (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
      (I := I) (M := M) g x).mp (h x)
  · intro h x
    exact (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
      (I := I) (M := M) g x).mpr (h x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.hasNonnegativeSectionalCurvature_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.hasNonnegativeSectionalCurvature_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.hasNonnegativeSectionalCurvature_iff ``Submission.DifferentialGeometry.Geometry.hasNonnegativeSectionalCurvature_iff

omit [SigmaCompactSpace M] in
theorem riemann_contraction_nonneg
    {g : SmoothRiemannianMetric I M}
    (hsec : hasNonnegativeSectionalCurvature (I := I) g)
    (x : M) (W T : TangentSpace I x) :
    0 ≤ g.inner x W
      (riemannOp (cov := LeviCivita (I := I) g) x W T T) := by
  have hRm : 0 ≤ metricRm04StandardAt (I := I) (M := M) g x W T T W :=
    (hasNonnegativeSectionalCurvature_iff (I := I) g).mp hsec x W T
  rwa [rm04_eq_inner_riem (I := I) (M := M) g x W T T W] at hRm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemann_contraction_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemann_contraction_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemann_contraction_nonneg ``Submission.DifferentialGeometry.Geometry.riemann_contraction_nonneg

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry

@[reducible] alias HasNonnegativeSectionalCurvature := DifferentialGeometry.Geometry.hasNonnegativeSectionalCurvature

end DifferentialGeometry.Geometry
