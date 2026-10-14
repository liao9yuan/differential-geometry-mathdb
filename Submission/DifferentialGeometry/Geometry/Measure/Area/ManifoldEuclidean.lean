import Submission.DifferentialGeometry.Geometry.Measure.Area.Manifold
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]



def standardEuclideanMetric (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    SmoothRiemannianMetric 𝓘(ℝ, F) F where
  inner := (riemannianMetricVectorSpace F).inner
  symm := (riemannianMetricVectorSpace F).symm
  pos := (riemannianMetricVectorSpace F).pos
  isVonNBounded := (riemannianMetricVectorSpace F).isVonNBounded
  contMDiff := (riemannianMetricVectorSpace F).contMDiff.of_le le_top

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.standardEuclideanMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.standardEuclideanMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.standardEuclideanMetric ``Submission.DifferentialGeometry.Geometry.standardEuclideanMetric

theorem riemannianAreaDensity_standardEuclideanMetric (u : ℂ → F) (z : ℂ) :
    riemannianAreaDensity (standardEuclideanMetric F) u z = euclideanAreaDensity u z := by
  simp only [riemannianAreaDensity, mfderiv_eq_fderiv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianAreaDensity_standardEuclideanMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianAreaDensity_standardEuclideanMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianAreaDensity_standardEuclideanMetric ``Submission.DifferentialGeometry.Geometry.riemannianAreaDensity_standardEuclideanMetric

theorem riemannianArea_standardEuclideanMetric (u : ℂ → F) (s : Set ℂ) :
    riemannianArea (standardEuclideanMetric F) u s = euclideanArea u s := by
  simp only [riemannianArea, riemannianAreaDensity_standardEuclideanMetric, euclideanArea]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianArea_standardEuclideanMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianArea_standardEuclideanMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianArea_standardEuclideanMetric ``Submission.DifferentialGeometry.Geometry.riemannianArea_standardEuclideanMetric

theorem riemannianDiskArea_standardEuclideanMetric (u : closedDisk → F) :
    riemannianDiskArea (standardEuclideanMetric F) u = euclideanDiskArea u :=
  riemannianArea_standardEuclideanMetric _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianDiskArea_standardEuclideanMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianDiskArea_standardEuclideanMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianDiskArea_standardEuclideanMetric ``Submission.DifferentialGeometry.Geometry.riemannianDiskArea_standardEuclideanMetric

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_standardEuclideanMetric (x y : F) :
    DifferentialGeometry.riemannianEDistOf
      (standardEuclideanMetric F) x y = _root_.EDist.edist x y := by
  change Manifold.riemannianEDist 𝓘(ℝ, F) x y = _root_.EDist.edist x y
  exact (IsRiemannianManifold.out x y).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianEDistOf_standardEuclideanMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianEDistOf_standardEuclideanMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianEDistOf_standardEuclideanMetric ``Submission.DifferentialGeometry.Geometry.riemannianEDistOf_standardEuclideanMetric

end DifferentialGeometry.Geometry
