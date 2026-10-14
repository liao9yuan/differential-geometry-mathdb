import Submission.DifferentialGeometry.Geometry.Measure.Area.Manifold
import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission










noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]


def diskMapPartial (U : ℂ → M) (z v : ℂ) : TangentSpace 𝓘(ℝ, E) (U z) :=
  mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapPartial ``Submission.DifferentialGeometry.Geometry.diskMapPartial



def DiskMapConformalAt (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z : ℂ) : Prop :=
  g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z Complex.I) = 0 ∧
    g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) =
      g.inner (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskMapConformalAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskMapConformalAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskMapConformalAt ``Submission.DifferentialGeometry.Geometry.DiskMapConformalAt



def diskMapCovariantPartial (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z v w : ℂ) : TangentSpace 𝓘(ℝ, E) (U z) :=
  covDerivAlong g (fun t : ℝ => U (z + t • v))
    (fun t : ℝ => diskMapPartial U (z + t • v) w) 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapCovariantPartial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapCovariantPartial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapCovariantPartial ``Submission.DifferentialGeometry.Geometry.diskMapCovariantPartial



def diskMapTension (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z : ℂ) : TangentSpace 𝓘(ℝ, E) (U z) :=
  diskMapCovariantPartial g U z 1 1 + diskMapCovariantPartial g U z Complex.I Complex.I

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapTension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapTension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapTension ``Submission.DifferentialGeometry.Geometry.diskMapTension


def diskMapEnergyDensity (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z : ℂ) : ℝ :=
  (g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) +
    g.inner (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)) / 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapEnergyDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapEnergyDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapEnergyDensity ``Submission.DifferentialGeometry.Geometry.diskMapEnergyDensity


def DiskSmoothInterior (u : C(closedDisk, M)) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u) (Metric.ball 0 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskSmoothInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskSmoothInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskSmoothInterior ``Submission.DifferentialGeometry.Geometry.DiskSmoothInterior



def DiskSmoothUpToBoundary (u : C(closedDisk, M)) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u) (Metric.closedBall 0 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.DiskSmoothUpToBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.DiskSmoothUpToBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.DiskSmoothUpToBoundary ``Submission.DifferentialGeometry.Geometry.DiskSmoothUpToBoundary

end DifferentialGeometry.Geometry
