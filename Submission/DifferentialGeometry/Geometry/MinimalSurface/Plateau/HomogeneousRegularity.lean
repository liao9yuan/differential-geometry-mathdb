import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import Submission.DifferentialGeometry.Geometry.Measure.Area.ManifoldLipschitz
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.DifferentialGeometry.Geometry.Metric.Completeness.PseudoEMetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Set
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

abbrev plateauCoordinateSpace := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.plateauCoordinateSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.plateauCoordinateSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.plateauCoordinateSpace ``Submission.DifferentialGeometry.Geometry.plateauCoordinateSpace

def plateauOpenCube : Set plateauCoordinateSpace := {y | ∀ i, |y i| < 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.plateauOpenCube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.plateauOpenCube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.plateauOpenCube ``Submission.DifferentialGeometry.Geometry.plateauOpenCube
def plateauClosedCube : Set plateauCoordinateSpace := {y | ∀ i, |y i| ≤ 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.plateauClosedCube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.plateauClosedCube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.plateauClosedCube ``Submission.DifferentialGeometry.Geometry.plateauClosedCube

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]


def plateauChartCoefficient (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (ψ : OpenPartialHomeomorph plateauCoordinateSpace M) (i j : Fin 3)
    (y : plateauCoordinateSpace) : ℝ :=
  g.inner (ψ y)
    (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ψ y (EuclideanSpace.single i (1 : ℝ)))
    (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ψ y (EuclideanSpace.single j (1 : ℝ)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.plateauChartCoefficient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.plateauChartCoefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.plateauChartCoefficient ``Submission.DifferentialGeometry.Geometry.plateauChartCoefficient




def HomogeneouslyRegularMetric (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) : Prop :=
  ∃ m A : ℝ, 0 < m ∧ m ≤ A ∧
    ∃ ψ : M → OpenPartialHomeomorph plateauCoordinateSpace M,
      (∀ p, plateauClosedCube ⊆ (ψ p).source ∧ ψ p 0 = p ∧
        ContMDiffOn 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ∞ (ψ p) (ψ p).source ∧
        ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, plateauCoordinateSpace) ∞ (ψ p).symm (ψ p).target ∧
        ∀ y ∈ plateauOpenCube, ∀ ξ : plateauCoordinateSpace,
          m * ‖ξ‖ ^ 2 ≤ g.inner (ψ p y)
            (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) (ψ p) y ξ)
            (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) (ψ p) y ξ) ∧
          g.inner (ψ p y)
            (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) (ψ p) y ξ)
            (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) (ψ p) y ξ) ≤ A * ‖ξ‖ ^ 2) ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p i j y, y ∈ plateauOpenCube →
        ‖iteratedFDeriv ℝ k (plateauChartCoefficient g (ψ p) i j) y‖ ≤ C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.HomogeneouslyRegularMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.HomogeneouslyRegularMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.HomogeneouslyRegularMetric ``Submission.DifferentialGeometry.Geometry.HomogeneouslyRegularMetric



end DifferentialGeometry.Geometry
