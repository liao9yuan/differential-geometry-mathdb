import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Submission.DifferentialGeometry.Topology.SphereSeparation.StandardSphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SphereSeparation

structure SmoothSideClosure
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    (B S : Set N) where

  chartedSpace : ChartedSpace (EuclideanHalfSpace 3) (closure B)

  isManifold : let _ := chartedSpace
    IsManifold (𝓡∂ 3) ∞ (closure B)


  inclusion_isSmoothEmbedding : let _ := chartedSpace
    Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓘(ℝ, EuclideanThree)) ∞
      (Subtype.val : closure B → N)

  interior_image : let _ := chartedSpace
    Subtype.val '' (𝓡∂ 3).interior (closure B) = B

  boundary_image : let _ := chartedSpace
    Subtype.val '' (𝓡∂ 3).boundary (closure B) = S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SmoothSideClosure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SmoothSideClosure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SmoothSideClosure ``Submission.DifferentialGeometry.Topology.SphereSeparation.SmoothSideClosure

structure SmoothSphereSides
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    (S : Set N) extends SphereSides S where
  compactClosureSmooth : SmoothSideClosure toSphereSides.compactSide S
  endClosureSmooth : SmoothSideClosure toSphereSides.endSide S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SmoothSphereSides then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SmoothSphereSides"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SmoothSphereSides ``Submission.DifferentialGeometry.Topology.SphereSeparation.SmoothSphereSides

namespace SmoothSphereSides

variable {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
  {S : Set N}

def sides (d : SmoothSphereSides S) : SphereSides S := d.toSphereSides

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SmoothSphereSides.sides then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SmoothSphereSides.sides"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SmoothSphereSides.sides ``Submission.DifferentialGeometry.Topology.SphereSeparation.SmoothSphereSides.sides

end SmoothSphereSides

end DifferentialGeometry.Topology.SphereSeparation
