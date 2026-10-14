import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]


structure TransversePath (p z : M) (sphere : Set M) where
  curve : ℝ → M
  continuous : ContinuousOn curve (Set.Icc 0 1)
  start : curve 0 = p
  finish : curve 1 = z
  collar : PartialDiffeomorph IC I3 Cylinder M ∞
  collar_domain : Set.univ ×ˢ Set.Icc (-1) 1 ⊆ collar.source
  central_eq : sphere = collar '' (Set.univ ×ˢ ({0} : Set ℝ))
  crossings : Finset ℝ
  crossings_interior : ∀ s ∈ crossings, s ∈ Set.Ioo 0 1
  crossings_eq : ∀ s ∈ Set.Icc (0 : ℝ) 1, curve s ∈ sphere ↔ s ∈ crossings
  transverse : ∀ s ∈ crossings,
    deriv (fun t => (collar.symm (curve t)).2) s ≠ 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TransversePath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TransversePath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TransversePath ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TransversePath

def TransversePath.intersection {p z : M} {sphere : Set M}
    (c : TransversePath p z sphere) : ℤ :=
  ∑ s ∈ c.crossings, if 0 < deriv (fun t => (c.collar.symm (c.curve t)).2) s then 1 else -1

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TransversePath
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TransversePath.intersection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TransversePath.intersection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TransversePath.intersection ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.TransversePath.intersection


structure MinimizingArm (g : SmoothRiemannianMetric I3 M) (x : M) where
  length : ℝ
  length_pos : 0 < length
  point : ℝ → M
  start : point 0 = x
  minimizing : ∀ s ∈ Set.Icc 0 length, ∀ t ∈ Set.Icc 0 length,
    metricDistance g (point s) (point t) = |s - t|

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MinimizingArm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MinimizingArm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MinimizingArm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.MinimizingArm


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
