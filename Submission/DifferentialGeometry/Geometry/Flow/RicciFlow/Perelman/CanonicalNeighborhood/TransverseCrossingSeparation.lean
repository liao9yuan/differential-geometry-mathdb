import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseCrossingSide

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
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation (SphereSides TwoSidedSeparation)

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]

omit [IsManifold I3 ∞ M] in
theorem not_isPreconnected_compl_and_not_mem_connectedComponentIn_of_twoSidedSeparation
    {sphere : Set M} (d : TwoSidedSeparation sphere) :
    ¬ IsPreconnected sphereᶜ ∧
      ∀ {p z : M}, p ∉ sphere → z ∉ sphere → (c : TransversePath p z sphere) →
        (c.intersection = 1 ∨ c.intersection = -1) →
          z ∉ connectedComponentIn sphereᶜ p :=
  ⟨d.not_isPreconnected_compl, fun hp hz c hint =>
    c.not_mem_connectedComponentIn_of_intersection d hp hz hint⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_isPreconnected_compl_and_not_mem_connectedComponentIn_of_twoSidedSeparation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_isPreconnected_compl_and_not_mem_connectedComponentIn_of_twoSidedSeparation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_isPreconnected_compl_and_not_mem_connectedComponentIn_of_twoSidedSeparation ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_isPreconnected_compl_and_not_mem_connectedComponentIn_of_twoSidedSeparation

omit [IsManifold I3 ∞ M] in
theorem not_isPreconnected_compl_and_not_mem_connectedComponentIn_of_sphereSides
    {sphere : Set M} (d : SphereSides sphere) :
    ¬ IsPreconnected sphereᶜ ∧
      ∀ {p z : M}, p ∉ sphere → z ∉ sphere → (c : TransversePath p z sphere) →
        (c.intersection = 1 ∨ c.intersection = -1) →
          z ∉ connectedComponentIn sphereᶜ p :=
  not_isPreconnected_compl_and_not_mem_connectedComponentIn_of_twoSidedSeparation
    d.toTwoSidedSeparation

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_isPreconnected_compl_and_not_mem_connectedComponentIn_of_sphereSides then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_isPreconnected_compl_and_not_mem_connectedComponentIn_of_sphereSides"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_isPreconnected_compl_and_not_mem_connectedComponentIn_of_sphereSides ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_isPreconnected_compl_and_not_mem_connectedComponentIn_of_sphereSides

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

omit [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] in
theorem open_nonnegative_sphere_separation
    (P : PointedRiemannianManifold.{u, 0, 0} I3)
    (f : Sphere 2 → P.M) (d : TwoSidedSeparation (Set.range f)) :
    ¬ IsPreconnected (Set.range f)ᶜ ∧
      ∀ p z : P.M, p ∉ Set.range f → z ∉ Set.range f →
        ∀ c : TransversePath p z (Set.range f),
          (c.intersection = 1 ∨ c.intersection = -1) →
            z ∉ connectedComponentIn (Set.range f)ᶜ p :=
  not_isPreconnected_compl_and_not_mem_connectedComponentIn_of_twoSidedSeparation d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.open_nonnegative_sphere_separation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.open_nonnegative_sphere_separation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.open_nonnegative_sphere_separation ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.open_nonnegative_sphere_separation

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
