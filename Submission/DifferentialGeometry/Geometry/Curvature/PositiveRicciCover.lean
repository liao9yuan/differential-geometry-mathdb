import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.PositiveRicci.Hamilton
import Submission.DifferentialGeometry.Geometry.Curvature.SphericalCover

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Topology.ThreeManifold
open _root_.Submission.DifferentialGeometry.Topology

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [SigmaCompactSpace M]

theorem exists_spherical_cover_of_admits_positive_ricci
    (hM : isClosedThreeManifold (I := 𝓡 3) (M := M))
    (hpos : admitsPositiveRicci (I := 𝓡 3) (M := M)) :
    (∃ p : SphereThree → M, IsCoveringMap p ∧ Function.Surjective p ∧
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p) ∧
      ∀ x : M, Finite (FundamentalGroup M x) := by
  exact exists_spherical_cover_of_admits_constant_positive_sectional_curvature hM
    (DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamilton_positive_ricci
      (I := 𝓡 3) (M := M) hM hpos).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_spherical_cover_of_admits_positive_ricci then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_spherical_cover_of_admits_positive_ricci"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_spherical_cover_of_admits_positive_ricci ``Submission.DifferentialGeometry.Geometry.exists_spherical_cover_of_admits_positive_ricci

end DifferentialGeometry.Geometry
