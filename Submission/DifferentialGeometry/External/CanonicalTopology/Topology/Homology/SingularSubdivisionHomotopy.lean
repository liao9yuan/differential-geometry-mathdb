import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SingularSubdivisionBoundary
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.UniversalHomotopyBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The same subdivision homotopy on the original full singular chains -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- The exact homotopy boundary formula on every original singular simplex. -/
theorem integralSingularSubdivisionHomotopy_boundary_simplex (n : ℕ)
    (σ : integralSingularSimplex (n + 1) X) :
    (integralSingularChains X).d (n + 2) (n + 1)
      (integralSingularSubdivisionHomotopy (n + 1) (integralSimplexChain (n + 1) σ)) =
        integralSimplexChain (n + 1) σ - integralSingularSubdivision (n + 1) (integralSimplexChain (n + 1) σ) -
          integralSingularSubdivisionHomotopy n ((integralSingularChains X).d (n + 1) n
            (integralSimplexChain (n + 1) σ)) := by
  rw [integralSingularSubdivisionHomotopy_simplex, ← singularSimplexChainPush_boundary,
    universalSimplexHomotopy_boundary]
  simp only [map_sub, map_sum, map_zsmul]
  rw [singularSimplexChainPush_identity, integralSingularSubdivision_simplex,
    integralSimplexChain_boundary, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [singularSimplexChainPush_face, map_zsmul, integralSingularSubdivisionHomotopy_simplex]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_boundary_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_boundary_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_boundary_simplex ``Submission.DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_boundary_simplex

/-- The same original operators satisfy the actual identity-minus-subdivision
homotopy equation on EVERY original singular chain in positive degrees. -/
theorem integralSingularSubdivisionHomotopy_boundary (n : ℕ) :
    ((integralSingularChains X).d (n + 2) (n + 1)).hom.comp (integralSingularSubdivisionHomotopy (n + 1)) =
      LinearMap.id - integralSingularSubdivision (n + 1) -
        (integralSingularSubdivisionHomotopy n).comp ((integralSingularChains X).d (n + 1) n).hom := by
  apply (integralSingularChainBasis (n + 1) X).ext
  intro σ
  rw [integralSingularChainBasis_apply]
  exact integralSingularSubdivisionHomotopy_boundary_simplex n σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_boundary ``Submission.DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_boundary

/-- Each original cycle and its subdivision differ by the boundary of the
SAME constructed homotopy chain. -/
theorem integralSingularSubdivisionHomotopy_cycle (n : ℕ)
    (c : (integralSingularChains X).X (n + 1)) (hc : (integralSingularChains X).d (n + 1) n c = 0) :
    (integralSingularChains X).d (n + 2) (n + 1) (integralSingularSubdivisionHomotopy (n + 1) c) =
      c - integralSingularSubdivision (n + 1) c := by
  have h := LinearMap.congr_fun (integralSingularSubdivisionHomotopy_boundary n) c
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, hc, map_zero, sub_zero] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_cycle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_cycle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_cycle ``Submission.DifferentialGeometry.Topology.integralSingularSubdivisionHomotopy_cycle

end DifferentialGeometry.Topology
