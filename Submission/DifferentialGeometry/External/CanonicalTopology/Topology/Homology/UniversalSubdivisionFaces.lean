import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SingularSubdivision
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexPushFaces

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Exact ordered faces of the universal subdivided simplex chains -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

/-- The subdivided original affine face is the actual image of the same
universal subdivided lower-dimensional simplex. -/
theorem universalSimplexSubdivision_face (n : ℕ) (i : Fin (n + 2)) :
    affineSingularSubdivision n
      (affineSingularChain n (liftedSimplexVertex.{u} (n + 1) ∘ i.succAbove)) =
      (singularCarrierMap n ⟨liftedSimplexLinearMap n (n + 1) i.succAbove,
        (liftedSimplexLinearMap n (n + 1) i.succAbove).continuous⟩
          (liftedSimplexLinearMap_body n (n + 1) i.succAbove) (universalSimplexSubdivision n)).val := by
  change _ = (integralSingularChainMap
    ⟨liftedSimplexLinearMap n (n + 1) i.succAbove, (liftedSimplexLinearMap n (n + 1) i.succAbove).continuous⟩).f n
      (affineSingularSubdivision n (affineSingularChain n (liftedSimplexVertex.{u} n)))
  rw [affineSingularSubdivision_linear n _ (convex_liftedSimplexBody n) (liftedSimplexChain_mem n),
    affineSingularChain_linear]
  have hv : liftedSimplexLinearMap.{u} n (n + 1) i.succAbove ∘ liftedSimplexVertex n =
      liftedSimplexVertex (n + 1) ∘ i.succAbove :=
    funext (liftedSimplexLinearMap_vertex n (n + 1) i.succAbove)
  rw [hv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.universalSimplexSubdivision_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.universalSimplexSubdivision_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.universalSimplexSubdivision_face ``Submission.DifferentialGeometry.Topology.universalSimplexSubdivision_face

/-- The SAME universal homotopy has the corresponding exact face naturality. -/
theorem universalSimplexHomotopy_face (n : ℕ) (i : Fin (n + 2)) :
    affineSubdivisionHomotopy n
      (affineSingularChain n (liftedSimplexVertex.{u} (n + 1) ∘ i.succAbove)) =
      (singularCarrierMap (n + 1) ⟨liftedSimplexLinearMap n (n + 1) i.succAbove,
        (liftedSimplexLinearMap n (n + 1) i.succAbove).continuous⟩
          (liftedSimplexLinearMap_body n (n + 1) i.succAbove) (universalSimplexHomotopy n)).val := by
  change _ = (integralSingularChainMap
    ⟨liftedSimplexLinearMap n (n + 1) i.succAbove, (liftedSimplexLinearMap n (n + 1) i.succAbove).continuous⟩).f (n + 1)
      (affineSubdivisionHomotopy n (affineSingularChain n (liftedSimplexVertex.{u} n)))
  rw [affineSubdivisionHomotopy_linear n _ (convex_liftedSimplexBody n) (liftedSimplexChain_mem n),
    affineSingularChain_linear]
  have hv : liftedSimplexLinearMap.{u} n (n + 1) i.succAbove ∘ liftedSimplexVertex n =
      liftedSimplexVertex (n + 1) ∘ i.succAbove :=
    funext (liftedSimplexLinearMap_vertex n (n + 1) i.succAbove)
  rw [hv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.universalSimplexHomotopy_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.universalSimplexHomotopy_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.universalSimplexHomotopy_face ``Submission.DifferentialGeometry.Topology.universalSimplexHomotopy_face

/-- The actual boundary of the original universal subdivision is exactly
the signed sum of those original subdivided faces, in the same carrier. -/
theorem universalSimplexSubdivision_boundary (n : ℕ) :
    (⟨(integralSingularChains (liftedSimplexSpace.{u} (n + 1))).d (n + 1) n
        (universalSimplexSubdivision (n + 1)).val,
      integralSingularChainsIn_boundary n _ (universalSimplexSubdivision (n + 1)).property⟩ :
        integralSingularChainsIn n (liftedSimplexBody (n + 1))) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        singularCarrierMap n ⟨liftedSimplexLinearMap n (n + 1) i.succAbove,
          (liftedSimplexLinearMap n (n + 1) i.succAbove).continuous⟩
            (liftedSimplexLinearMap_body n (n + 1) i.succAbove) (universalSimplexSubdivision n) := by
  apply Subtype.ext
  change (integralSingularChains (liftedSimplexSpace.{u} (n + 1))).d (n + 1) n
    (affineSingularSubdivision (n + 1) (affineSingularChain (n + 1) (liftedSimplexVertex (n + 1)))) =
      (integralSingularChainsIn n (liftedSimplexBody (n + 1))).subtype (∑ i : Fin (n + 2),
        (-1 : ℤ) ^ i.val • singularCarrierMap n
          ⟨liftedSimplexLinearMap n (n + 1) i.succAbove, (liftedSimplexLinearMap n (n + 1) i.succAbove).continuous⟩
            (liftedSimplexLinearMap_body n (n + 1) i.succAbove) (universalSimplexSubdivision n))
  rw [map_sum, affineSingularSubdivision_boundary n (convex_liftedSimplexBody (n + 1))
    (liftedSimplexChain_mem (n + 1)), affineSingularChain_boundary, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, map_zsmul, universalSimplexSubdivision_face]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.universalSimplexSubdivision_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.universalSimplexSubdivision_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.universalSimplexSubdivision_boundary ``Submission.DifferentialGeometry.Topology.universalSimplexSubdivision_boundary

end DifferentialGeometry.Topology
