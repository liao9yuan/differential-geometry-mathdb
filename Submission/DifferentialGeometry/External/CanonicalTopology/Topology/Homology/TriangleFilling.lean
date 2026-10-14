import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homotopy.TriangleFaces
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homotopy.TrianglePathBoundary
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homotopy.ConvexPlaneExtension
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.PathEvaluation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Actual singular triangle fillings from simple connectivity -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set
open scoped _root_.Simplicial _root_.Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X] {a b c : X}

/-- Three prescribed paths with compatible endpoints are the exact ordered
faces of one actual singular triangle. No reparametrization or homotopic
replacement of any of the three paths occurs. -/
theorem exists_integralPathTriangle (p : Path a b) (q : Path b c) (r : Path a c) :
    ∃ σ : integralSingularSimplex 2 X,
      ∀ i : Fin 3, (TopCat.toSSet.obj (TopCat.of X)).δ i σ =
        ![integralPathSimplex q, integralPathSimplex r, integralPathSimplex p] i := by
  obtain ⟨F, hF⟩ := exists_convex_plane_boundary_extension convex_planeTriangle
    isClosed_planeTriangle isBounded_planeTriangle planeTriangle_interior_nonempty
      (triangleBoundaryMap p q r)
  let σ : integralSingularSimplex 2 X := (integralSingularSimplexEquiv 2 X).symm
    (F.comp ⟨simplexTriangleHomeomorph, simplexTriangleHomeomorph.continuous⟩)
  have hf (i : Fin 3) (t : stdSimplex ℝ (Fin 2)) :
      integralSingularSimplexEquiv 1 X ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) t =
        triangleBoundaryPaths p q r (i, stdSimplexHomeomorphUnitInterval t) := by
    change (TopCat.of X).toSSetObjEquiv _ ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) t = _
    rw [TopCat.toSSetObjEquiv_δ_apply]
    change integralSingularSimplexEquiv 2 X ((integralSingularSimplexEquiv 2 X).symm
      (F.comp ⟨simplexTriangleHomeomorph, simplexTriangleHomeomorph.continuous⟩))
        (stdSimplex.map i.succAbove t) = _
    rw [Equiv.apply_symm_apply]
    change F (simplexTriangleHomeomorph (stdSimplex.map i.succAbove t)) = _
    let z := planeTriangleEdge i (stdSimplexHomeomorphUnitInterval t)
    have he : simplexTriangleHomeomorph (stdSimplex.map i.succAbove t) =
        (⟨z.val, isClosed_planeTriangle.frontier_subset z.property⟩ : planeTriangle) :=
      Subtype.ext (simplexTriangleHomeomorph_face i t)
    rw [he]
    exact (hF z).trans (triangleBoundaryMap_edge p q r i (stdSimplexHomeomorphUnitInterval t))
  refine ⟨σ, fun i => (integralSingularSimplexEquiv 1 X).injective ?_⟩
  apply ContinuousMap.ext
  intro t
  rw [hf]
  fin_cases i <;> exact (integralPathSimplex_apply _ t).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_integralPathTriangle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_integralPathTriangle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_integralPathTriangle ``Submission.DifferentialGeometry.Topology.exists_integralPathTriangle

/-- The same triangle gives the original signed singular boundary q - r + p. -/
theorem exists_integralPathTriangle_boundary (p : Path a b) (q : Path b c) (r : Path a c) :
    ∃ σ : integralSingularSimplex 2 X,
      (integralSingularChains X).d 2 1 (integralSimplexChain 2 σ) =
        integralPathChain q - integralPathChain r + integralPathChain p := by
  obtain ⟨σ, hσ⟩ := exists_integralPathTriangle p q r
  refine ⟨σ, ?_⟩
  rw [integralSimplexChain_boundary_two, hσ 0, hσ 1, hσ 2]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_integralPathTriangle_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_integralPathTriangle_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_integralPathTriangle_boundary ``Submission.DifferentialGeometry.Topology.exists_integralPathTriangle_boundary

end DifferentialGeometry.Topology
