import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homotopy.TriangleEdges

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Exact ordered barycentric faces of the original planar triangle -/

noncomputable section

open _root_.Set _root_.Function
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

/-- The ordered face maps have the same interval parameter as the original
three planar edges, including all their endpoints. -/
theorem simplexTriangleHomeomorph_face (i : Fin 3) (t : stdSimplex ℝ (Fin 2)) :
    (simplexTriangleHomeomorph (stdSimplex.map i.succAbove t)).val =
      planeTriangleEdgeValue i (stdSimplexHomeomorphUnitInterval t) := by
  have ht : t.val 0 + t.val 1 = 1 := by
    simpa [Fin.sum_univ_two] using t.property.2
  change (⟨(FunOnFinite.linearMap ℝ ℝ i.succAbove t.val) 1,
    (FunOnFinite.linearMap ℝ ℝ i.succAbove t.val) 2⟩ : ℂ) =
      planeTriangleEdgeValue i ⟨t.val 1, _⟩
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_filter, Fin.sum_univ_two]
  fin_cases i <;> apply Complex.ext <;>
    simp [planeTriangleEdgeValue, Fin.succAbove]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplexTriangleHomeomorph_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplexTriangleHomeomorph_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplexTriangleHomeomorph_face ``Submission.DifferentialGeometry.Topology.simplexTriangleHomeomorph_face

end DifferentialGeometry.Topology
