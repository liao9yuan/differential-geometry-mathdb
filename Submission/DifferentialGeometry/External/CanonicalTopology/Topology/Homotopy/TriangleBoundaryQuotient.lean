import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homotopy.TriangleEdges
import Mathlib.Topology.ContinuousMap.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The actual triangle frontier as a quotient of its three ordered edges -/

noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

/-- Glue the same three original closed intervals along their actual vertices. -/
def triangleBoundaryProjection : C(Fin 3 × unitInterval, frontier planeTriangle) :=
  (⟨planeTriangleEdge, continuous_of_discreteTopology⟩ : C(Fin 3, C(unitInterval, frontier planeTriangle))).uncurry

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.triangleBoundaryProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.triangleBoundaryProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.triangleBoundaryProjection ``Submission.DifferentialGeometry.Topology.triangleBoundaryProjection

/-- The quotient formula is exactly the chosen ordered edge parametrization. -/
theorem triangleBoundaryProjection_apply (i : Fin 3) (s : unitInterval) :
    (triangleBoundaryProjection (i, s)).val = planeTriangleEdgeValue i s := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.triangleBoundaryProjection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.triangleBoundaryProjection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.triangleBoundaryProjection_apply ``Submission.DifferentialGeometry.Topology.triangleBoundaryProjection_apply

/-- Every original frontier point lies on one of the original parametrized edges. -/
theorem triangleBoundaryProjection_surjective : _root_.Function.Surjective triangleBoundaryProjection := by
  intro z
  have hz := isClosed_planeTriangle.frontier_subset z.property
  have him : z.val.im ≤ 1 := by linarith [hz.1, hz.2.2]
  have hre : z.val.re ≤ 1 := by linarith [hz.2.1, hz.2.2]
  rcases planeTriangle_frontier_edges z.property with hr | hi | hs
  · refine ⟨(1, ⟨z.val.im, hz.2.1, him⟩), ?_⟩
    apply Subtype.ext
    change planeTriangleEdgeValue 1 _ = z.val
    apply Complex.ext
    · simpa [planeTriangleEdgeValue] using hr.symm
    · simp [planeTriangleEdgeValue]
  · refine ⟨(2, ⟨z.val.re, hz.1, hre⟩), ?_⟩
    apply Subtype.ext
    change planeTriangleEdgeValue 2 _ = z.val
    apply Complex.ext
    · simp [planeTriangleEdgeValue]
    · simpa [planeTriangleEdgeValue] using hi.symm
  · refine ⟨(0, ⟨z.val.im, hz.2.1, him⟩), ?_⟩
    apply Subtype.ext
    change planeTriangleEdgeValue 0 _ = z.val
    apply Complex.ext
    · simpa [planeTriangleEdgeValue] using (show 1 - z.val.im = z.val.re by linarith)
    · simp [planeTriangleEdgeValue]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.triangleBoundaryProjection_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.triangleBoundaryProjection_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.triangleBoundaryProjection_surjective ``Submission.DifferentialGeometry.Topology.triangleBoundaryProjection_surjective

/-- This actual compact-domain continuous surjection is a quotient map. -/
theorem triangleBoundaryProjection_isQuotientMap :
    _root_.Topology.IsQuotientMap triangleBoundaryProjection :=
  .of_surjective_continuous triangleBoundaryProjection_surjective triangleBoundaryProjection.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.triangleBoundaryProjection_isQuotientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.triangleBoundaryProjection_isQuotientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.triangleBoundaryProjection_isQuotientMap ``Submission.DifferentialGeometry.Topology.triangleBoundaryProjection_isQuotientMap

end DifferentialGeometry.Topology
