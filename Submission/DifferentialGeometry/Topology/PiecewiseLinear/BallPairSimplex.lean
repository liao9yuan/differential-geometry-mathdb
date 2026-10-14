import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallPairModel
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplexPush

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isPLBallPair_convexHull_of_mem_openSimplex {n : ℕ} {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = n + 2) {p : E}
    (hp : p ∈ openSimplex T) {J : Geometry.SimplicialComplex ℝ E}
    (hJ : J.faces ⊆ (simplexBoundary T hT).faces) {a b : E} (hab : a ≠ b)
    (hJs : J.space = {a, b}) :
    IsPLBallPair n 1 (convexHull ℝ (T : Set E)) (segment ℝ p a ∪ segment ℝ p b) := by
  classical
  have h2 : 2 ≤ T.card := by omega
  have hfin : Finite (simplexBoundary T hT).faces := (simplexBoundary_faces_finite T hT).to_subtype
  have hL : IsConeBase p (simplexBoundary T hT) := isConeBase_simplexBoundary hT h2 hp
  have hsph : IsPLSphere n (simplexBoundary T hT).space := by
    rw [simplexBoundary_space T hT h2]
    exact isPLSphere_biUnion_erase T hT hcard
  have hpair := isPLBallPair_coneSet_arc hL hJ hsph hab hJs
  rwa [← coneComplex_space_eq_coneSet hL, coneComplex_simplexBoundary_space hT h2 hp] at hpair

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBallPair_convexHull_of_mem_openSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBallPair_convexHull_of_mem_openSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBallPair_convexHull_of_mem_openSimplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBallPair_convexHull_of_mem_openSimplex

end DifferentialGeometry.Topology.PiecewiseLinear
