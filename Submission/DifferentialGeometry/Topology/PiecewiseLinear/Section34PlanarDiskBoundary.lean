import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.image_stdSimplexBoundary_eq_frontier_real_prod
    {P : Set (ℝ × ℝ)} {r : (Fin 3 → ℝ) → ℝ × ℝ}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) P) :
    r '' stdSimplexBoundary 2 = frontier P := by
  let e : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm
  have hP : IsPolyhedron P := (show IsPLBall 2 P from ⟨r, hr⟩).isPolyhedron
  have he : IsPLHomeomorphOn e P (e '' P) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP
      ((isPiecewiseAffineOn_of_affine e.toLinearMap.toAffineMap isOpen_univ).mono_of_isPolyhedron
        hP (_root_.Set.subset_univ _)) e.injective.injOn.bijOn_image
  have h := (hr.trans he).image_stdSimplexBoundary_eq_frontier
  rw [_root_.Set.image_comp] at h
  have hefront : e '' frontier P = frontier (e '' P) := e.toHomeomorph.image_frontier P
  rw [← hefront] at h
  exact (Set.image_injective.mpr e.injective) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_stdSimplexBoundary_eq_frontier_real_prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_stdSimplexBoundary_eq_frontier_real_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_stdSimplexBoundary_eq_frontier_real_prod ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_stdSimplexBoundary_eq_frontier_real_prod

end DifferentialGeometry.Topology.PiecewiseLinear
