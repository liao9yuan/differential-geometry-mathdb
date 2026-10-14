import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereRank

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Original top-dimensional integral sphere homology -/

noncomputable section

open _root_.Metric _root_.Module

universe u

namespace DifferentialGeometry.Topology

/-- The original integral homology in the dimension of a positive-dimensional
sphere is Z. This is proved by the actual excision dimension shift, terminating
at the computed normalized two-point augmentation kernel. No sphere homology
value or fundamental class is an input. -/
def integralSphereTopHomologyEquiv (n : ℕ) (E : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hd : _root_.Module.finrank ℝ E = n + 2) :
    integralSingularHomology (n + 1) (_root_.Metric.sphere (0 : E) 1) ≃ₗ[ℤ] ℤ := by
  induction n generalizing E with
  | zero =>
      let v := unitSpherePointOfFinrankPos (E := E) (by omega)
      letI := unitSphere_pathConnected_of_finrank (E := E) (by omega)
      exact (integralSphereHomologyOneReducedEquiv v).trans
        (integralZeroSphereReducedEquiv (unitSpherePoleHyperplane_finrank 1 hd (-v)))
  | succ n ih =>
      let v := unitSpherePointOfFinrankPos (E := E) (by omega)
      exact (integralSphereHomologyShiftEquiv n v).trans
        (ih (ℝ ∙ ((-v : _root_.Metric.sphere (0 : E) 1) : E))ᗮ
          (unitSpherePoleHyperplane_finrank (n + 2) (by omega) (-v)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSphereTopHomologyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSphereTopHomologyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSphereTopHomologyEquiv ``Submission.DifferentialGeometry.Topology.integralSphereTopHomologyEquiv

end DifferentialGeometry.Topology
