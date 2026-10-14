import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereHomologyShift
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ReducedZero
import Mathlib.Analysis.Normed.Module.Connected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The degree-one sphere computation uses actual reduced H0 -/

noncomputable section

open _root_.ContinuousMap _root_.Set _root_.Metric

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Original H1 of the sphere is original reduced H0 of the lower sphere,
using the same pole charts and the normalized original augmentation. -/
def integralSphereHomologyOneReducedEquiv [PathConnectedSpace (_root_.Metric.sphere (0 : E) 1)]
    (v : _root_.Metric.sphere (0 : E) 1) :
    integralSingularHomology 1 (_root_.Metric.sphere (0 : E) 1) ≃ₗ[ℤ]
      integralReducedHomologyZero (_root_.Metric.sphere (0 : (ℝ ∙ ((-v : _root_.Metric.sphere (0 : E) 1) : E))ᗮ) 1) := by
  letI := spherePuncture_contractible (-v)
  exact ((integralSphereHomologyOneKernelEquiv v).trans
    (integralZeroMapKernelReducedEquiv (singularSubspaceInclusion
      (subspaceIntersection ({v}ᶜ : Set (_root_.Metric.sphere (0 : E) 1)) {-v}ᶜ)))).trans
        (integralReducedZeroHomotopyEquiv (spherePoleIntersectionHomotopyEquiv v))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSphereHomologyOneReducedEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSphereHomologyOneReducedEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSphereHomologyOneReducedEquiv ``Submission.DifferentialGeometry.Topology.integralSphereHomologyOneReducedEquiv

/-- The required path-connectedness is proved from actual vector-space
rank, rather than included as a sphere-homology hypothesis. -/
theorem unitSphere_pathConnected_of_rank (h : 1 < Module.rank ℝ E) :
    PathConnectedSpace (_root_.Metric.sphere (0 : E) 1) :=
  isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere h 0 (by norm_num))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.unitSphere_pathConnected_of_rank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.unitSphere_pathConnected_of_rank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.unitSphere_pathConnected_of_rank ``Submission.DifferentialGeometry.Topology.unitSphere_pathConnected_of_rank

end DifferentialGeometry.Topology
