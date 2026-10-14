import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SpherePuncture
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ContractibleCoverOne

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Dimension shift for the original singular homology of a sphere -/

noncomputable section

open _root_.CategoryTheory _root_.ContinuousMap _root_.Set _root_.Metric

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual intersection of the two pole complements is homotopy
 equivalent to the unit sphere in the pole's orthogonal hyperplane. -/
def spherePoleIntersectionHomotopyEquiv (v : _root_.Metric.sphere (0 : E) 1) :
    subspaceIntersection ({v}ᶜ : Set (_root_.Metric.sphere (0 : E) 1)) {-v}ᶜ ≃ₕ
      sphere (0 : (ℝ ∙ ((-v : _root_.Metric.sphere (0 : E) 1) : E))ᗮ) 1 :=
  (sphereDoublePunctureHomeomorph v).toHomotopyEquiv.trans
    (puncturedSpaceSphereHomotopyEquiv _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.spherePoleIntersectionHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.spherePoleIntersectionHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.spherePoleIntersectionHomotopyEquiv ``Submission.DifferentialGeometry.Topology.spherePoleIntersectionHomotopyEquiv

/-- Original sphere homology shifts down one degree to the same original
lower-dimensional sphere. The map uses the actual relative connecting
homomorphism, excision, stereographic projection and radial normalization. -/
def integralSphereHomologyShiftEquiv (n : ℕ) (v : _root_.Metric.sphere (0 : E) 1) :
    integralSingularHomology (n + 2) (_root_.Metric.sphere (0 : E) 1) ≃ₗ[ℤ]
      integralSingularHomology (n + 1) (_root_.Metric.sphere (0 : (ℝ ∙ ((-v : _root_.Metric.sphere (0 : E) 1) : E))ᗮ) 1) := by
  letI := spherePuncture_contractible v
  letI := spherePuncture_contractible (-v)
  exact (integralHomologyContractibleCoverEquiv n {v}ᶜ {-v}ᶜ
    isOpen_compl_singleton isOpen_compl_singleton (spherePunctures_cover v)).trans
      (integralSingularHomologyHomotopyEquiv (n + 1) (spherePoleIntersectionHomotopyEquiv v))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSphereHomologyShiftEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSphereHomologyShiftEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSphereHomologyShiftEquiv ``Submission.DifferentialGeometry.Topology.integralSphereHomologyShiftEquiv

/-- Degree one is the actual kernel of the inclusion on H0 of the same
intersection, with no generator or homology computation assumed. -/
def integralSphereHomologyOneKernelEquiv [PathConnectedSpace (_root_.Metric.sphere (0 : E) 1)]
    (v : _root_.Metric.sphere (0 : E) 1) :
    integralSingularHomology 1 (_root_.Metric.sphere (0 : E) 1) ≃ₗ[ℤ]
      LinearMap.ker (integralSingularHomologyMap 0
        (singularSubspaceInclusion (subspaceIntersection ({v}ᶜ : Set (_root_.Metric.sphere (0 : E) 1)) {-v}ᶜ))) := by
  letI := spherePuncture_contractible v
  letI := spherePuncture_contractible (-v)
  exact integralHomologyOneContractibleCoverEquiv {v}ᶜ {-v}ᶜ
    isOpen_compl_singleton isOpen_compl_singleton (spherePunctures_cover v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSphereHomologyOneKernelEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSphereHomologyOneKernelEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSphereHomologyOneKernelEquiv ``Submission.DifferentialGeometry.Topology.integralSphereHomologyOneKernelEquiv

end DifferentialGeometry.Topology
