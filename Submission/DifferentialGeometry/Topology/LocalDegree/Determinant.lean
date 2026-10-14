import Submission.DifferentialGeometry.Topology.LocalDegree.EuclideanLinearization
import Submission.DifferentialGeometry.Topology.LocalDegree.LinearDegree

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Metric _root_.Set
open scoped _root_.Topology
noncomputable section
namespace DifferentialGeometry.LocalDegree

variable {d : ℕ}
  {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
  {x : EuclideanSpace ℝ (Fin (d + 1))}

theorem isolatedZero_of_det_fderiv_ne_zero
    {s : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hs : s ∈ 𝓝 x) (hc : ContinuousOn f s) (hz : f x = 0)
    (hd : DifferentiableAt ℝ f x) (hdet : LinearMap.det (fderiv ℝ f x).toLinearMap ≠ 0) :
    isolatedZero f x := by
  let A := (fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero hdet
  exact isolatedZero_of_hasFDerivAt_equiv A hs hc hz hd.hasFDerivAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.isolatedZero_of_det_fderiv_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.isolatedZero_of_det_fderiv_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.isolatedZero_of_det_fderiv_ne_zero ``Submission.DifferentialGeometry.LocalDegree.isolatedZero_of_det_fderiv_ne_zero

theorem euclideanLocalDegree_eq_sign_det_fderiv
    (h : isolatedZero f x) (hd : DifferentiableAt ℝ f x)
    (hdet : LinearMap.det (fderiv ℝ f x).toLinearMap ≠ 0) :
    euclideanLocalDegree f x h = (SignType.sign (LinearMap.det (fderiv ℝ f x).toLinearMap) : ℤ) := by
  let A := (fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero hdet
  have hR := h.choose_spec
  rw [euclideanLocalDegree_eq_linear_of_hasFDerivAt A
    (_root_.Metric.closedBall_mem_nhds _ hR.pos) hR.continuousOn hR.zero hd.hasFDerivAt h,
    euclideanSphereDegree_linearEquiv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_sign_det_fderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_sign_det_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_sign_det_fderiv ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_sign_det_fderiv

end DifferentialGeometry.LocalDegree
