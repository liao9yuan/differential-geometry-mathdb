import Submission.DifferentialGeometry.Topology.LocalDegree.Euclidean
import Submission.DifferentialGeometry.Topology.LocalDegree.LinearSphere
import Submission.DifferentialGeometry.Topology.LocalDegree.LinearizationHomotopy
import Mathlib.Algebra.Group.Int.Units

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

theorem isolatedZero_of_hasFDerivAt_equiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} {s : Set E}
    (A : E ≃L[ℝ] F) (hs : s ∈ 𝓝 x) (hf : ContinuousOn f s)
    (hz : f x = 0) (hd : HasFDerivAt f A.toContinuousLinearMap x) : isolatedZero f x := by
  obtain ⟨R, hR, hc, hn, _⟩ := exists_sphereMap_linearization_homotopy A hs hf hz hd
  refine ⟨R, hR, hc, fun y hy => ⟨?_, ?_⟩⟩
  · intro hfy
    by_contra hne
    exact hn y hy hne hfy
  · intro hyx
    exact hyx ▸ hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.isolatedZero_of_hasFDerivAt_equiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.isolatedZero_of_hasFDerivAt_equiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.isolatedZero_of_hasFDerivAt_equiv ``Submission.DifferentialGeometry.LocalDegree.isolatedZero_of_hasFDerivAt_equiv

variable {d : ℕ}
  {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
  {x : EuclideanSpace ℝ (Fin (d + 1))} {s : Set (EuclideanSpace ℝ (Fin (d + 1)))}

theorem euclideanLocalDegree_eq_linear_of_hasFDerivAt
    (A : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (hs : s ∈ 𝓝 x) (hf : ContinuousOn f s) (hz : f x = 0)
    (hd : HasFDerivAt f A.toContinuousLinearMap x) (h : isolatedZero f x) :
    euclideanLocalDegree f x h = euclideanSphereDegree (linearSphereMap A) := by
  obtain ⟨R, hR, hc, hn, hH⟩ := exists_sphereMap_linearization_homotopy A hs hf hz hd
  have hi : IsolatingRadius f x R := ⟨hR, hc, fun y hy => ⟨fun hfy => by
    by_contra hne
    exact hn y hy hne hfy, fun hyx => hyx ▸ hz⟩⟩
  rw [euclideanLocalDegree_eq_sphereDegree h hi ⟨R, hR, le_rfl⟩]
  obtain ⟨H, _⟩ := hH ⟨R, hR, le_rfl⟩
  exact (euclideanSphereDegree_eq_of_homotopy H).trans
    (congrArg euclideanSphereDegree (sphereMap_linear_eq A R ⟨R, hR, le_rfl⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_linear_of_hasFDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_linear_of_hasFDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_linear_of_hasFDerivAt ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_linear_of_hasFDerivAt


theorem euclideanLocalDegree_isUnit_of_hasFDerivAt
    (A : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (hs : s ∈ 𝓝 x) (hf : ContinuousOn f s) (hz : f x = 0)
    (hd : HasFDerivAt f A.toContinuousLinearMap x) (h : isolatedZero f x) :
    IsUnit (euclideanLocalDegree f x h) := by
  rw [euclideanLocalDegree_eq_linear_of_hasFDerivAt A hs hf hz hd h]
  exact euclideanSphereDegree_isUnit (linearSphereHomeomorph A).toHomotopyEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_isUnit_of_hasFDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_isUnit_of_hasFDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_isUnit_of_hasFDerivAt ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_isUnit_of_hasFDerivAt


theorem euclideanLocalDegree_eq_one_or_neg_one_of_hasFDerivAt
    (A : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (hs : s ∈ 𝓝 x) (hf : ContinuousOn f s) (hz : f x = 0)
    (hd : HasFDerivAt f A.toContinuousLinearMap x) (h : isolatedZero f x) :
    euclideanLocalDegree f x h = 1 ∨ euclideanLocalDegree f x h = -1 :=
  Int.isUnit_iff.mp (euclideanLocalDegree_isUnit_of_hasFDerivAt A hs hf hz hd h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_one_or_neg_one_of_hasFDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_one_or_neg_one_of_hasFDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_one_or_neg_one_of_hasFDerivAt ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_one_or_neg_one_of_hasFDerivAt

end DifferentialGeometry.LocalDegree
