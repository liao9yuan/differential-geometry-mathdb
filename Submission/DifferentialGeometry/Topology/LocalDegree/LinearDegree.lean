import Submission.DifferentialGeometry.Topology.LocalDegree.LinearDegreePath
import Submission.DifferentialGeometry.Topology.LocalDegree.OrthogonalDegree

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Metric
noncomputable section
namespace DifferentialGeometry.LocalDegree

variable {n : ℕ}

private theorem reduction_sphere_nonzero
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (t : unitInterval) (v : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    orthogonalReductionPath A t v ≠ 0 := by
  apply orthogonalReductionPath_nonzero
  intro hv
  have hn := norm_eq_of_mem_sphere v
  rw [hv, norm_zero] at hn
  exact zero_ne_one hn

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.reduction_sphere_nonzero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.reduction_sphere_nonzero target :: scope.openDecls } }

def linearSphereOrthogonalHomotopy
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (linearSphereMap A).Homotopy
      (linearSphereMap (orthogonalReduction A).toContinuousLinearEquiv) where
  toFun p := (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin n))
    ⟨orthogonalReductionPath A p.1 p.2, reduction_sphere_nonzero A p.1 p.2⟩).1
  continuous_toFun := by
    have hc : Continuous (fun p : unitInterval × _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        orthogonalReductionPath A p.1 p.2) :=
      ((orthogonalReductionPath A).continuous.comp continuous_fst).clm_apply
        (continuous_subtype_val.comp continuous_snd)
    exact (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin n))).continuous.fst.comp
      (hc.subtype_mk (fun p => reduction_sphere_nonzero A p.1 p.2))
  map_zero_left v := by
    apply Subtype.ext
    simp [homeomorphUnitSphereProd_apply_fst_coe]
  map_one_left v := by
    apply Subtype.ext
    simp [homeomorphUnitSphereProd_apply_fst_coe]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.linearSphereOrthogonalHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.linearSphereOrthogonalHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.linearSphereOrthogonalHomotopy ``Submission.DifferentialGeometry.LocalDegree.linearSphereOrthogonalHomotopy


theorem linearSphereOrthogonalHomotopy_apply
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (t : unitInterval) (v : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (linearSphereOrthogonalHomotopy A (t, v) : EuclideanSpace ℝ (Fin n)) =
      ‖orthogonalReductionPath A t v‖⁻¹ • orthogonalReductionPath A t v :=
  homeomorphUnitSphereProd_apply_fst_coe _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.linearSphereOrthogonalHomotopy_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.linearSphereOrthogonalHomotopy_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.linearSphereOrthogonalHomotopy_apply ``Submission.DifferentialGeometry.LocalDegree.linearSphereOrthogonalHomotopy_apply

theorem euclideanSphereDegree_linearEquiv {d : ℕ}
    (A : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    euclideanSphereDegree (linearSphereMap A) =
      (SignType.sign (LinearMap.det A.toLinearMap) : ℤ) := by
  rw [euclideanSphereDegree_eq_of_homotopy (linearSphereOrthogonalHomotopy A),
    euclideanSphereDegree_linearIsometryEquiv, orthogonalReduction_det_sign]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereDegree_linearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereDegree_linearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereDegree_linearEquiv ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereDegree_linearEquiv

end DifferentialGeometry.LocalDegree
