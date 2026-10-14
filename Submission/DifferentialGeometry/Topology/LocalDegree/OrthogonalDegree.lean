import Submission.DifferentialGeometry.Topology.LocalDegree.ReflectionDegree
import Mathlib.Data.Sign.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Metric _root_.Submodule
noncomputable section
namespace DifferentialGeometry.LocalDegree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem linearSphereMap_linearIsometryEquiv_mul (A B : E ≃ₗᵢ[ℝ] E) :
    linearSphereMap (A * B).toContinuousLinearEquiv =
      (linearSphereMap A.toContinuousLinearEquiv).comp
        (linearSphereMap B.toContinuousLinearEquiv) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  simp only [ContinuousMap.comp_apply, linearSphereMap_linearIsometryEquiv_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.linearSphereMap_linearIsometryEquiv_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.linearSphereMap_linearIsometryEquiv_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.linearSphereMap_linearIsometryEquiv_mul ``Submission.DifferentialGeometry.LocalDegree.linearSphereMap_linearIsometryEquiv_mul


theorem linearSphereMap_linearIsometryEquiv_one :
    linearSphereMap (1 : E ≃ₗᵢ[ℝ] E).toContinuousLinearEquiv =
      ContinuousMap.id (_root_.Metric.sphere (0 : E) 1) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rw [linearSphereMap_linearIsometryEquiv_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.linearSphereMap_linearIsometryEquiv_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.linearSphereMap_linearIsometryEquiv_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.linearSphereMap_linearIsometryEquiv_one ``Submission.DifferentialGeometry.LocalDegree.linearSphereMap_linearIsometryEquiv_one

variable {d : ℕ}

private theorem reflection_degree_eq_det_sign
    (v : EuclideanSpace ℝ (Fin (d + 1))) :
    euclideanSphereDegree (unitSphereReflection v) =
      (SignType.sign (LinearMap.det (ℝ ∙ v)ᗮ.reflection.toLinearMap) : ℤ) := by
  rw [Submodule.det_reflection, _root_.Submodule.orthogonal_orthogonal]
  by_cases hv : v = 0
  · subst v
    rw [show ℝ ∙ (0 : EuclideanSpace ℝ (Fin (d + 1))) = ⊥ from
      span_singleton_eq_bot.mpr rfl]
    simp
  · rw [finrank_span_singleton hv, pow_one, euclideanSphereDegree_reflection v hv]
    norm_num

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.reflection_degree_eq_det_sign
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.reflection_degree_eq_det_sign target :: scope.openDecls } }

private theorem orthogonal_det_mul
    (A B : EuclideanSpace ℝ (Fin (d + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    LinearMap.det (A * B).toLinearMap =
      LinearMap.det A.toLinearMap * LinearMap.det B.toLinearMap := by
  change LinearMap.det (A.toLinearMap * B.toLinearMap) = _
  exact map_mul LinearMap.det _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.orthogonal_det_mul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.orthogonal_det_mul target :: scope.openDecls } }

theorem euclideanSphereDegree_linearIsometryEquiv
    (A : EuclideanSpace ℝ (Fin (d + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    euclideanSphereDegree (linearSphereMap A.toContinuousLinearEquiv) =
      (SignType.sign (LinearMap.det A.toLinearMap) : ℤ) := by
  obtain ⟨l, hlength, rfl⟩ := A.reflections_generate_dim
  clear hlength
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, linearSphereMap_linearIsometryEquiv_one,
      euclideanSphereDegree_id]
    change (1 : ℤ) = (SignType.sign (LinearMap.det (1 : _ →ₗ[ℝ] _)) : ℤ)
    simp
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, linearSphereMap_linearIsometryEquiv_mul,
      euclideanSphereDegree_comp, orthogonal_det_mul, sign_mul, SignType.coe_mul]
    change euclideanSphereDegree (unitSphereReflection v) * _ = _
    rw [reflection_degree_eq_det_sign, ih]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereDegree_linearIsometryEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereDegree_linearIsometryEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereDegree_linearIsometryEquiv ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereDegree_linearIsometryEquiv

end DifferentialGeometry.LocalDegree
