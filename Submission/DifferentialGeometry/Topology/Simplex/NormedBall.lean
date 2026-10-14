import Submission.DifferentialGeometry.Topology.Simplex.BallCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Metric _root_.Topology
namespace DifferentialGeometry.Simplex
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (e : (Fin n → ℝ) ≃L[ℝ] E)

private theorem coordinateBody_interior_nonempty : (interior (e '' coordinateSimplex n)).Nonempty := by
  change (interior (e.toHomeomorph '' coordinateSimplex n)).Nonempty
  rw [← e.toHomeomorph.image_interior]
  exact (interior_coordinateSimplex_nonempty n).image e

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.coordinateBody_interior_nonempty
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.coordinateBody_interior_nonempty target :: scope.openDecls } }


def normedSimplexBallAmbientHomeomorph : E ≃ₜ E :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    ((convex_coordinateSimplex n).linear_image e.toLinearMap)
    (coordinateBody_interior_nonempty e)
    ((isCompact_coordinateSimplex n).image e.continuous).isBounded).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.normedSimplexBallAmbientHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.normedSimplexBallAmbientHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.normedSimplexBallAmbientHomeomorph ``Submission.DifferentialGeometry.Simplex.normedSimplexBallAmbientHomeomorph


theorem normedSimplexBallAmbientHomeomorph_image :
    normedSimplexBallAmbientHomeomorph e '' (e '' coordinateSimplex n) = _root_.Metric.closedBall (0 : E) 1 := by
  have hh := (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    ((convex_coordinateSimplex n).linear_image e.toLinearMap)
    (coordinateBody_interior_nonempty e)
    ((isCompact_coordinateSimplex n).image e.continuous).isBounded).choose_spec.2.1
  change normedSimplexBallAmbientHomeomorph e '' closure (e '' coordinateSimplex n) = _root_.Metric.closedBall (0 : E) 1 at hh
  rwa [((isCompact_coordinateSimplex n).image e.continuous).isClosed.closure_eq] at hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.normedSimplexBallAmbientHomeomorph_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.normedSimplexBallAmbientHomeomorph_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.normedSimplexBallAmbientHomeomorph_image ``Submission.DifferentialGeometry.Simplex.normedSimplexBallAmbientHomeomorph_image


theorem normedSimplexBallAmbientHomeomorph_image_frontier :
    normedSimplexBallAmbientHomeomorph e '' frontier (e '' coordinateSimplex n) = _root_.Metric.sphere (0 : E) 1 :=
  (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    ((convex_coordinateSimplex n).linear_image e.toLinearMap)
    (coordinateBody_interior_nonempty e)
    ((isCompact_coordinateSimplex n).image e.continuous).isBounded).choose_spec.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.normedSimplexBallAmbientHomeomorph_image_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.normedSimplexBallAmbientHomeomorph_image_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.normedSimplexBallAmbientHomeomorph_image_frontier ``Submission.DifferentialGeometry.Simplex.normedSimplexBallAmbientHomeomorph_image_frontier


def stdSimplexNormedBallHomeomorph : stdSimplex ℝ (Fin (n + 1)) ≃ₜ _root_.Metric.closedBall (0 : E) 1 :=
  (stdSimplexCoordinateHomeomorph n).trans
    ((e.toHomeomorph.trans (normedSimplexBallAmbientHomeomorph e)).sets (by
      ext x
      change x ∈ coordinateSimplex n ↔ normedSimplexBallAmbientHomeomorph e (e x) ∈ _root_.Metric.closedBall (0 : E) 1
      rw [← normedSimplexBallAmbientHomeomorph_image e, (normedSimplexBallAmbientHomeomorph e).injective.mem_set_image,
        e.injective.mem_set_image]))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph ``Submission.DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph


theorem stdSimplexNormedBallHomeomorph_mem_sphere_iff (x : stdSimplex ℝ (Fin (n + 1))) :
    (stdSimplexNormedBallHomeomorph e x).val ∈ _root_.Metric.sphere (0 : E) 1 ↔ x ∈ boundary (Fin (n + 1)) := by
  change normedSimplexBallAmbientHomeomorph e (e (stdSimplexCoordinateHomeomorph n x).val) ∈
    _root_.Metric.sphere (0 : E) 1 ↔ _
  rw [← normedSimplexBallAmbientHomeomorph_image_frontier e, (normedSimplexBallAmbientHomeomorph e).injective.mem_set_image]
  change e.toHomeomorph (stdSimplexCoordinateHomeomorph n x).val ∈ frontier (e.toHomeomorph '' coordinateSimplex n) ↔ _
  rw [← e.toHomeomorph.image_frontier, e.toHomeomorph.injective.mem_set_image,
    mem_frontier_coordinateSimplex_iff]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph_mem_sphere_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph_mem_sphere_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph_mem_sphere_iff ``Submission.DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph_mem_sphere_iff


def stdSimplexNormedBoundarySphereHomeomorph : boundary (Fin (n + 1)) ≃ₜ _root_.Metric.sphere (0 : E) 1 where
  toFun x := ⟨(stdSimplexNormedBallHomeomorph e x.val).val,
    (stdSimplexNormedBallHomeomorph_mem_sphere_iff e x.val).mpr x.prop⟩
  invFun y := ⟨(stdSimplexNormedBallHomeomorph e).symm ⟨y.val, _root_.Metric.sphere_subset_closedBall y.prop⟩,
    (stdSimplexNormedBallHomeomorph_mem_sphere_iff e _).mp (by simp)⟩
  left_inv x := by
    apply Subtype.ext
    exact (stdSimplexNormedBallHomeomorph e).symm_apply_apply x.val
  right_inv y := by
    apply Subtype.ext
    change ((stdSimplexNormedBallHomeomorph e) ((stdSimplexNormedBallHomeomorph e).symm
      ⟨y.val, _root_.Metric.sphere_subset_closedBall y.prop⟩)).val = y.val
    rw [Homeomorph.apply_symm_apply]
  continuous_toFun := (continuous_subtype_val.comp
    ((stdSimplexNormedBallHomeomorph e).continuous.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := ((stdSimplexNormedBallHomeomorph e).symm.continuous.comp
    (continuous_subtype_val.subtype_mk _)).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph ``Submission.DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph


@[simp]
theorem stdSimplexNormedBoundarySphereHomeomorph_val (x : boundary (Fin (n + 1))) :
    (stdSimplexNormedBoundarySphereHomeomorph e x).val =
      (stdSimplexNormedBallHomeomorph e x.val).val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph_val ``Submission.DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph_val

end DifferentialGeometry.Simplex
