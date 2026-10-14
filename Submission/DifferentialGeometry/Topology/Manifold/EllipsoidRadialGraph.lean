import Submission.DifferentialGeometry.Analysis.Calculus.Cutoff.BallRadialFunction
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.Structures

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Manifold _root_.Module
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def ellipsoidRadialFunction (A : E ≃L[ℝ] E) (r : ℝ) (u : _root_.Metric.sphere (0 : E) 1) : ℝ :=
  r / ‖A.symm (u : E)‖

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.ellipsoidRadialFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.ellipsoidRadialFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.ellipsoidRadialFunction ``Submission.DifferentialGeometry.Topology.Manifold.ellipsoidRadialFunction

private theorem norm_symm_unit_pos (A : E ≃L[ℝ] E) (u : _root_.Metric.sphere (0 : E) 1) :
    0 < ‖A.symm (u : E)‖ := by
  apply norm_pos_iff.mpr
  intro h
  apply ne_zero_of_mem_unit_sphere u
  simpa only [A.apply_symm_apply, map_zero] using congrArg A h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.norm_symm_unit_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.norm_symm_unit_pos target :: scope.openDecls } }

theorem ellipsoidRadialFunction_pos (A : E ≃L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (u : _root_.Metric.sphere (0 : E) 1) : 0 < ellipsoidRadialFunction A r u :=
  div_pos hr (norm_symm_unit_pos A u)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.ellipsoidRadialFunction_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.ellipsoidRadialFunction_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.ellipsoidRadialFunction_pos ``Submission.DifferentialGeometry.Topology.Manifold.ellipsoidRadialFunction_pos

theorem contMDiff_ellipsoidRadialFunction {n : ℕ} [Fact (_root_.Module.finrank ℝ E = n + 1)]
    (A : E ≃L[ℝ] E) (r : ℝ) :
    ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (ellipsoidRadialFunction A r) := by
  have hA : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (fun u : _root_.Metric.sphere (0 : E) 1 ↦ A.symm (u : E)) :=
    A.symm.contDiff.contMDiff.comp contMDiff_coe_sphere
  have hn : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (fun u : _root_.Metric.sphere (0 : E) 1 ↦ ‖A.symm (u : E)‖) := by
    intro u
    exact (contDiffAt_norm ℝ (norm_ne_zero_iff.mp (norm_symm_unit_pos A u).ne')).contMDiffAt.comp u
      (hA u)
  have hm := (contMDiff_const (c := r)).mul (hn.inv₀ (fun u ↦ (norm_symm_unit_pos A u).ne'))
  apply hm.congr
  intro u
  exact (div_eq_mul_inv r _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.contMDiff_ellipsoidRadialFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.contMDiff_ellipsoidRadialFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.contMDiff_ellipsoidRadialFunction ``Submission.DifferentialGeometry.Topology.Manifold.contMDiff_ellipsoidRadialFunction

theorem image_closedBall_affine_eq (A : E ≃L[ℝ] E) (p : E) (r : ℝ) :
    (fun x ↦ A x + p) '' _root_.Metric.closedBall 0 r = {y | ‖A.symm (y - p)‖ ≤ r} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [_root_.Set.mem_ofPred_eq, add_sub_cancel_right, A.symm_apply_apply] using mem_closedBall_zero_iff.mp hx
  · intro hy
    refine ⟨A.symm (y - p), mem_closedBall_zero_iff.mpr hy, ?_⟩
    change A (A.symm (y - p)) + p = y
    rw [A.apply_symm_apply, sub_add_cancel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.image_closedBall_affine_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.image_closedBall_affine_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.image_closedBall_affine_eq ``Submission.DifferentialGeometry.Topology.Manifold.image_closedBall_affine_eq

theorem image_ball_affine_eq (A : E ≃L[ℝ] E) (p : E) (r : ℝ) :
    (fun x ↦ A x + p) '' _root_.Metric.ball 0 r = {y | ‖A.symm (y - p)‖ < r} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [_root_.Set.mem_ofPred_eq, add_sub_cancel_right, A.symm_apply_apply] using mem_ball_zero_iff.mp hx
  · intro hy
    refine ⟨A.symm (y - p), mem_ball_zero_iff.mpr hy, ?_⟩
    change A (A.symm (y - p)) + p = y
    rw [A.apply_symm_apply, sub_add_cancel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.image_ball_affine_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.image_ball_affine_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.image_ball_affine_eq ``Submission.DifferentialGeometry.Topology.Manifold.image_ball_affine_eq

theorem smul_add_mem_closedEllipsoid_iff (A : E ≃L[ℝ] E) (p : E) (r : ℝ)
    (u : _root_.Metric.sphere (0 : E) 1) {t : ℝ} (ht : 0 ≤ t) :
    t • (u : E) + p ∈ (fun x ↦ A x + p) '' _root_.Metric.closedBall 0 r ↔
      t ≤ ellipsoidRadialFunction A r u := by
  rw [image_closedBall_affine_eq]
  change ‖A.symm (t • (u : E) + p - p)‖ ≤ r ↔ _
  rw [add_sub_cancel_right, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  exact (le_div_iff₀ (norm_symm_unit_pos A u)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.smul_add_mem_closedEllipsoid_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.smul_add_mem_closedEllipsoid_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.smul_add_mem_closedEllipsoid_iff ``Submission.DifferentialGeometry.Topology.Manifold.smul_add_mem_closedEllipsoid_iff

theorem smul_add_mem_openEllipsoid_iff (A : E ≃L[ℝ] E) (p : E) (r : ℝ)
    (u : _root_.Metric.sphere (0 : E) 1) {t : ℝ} (ht : 0 ≤ t) :
    t • (u : E) + p ∈ (fun x ↦ A x + p) '' _root_.Metric.ball 0 r ↔
      t < ellipsoidRadialFunction A r u := by
  rw [image_ball_affine_eq]
  change ‖A.symm (t • (u : E) + p - p)‖ < r ↔ _
  rw [add_sub_cancel_right, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  exact (lt_div_iff₀ (norm_symm_unit_pos A u)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.smul_add_mem_openEllipsoid_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.smul_add_mem_openEllipsoid_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.smul_add_mem_openEllipsoid_iff ``Submission.DifferentialGeometry.Topology.Manifold.smul_add_mem_openEllipsoid_iff

theorem ellipsoidRadialFunction_lt_ballRadialFunction
    (A : E ≃L[ℝ] E) (p : E) {r R : ℝ} (hr : 0 < r) (hp : ‖p‖ < R)
    (hsub : (fun x ↦ A x + p) '' _root_.Metric.closedBall 0 r ⊆ _root_.Metric.ball 0 R)
    (u : _root_.Metric.sphere (0 : E) 1) :
    ellipsoidRadialFunction A r u < DifferentialGeometry.Analysis.ballRadialFunction p R (u : E) := by
  have ha := ellipsoidRadialFunction_pos A hr u
  have hi := (smul_add_mem_closedEllipsoid_iff A p r u ha.le).mpr le_rfl
  exact (DifferentialGeometry.Analysis.smul_add_mem_ball_iff hp (norm_eq_of_mem_sphere u) ha.le).mp (hsub hi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.ellipsoidRadialFunction_lt_ballRadialFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.ellipsoidRadialFunction_lt_ballRadialFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.ellipsoidRadialFunction_lt_ballRadialFunction ``Submission.DifferentialGeometry.Topology.Manifold.ellipsoidRadialFunction_lt_ballRadialFunction

end DifferentialGeometry.Topology.Manifold
