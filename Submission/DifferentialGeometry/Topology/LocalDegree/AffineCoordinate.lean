import Submission.DifferentialGeometry.Topology.LocalDegree.LinearSphere
import Submission.DifferentialGeometry.Topology.LocalDegree.SphereMapParameter
import Submission.DifferentialGeometry.Topology.LocalDegree.Euclidean

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Filter _root_.Metric _root_.Set
open scoped _root_.Topology
noncomputable section
namespace DifferentialGeometry.LocalDegree
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem normalize_pos_smul (z : E) {a : ℝ} (ha : 0 < a) :
    ‖a • z‖⁻¹ • (a • z) = ‖z‖⁻¹ • z := by
  rw [norm_smul, Real.norm_of_nonneg ha.le, mul_inv_rev, smul_smul,
    mul_assoc, inv_mul_cancel₀ ha.ne', mul_one]

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.normalize_pos_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.normalize_pos_smul target :: scope.openDecls } }

theorem exists_affineCoordinate_closedBall (A : E ≃L[ℝ] F) (x : E) (y : F)
    {S : ℝ} (hS : 0 < S) :
    ∃ R > 0, _root_.Set.MapsTo (fun z => y + A (z - x)) (_root_.Metric.closedBall x R) (_root_.Metric.closedBall y S) := by
  have hc : Continuous (fun z : E => y + A (z - x)) :=
    continuous_const.add (A.continuous.comp (continuous_id.sub continuous_const))
  have hn : (fun z => y + A (z - x)) ⁻¹' _root_.Metric.ball y S ∈ 𝓝 x :=
    hc.continuousAt.preimage_mem_nhds (by simpa using _root_.Metric.ball_mem_nhds y hS)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨ε / 2, by positivity, ?_⟩
  intro z hz
  exact _root_.Metric.ball_subset_closedBall (hball (_root_.Metric.closedBall_subset_ball (by linarith) hz))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.exists_affineCoordinate_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.exists_affineCoordinate_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.exists_affineCoordinate_closedBall ``Submission.DifferentialGeometry.LocalDegree.exists_affineCoordinate_closedBall

private theorem affineRadius_mem (A : E ≃L[ℝ] F) (x : E) (y : F) {R S : ℝ}
    (hball : _root_.Set.MapsTo (fun z => y + A (z - x)) (_root_.Metric.closedBall x R) (_root_.Metric.closedBall y S))
    (r : _root_.Set.Ioc (0 : ℝ) R) (v : _root_.Metric.sphere (0 : E) 1) : (r : ℝ) * ‖A v‖ ∈ _root_.Set.Ioc (0 : ℝ) S := by
    have hv : (v : E) ≠ 0 := by
      intro he
      have hn := norm_eq_of_mem_sphere v
      rw [he, norm_zero] at hn
      exact zero_ne_one hn
    refine ⟨mul_pos r.property.1 (norm_pos_iff.mpr (mt A.map_eq_zero_iff.mp hv)), ?_⟩
    have hmem : x + (r : ℝ) • (v : E) ∈ _root_.Metric.closedBall x R := by
      rw [_root_.Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg r.property.1.le, norm_eq_of_mem_sphere v, mul_one]
      exact r.property.2
    have hh := hball hmem
    simpa only [_root_.Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, map_smul,
      norm_smul, Real.norm_of_nonneg r.property.1.le] using hh

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.affineRadius_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.affineRadius_mem target :: scope.openDecls } }

private def affineRadius (A : E ≃L[ℝ] F) (x : E) (y : F) {R S : ℝ}
    (hball : _root_.Set.MapsTo (fun z => y + A (z - x)) (_root_.Metric.closedBall x R) (_root_.Metric.closedBall y S))
    (r : _root_.Set.Ioc (0 : ℝ) R) : C(_root_.Metric.sphere (0 : E) 1, _root_.Set.Ioc (0 : ℝ) S) where
  toFun v := ⟨(r : ℝ) * ‖A v‖, affineRadius_mem A x y hball r v⟩
  continuous_toFun := (continuous_const.mul
    (A.continuous.comp continuous_subtype_val).norm).subtype_mk _

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.affineRadius
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.affineRadius target :: scope.openDecls } }

private theorem affineRadius_direction (A : E ≃L[ℝ] F) (x : E) (y : F) {R S : ℝ}
    (hball : _root_.Set.MapsTo (fun z => y + A (z - x)) (_root_.Metric.closedBall x R) (_root_.Metric.closedBall y S))
    (r : _root_.Set.Ioc (0 : ℝ) R) (v : _root_.Metric.sphere (0 : E) 1) :
    (affineRadius A x y hball r v : ℝ) • (linearSphereMap A v : F) =
      A ((r : ℝ) • (v : E)) := by
  have hn : ‖A v‖ ≠ 0 := by
    have hp := (affineRadius A x y hball r v).property.1
    change 0 < (r : ℝ) * ‖A v‖ at hp
    intro hh
    rw [hh, _root_.MulZeroClass.mul_zero] at hp
    exact lt_irrefl 0 hp
  change ((r : ℝ) * ‖A v‖) • (linearSphereMap A v : F) = _
  rw [linearSphereMap_apply, map_smul, smul_smul, mul_assoc, mul_inv_cancel₀ hn, mul_one]

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.affineRadius_direction
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.affineRadius_direction target :: scope.openDecls } }

theorem sphereMap_affineCoordinate_homotopy (A : E ≃L[ℝ] F) (x : E) (y : F)
    {V : F → F} {R S : ℝ} (hS : 0 < S)
    (hV : ContinuousOn V (_root_.Metric.closedBall y S))
    (hz : ∀ z ∈ _root_.Metric.closedBall y S, z ≠ y → V z ≠ 0)
    (hball : _root_.Set.MapsTo (fun z => y + A (z - x)) (_root_.Metric.closedBall x R) (_root_.Metric.closedBall y S))
    (hP : ContinuousOn (fun z => A.symm (V (y + A (z - x)))) (_root_.Metric.closedBall x R))
    (hPz : ∀ z ∈ _root_.Metric.closedBall x R, z ≠ x → A.symm (V (y + A (z - x))) ≠ 0)
    (r : _root_.Set.Ioc (0 : ℝ) R) :
    Nonempty ((sphereMap (fun z => A.symm (V (y + A (z - x)))) x R hP hPz r).Homotopy
      ((linearSphereMap A.symm).comp
        ((sphereMap V y S hV hz ⟨S, hS, le_rfl⟩).comp (linearSphereMap A)))) := by
  let rv := affineRadius A x y hball r
  let H := sphereMapParameterHomotopy V y S hV hz rv
    (ContinuousMap.const _ ⟨S, hS, le_rfl⟩) (linearSphereMap A)
  have heq : (linearSphereMap A.symm).comp
      (sphereMapParameter V y S hV hz rv (linearSphereMap A)) =
      sphereMap (fun z => A.symm (V (y + A (z - x)))) x R hP hPz r := by
    apply ContinuousMap.ext
    intro v
    apply Subtype.ext
    have harg : y + (rv v : ℝ) • (linearSphereMap A v : F) =
        y + A ((r : ℝ) • (v : E)) := by
      rw [affineRadius_direction]
    have hnorm : 0 < ‖V (y + A ((r : ℝ) • (v : E)))‖ := by
      have hh := (sphereMapParameter V y S hV hz rv (linearSphereMap A) v).property
      rw [_root_.Metric.mem_sphere, dist_zero_right] at hh
      by_contra hn
      have he : V (y + A ((r : ℝ) • (v : E))) = 0 :=
        norm_eq_zero.mp (le_antisymm (le_of_not_gt hn) (norm_nonneg _))
      have he' : (sphereMapParameter V y S hV hz rv (linearSphereMap A) v : F) = 0 := by
        rw [sphereMapParameter_apply, harg, he, smul_zero]
      rw [he', norm_zero] at hh
      exact zero_ne_one hh
    rw [ContinuousMap.comp_apply, linearSphereMap_apply, sphereMapParameter_apply, harg]
    simp only [map_smul, sphereMap_apply, add_sub_cancel_left]
    simpa only [map_smul] using
      normalize_pos_smul (A.symm (V (y + A ((r : ℝ) • (v : E))))) (inv_pos.mpr hnorm)
  exact ⟨((ContinuousMap.Homotopy.refl (linearSphereMap A.symm)).comp H).cast heq
    (by rw [sphereMapParameter_const])⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereMap_affineCoordinate_homotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereMap_affineCoordinate_homotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereMap_affineCoordinate_homotopy ``Submission.DifferentialGeometry.LocalDegree.sphereMap_affineCoordinate_homotopy

theorem isolatedZero_affineCoordinate (A : E ≃L[ℝ] F) (x : E) (y : F)
    {V : F → F} (hV : isolatedZero V y) :
    isolatedZero (fun z => A.symm (V (y + A (z - x)))) x := by
  obtain ⟨S, hS⟩ := hV
  obtain ⟨R, hR, hball⟩ := exists_affineCoordinate_closedBall A x y hS.pos
  refine ⟨R, hR, ?_, ?_⟩
  · exact A.symm.continuous.comp_continuousOn (hS.continuousOn.comp
      (continuous_const.add (A.continuous.comp (continuous_id.sub continuous_const))).continuousOn
      hball)
  · intro z hz
    rw [A.symm.map_eq_zero_iff, hS.zero_iff _ (hball hz)]
    simp only [add_eq_left, A.map_eq_zero_iff, sub_eq_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.isolatedZero_affineCoordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.isolatedZero_affineCoordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.isolatedZero_affineCoordinate ``Submission.DifferentialGeometry.LocalDegree.isolatedZero_affineCoordinate

variable {d : ℕ}


theorem euclideanSphereDegree_linear_inverse
    (A : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    euclideanSphereDegree (linearSphereMap A.symm) *
      euclideanSphereDegree (linearSphereMap A) = 1 := by
  rw [← euclideanSphereDegree_comp]
  have he : (linearSphereMap A.symm).comp (linearSphereMap A) = ContinuousMap.id _ := by
    apply ContinuousMap.ext
    exact linearSphereMap_symm_apply A
  rw [he, euclideanSphereDegree_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereDegree_linear_inverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereDegree_linear_inverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereDegree_linear_inverse ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereDegree_linear_inverse

theorem euclideanLocalDegree_affineCoordinate
    (A : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (x y : EuclideanSpace ℝ (Fin (d + 1)))
    {V : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    (hV : isolatedZero V y) :
    euclideanLocalDegree (fun z => A.symm (V (y + A (z - x)))) x
        (isolatedZero_affineCoordinate A x y hV) = euclideanLocalDegree V y hV := by
  obtain ⟨S, hS⟩ := hV
  obtain ⟨R, hR, hball⟩ := exists_affineCoordinate_closedBall A x y hS.pos
  have hP : IsolatingRadius (fun z => A.symm (V (y + A (z - x)))) x R := by
    refine ⟨hR, ?_, ?_⟩
    · exact A.symm.continuous.comp_continuousOn (hS.continuousOn.comp
        (continuous_const.add (A.continuous.comp (continuous_id.sub continuous_const))).continuousOn
        hball)
    · intro z hz
      rw [A.symm.map_eq_zero_iff, hS.zero_iff _ (hball hz)]
      simp only [add_eq_left, A.map_eq_zero_iff, sub_eq_zero]
  erw [euclideanLocalDegree_eq_sphereDegree _ hP ⟨R, hR, le_rfl⟩,
    euclideanLocalDegree_eq_sphereDegree _ hS ⟨S, hS.pos, le_rfl⟩]
  obtain ⟨H⟩ := sphereMap_affineCoordinate_homotopy A x y hS.pos hS.continuousOn
    hS.nonzero hball hP.continuousOn hP.nonzero ⟨R, hR, le_rfl⟩
  rw [euclideanSphereDegree_eq_of_homotopy H, euclideanSphereDegree_comp,
    euclideanSphereDegree_comp]
  have hi := euclideanSphereDegree_linear_inverse A
  calc
    _ = (euclideanSphereDegree (linearSphereMap A.symm) *
        euclideanSphereDegree (linearSphereMap A)) *
        euclideanSphereDegree (sphereMap V y S hS.continuousOn hS.nonzero ⟨S, hS.pos, le_rfl⟩) :=
      by ring
    _ = _ := by rw [hi, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_affineCoordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_affineCoordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_affineCoordinate ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_affineCoordinate

end DifferentialGeometry.LocalDegree
