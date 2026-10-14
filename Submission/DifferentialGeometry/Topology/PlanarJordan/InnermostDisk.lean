import Submission.DifferentialGeometry.Topology.PlanarJordan.AmbientExtension
import Submission.DifferentialGeometry.Topology.PlanarJordan.Innermost
import Mathlib.Topology.MetricSpace.Thickening

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology.PlanarJordan

theorem isJordanCurve_image_sphere
    (F : Schoenflies.Plane ≃ₜ Schoenflies.Plane) (c : Schoenflies.Plane) {r : ℝ} (hr : 0 < r) :
    Schoenflies.IsJordanCurve (F '' _root_.Metric.sphere c r) := by
  let N : Schoenflies.Plane ≃ₜ Schoenflies.Plane :=
    (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft c)
  let j : _root_.Metric.sphere (0 : Schoenflies.Plane) 1 → Schoenflies.Plane := fun x => F (N x.val)
  have hj : Topology.IsEmbedding j := (N.trans F).isEmbedding.comp .subtypeVal
  have hjrange : _root_.Set.range j = F '' _root_.Metric.sphere c r := by
    apply Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      refine ⟨N x.val, ?_, rfl⟩
      have hxn : ‖x.val‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
      change _root_.Dist.dist (c + r • x.val) c = r
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hxn, mul_one]
    · rintro _ ⟨y, hy, rfl⟩
      have hyn : ‖y - c‖ = r := by simpa only [_root_.Metric.mem_sphere, dist_eq_norm] using hy
      have hx : r⁻¹ • (y - c) ∈ _root_.Metric.sphere (0 : Schoenflies.Plane) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hr), hyn, inv_mul_cancel₀ hr.ne']
      refine ⟨⟨r⁻¹ • (y - c), hx⟩, ?_⟩
      change F (c + r • (r⁻¹ • (y - c))) = F y
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
  exact hjrange ▸ isJordanCurve_range_of_isEmbedding_circle hj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_image_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_image_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_image_sphere ``Submission.DifferentialGeometry.Topology.PlanarJordan.isJordanCurve_image_sphere

theorem image_ball_eq_inside_image_sphere
    (F : Schoenflies.Plane ≃ₜ Schoenflies.Plane) (c : Schoenflies.Plane) {r : ℝ} (hr : 0 < r) :
    F '' _root_.Metric.ball c r = Schoenflies.inside (F '' _root_.Metric.sphere c r) := by
  let U := F '' _root_.Metric.ball c r
  have hU : IsOpen U := F.isOpenMap _ _root_.Metric.isOpen_ball
  have hconn : IsConnected U := (convex_ball c r).isConnected
    (nonempty_ball.mpr hr) |>.image F F.continuous.continuousOn
  have hfront : frontier U = F '' _root_.Metric.sphere c r := by
    rw [← F.image_frontier, frontier_ball c hr.ne']
  have hbounded : Bornology.IsBounded U :=
    ((_root_.ProperSpace.isCompact_closedBall c r).image F.continuous).isBounded.subset
      (_root_.Set.image_mono _root_.Metric.ball_subset_closedBall)
  obtain ⟨x, hx⟩ := hconn.nonempty
  have hsub : U ⊆ (F '' _root_.Metric.sphere c r)ᶜ := by
    intro y hy hye
    exact (hU.frontier_eq ▸ (hfront ▸ hye)).2 hy
  have hcomponent : connectedComponentIn (F '' _root_.Metric.sphere c r)ᶜ x = U :=
    Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint hU
      hconn.isPreconnected hsub (by rw [hfront]; exact _root_.Set.inter_compl_self _) hx
  have hxinside : x ∈ Schoenflies.inside (F '' _root_.Metric.sphere c r) :=
    ⟨hsub hx, hcomponent.symm ▸ hbounded⟩
  have hsep := Schoenflies.jordan_curve_theorem (isJordanCurve_image_sphere F c hr)
  exact hcomponent.symm.trans (hsep.connectedComponentIn_eq_inside hxinside)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.image_ball_eq_inside_image_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.image_ball_eq_inside_image_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.image_ball_eq_inside_image_sphere ``Submission.DifferentialGeometry.Topology.PlanarJordan.image_ball_eq_inside_image_sphere

theorem image_closedBall_eq_closure_inside_image_sphere
    (F : Schoenflies.Plane ≃ₜ Schoenflies.Plane) (c : Schoenflies.Plane) {r : ℝ} (hr : 0 < r) :
    F '' _root_.Metric.closedBall c r = closure (Schoenflies.inside (F '' _root_.Metric.sphere c r)) := by
  rw [← closure_ball c hr.ne', F.image_closure, image_ball_eq_inside_image_sphere F c hr]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.image_closedBall_eq_closure_inside_image_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.image_closedBall_eq_closure_inside_image_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.image_closedBall_eq_closure_inside_image_sphere ``Submission.DifferentialGeometry.Topology.PlanarJordan.image_closedBall_eq_closure_inside_image_sphere

theorem image_closedBall_eq_of_image_sphere_eq
    (F G : Schoenflies.Plane ≃ₜ Schoenflies.Plane) (c d : Schoenflies.Plane)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hboundary : F '' _root_.Metric.sphere c r = G '' _root_.Metric.sphere d s) :
    F '' _root_.Metric.closedBall c r = G '' _root_.Metric.closedBall d s := by
  rw [image_closedBall_eq_closure_inside_image_sphere F c hr,
    image_closedBall_eq_closure_inside_image_sphere G d hs, hboundary]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.image_closedBall_eq_of_image_sphere_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.image_closedBall_eq_of_image_sphere_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.image_closedBall_eq_of_image_sphere_eq ``Submission.DifferentialGeometry.Topology.PlanarJordan.image_closedBall_eq_of_image_sphere_eq

theorem exists_homeomorph_extending_circle_embedding_image_ball
    {e : _root_.Metric.sphere (0 : Schoenflies.Plane) 1 → Schoenflies.Plane}
    (he : Topology.IsEmbedding e) :
    ∃ F : Schoenflies.Plane ≃ₜ Schoenflies.Plane,
      (∀ z : _root_.Metric.sphere (0 : Schoenflies.Plane) 1, F z = e z) ∧
      F '' _root_.Metric.ball (0 : Schoenflies.Plane) 1 = Schoenflies.inside (_root_.Set.range e) ∧
      F '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 = closure (Schoenflies.inside (_root_.Set.range e)) := by
  obtain ⟨F, hF⟩ := exists_homeomorph_extending_circle_embedding he
  have hboundary : F '' _root_.Metric.sphere (0 : Schoenflies.Plane) 1 = _root_.Set.range e := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (hF ⟨x, hx⟩).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, hF x⟩
  have hball : F '' _root_.Metric.ball (0 : Schoenflies.Plane) 1 = Schoenflies.inside (_root_.Set.range e) := by
    rw [image_ball_eq_inside_image_sphere F 0 zero_lt_one, hboundary]
  refine ⟨F, hF, hball, ?_⟩
  rw [← closure_ball (0 : Schoenflies.Plane) one_ne_zero, F.image_closure, hball]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_extending_circle_embedding_image_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_extending_circle_embedding_image_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_extending_circle_embedding_image_ball ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_homeomorph_extending_circle_embedding_image_ball

theorem exists_innermost_circle_disk
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (e : ι → _root_.Metric.sphere (0 : Schoenflies.Plane) 1 → Schoenflies.Plane)
    (he : ∀ i ∈ s, Topology.IsEmbedding (e i))
    (hdisjoint : (s : Set ι).Pairwise fun i j => Disjoint (_root_.Set.range (e i)) (_root_.Set.range (e j))) :
    ∃ i ∈ s, ∃ F : Schoenflies.Plane ≃ₜ Schoenflies.Plane,
      (∀ z : _root_.Metric.sphere (0 : Schoenflies.Plane) 1, F z = e i z) ∧
      F '' _root_.Metric.ball (0 : Schoenflies.Plane) 1 = Schoenflies.inside (_root_.Set.range (e i)) ∧
      F '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 =
        closure (Schoenflies.inside (_root_.Set.range (e i))) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ j ∈ s, j ≠ i →
        Disjoint (_root_.Metric.cthickening δ (F '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1)) (_root_.Set.range (e j)) := by
  classical
  let curves := s.image (fun i => _root_.Set.range (e i))
  have hcurves : ∀ C ∈ curves, Schoenflies.IsJordanCurve C := by
    intro C hC
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC
    exact isJordanCurve_range_of_isEmbedding_circle (he i hi)
  have hcurvesdisjoint : (curves : Set (Set Schoenflies.Plane)).Pairwise Disjoint := by
    intro C hC J hJ hCJ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hJ
    exact hdisjoint hi hj (fun hij => hCJ (congrArg (fun k => _root_.Set.range (e k)) hij))
  obtain ⟨C, hC, hinside⟩ := exists_innermost_jordan_curve curves
    (hs.image _) hcurves hcurvesdisjoint
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨F, hF, hball, hclosed⟩ :=
    exists_homeomorph_extending_circle_embedding_image_ball (he i hi)
  have hdisk : ∀ j ∈ s, j ≠ i →
      Disjoint (F '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1) (_root_.Set.range (e j)) := by
    intro j hj hji
    rw [hclosed, closure_eq_self_union_frontier,
      (Schoenflies.jordan_curve_theorem
        (isJordanCurve_range_of_isEmbedding_circle (he i hi))).frontier_inside]
    exact (hinside _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)).union_left
      (hdisjoint hi hj hji.symm)
  let rest := ⋃ j ∈ s.erase i, _root_.Set.range (e j)
  have hrest : IsClosed rest := isClosed_biUnion_finset fun j hj =>
    (isJordanCurve_range_of_isEmbedding_circle (he j (Finset.mem_of_mem_erase hj))).isClosed
  have havoid : F '' _root_.Metric.closedBall (0 : Schoenflies.Plane) 1 ⊆ restᶜ := by
    intro x hx
    simp only [rest, _root_.Set.mem_compl_iff, _root_.Set.mem_iUnion, not_exists]
    intro j hj hjx
    exact Set.disjoint_left.mp (hdisk j (Finset.mem_of_mem_erase hj)
      (Finset.ne_of_mem_erase hj)) hx hjx
  obtain ⟨δ, hδ, hthick⟩ :=
    ((_root_.ProperSpace.isCompact_closedBall (0 : Schoenflies.Plane) 1).image F.continuous).exists_cthickening_subset_open hrest.isOpen_compl havoid
  refine ⟨i, hi, F, hF, hball, hclosed, δ, hδ, ?_⟩
  intro j hj hji
  apply Set.disjoint_left.mpr
  intro x hx hjx
  exact hthick hx (mem_iUnion.mpr ⟨j,
    mem_iUnion.mpr ⟨Finset.mem_erase.mpr ⟨hji, hj⟩, hjx⟩⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_innermost_circle_disk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_innermost_circle_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_innermost_circle_disk ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_innermost_circle_disk

end DifferentialGeometry.Topology.PlanarJordan
