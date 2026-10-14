import Submission.DifferentialGeometry.Topology.PlanarJordan.AlternatingCross
import Submission.DifferentialGeometry.Topology.LevelSet.Disk.StrictLevels

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology.PlanarJordan

local notation "Plane" => Schoenflies.Plane

theorem not_alternating_cross_of_disk_maximum_minimum_principle
    {R : ℝ} (hR : 0 < R) {u : Plane → ℝ}
    (hu : ContinuousOn u (_root_.Metric.closedBall (0 : Plane) R))
    (hboundary : ∀ x ∈ _root_.Metric.sphere (0 : Plane) R, u x = x 0)
    (hmax : ∀ Ω : Set (_root_.Metric.closedBall (0 : Plane) R), IsOpen Ω → IsCompact (closure Ω) →
      Ω ⊆ {x | ‖(x : Plane)‖ = R}ᶜ → ∀ c : ℝ,
        (∀ x ∈ frontier Ω, u x ≤ c) → ∀ x ∈ Ω, u x ≤ c)
    (hmin : ∀ Ω : Set (_root_.Metric.closedBall (0 : Plane) R), IsOpen Ω → IsCompact (closure Ω) →
      Ω ⊆ {x | ‖(x : Plane)‖ = R}ᶜ → ∀ c : ℝ,
        (∀ x ∈ frontier Ω, c ≤ u x) → ∀ x ∈ Ω, c ≤ u x)
    (e : OpenPartialHomeomorph (ℝ × ℝ) Plane) {ε : ℝ} (hε : 0 < ε)
    (hsource : _root_.Set.Icc (-ε) ε ×ˢ _root_.Set.Icc (-ε) ε ⊆ e.source)
    (himage : _root_.Set.MapsTo e (_root_.Set.Icc (-ε) ε ×ˢ _root_.Set.Icc (-ε) ε) (_root_.Metric.ball (0 : Plane) R))
    (hpositive : ∀ t ∈ _root_.Set.Icc (-ε) ε, t ≠ 0 → u (e (0, 0)) < u (e (t, 0)))
    (hnegative : ∀ t ∈ _root_.Set.Icc (-ε) ε, t ≠ 0 → u (e (0, t)) < u (e (0, 0))) : False := by
  have hpos := DifferentialGeometry.Topology.isPreconnected_ball_superlevel_of_maximum_principle
    hR hu hboundary hmax (u (e (0, 0)))
  have hneg := DifferentialGeometry.Topology.isPreconnected_ball_sublevel_of_minimum_principle
    hR hu hboundary hmin (u (e (0, 0)))
  exact not_alternating_cross_of_preconnected_strict_levels _root_.Metric.isOpen_ball
    (hu.mono _root_.Metric.ball_subset_closedBall) hpos hneg e hε hsource himage rfl hpositive hnegative

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.not_alternating_cross_of_disk_maximum_minimum_principle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.not_alternating_cross_of_disk_maximum_minimum_principle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.not_alternating_cross_of_disk_maximum_minimum_principle ``Submission.DifferentialGeometry.Topology.PlanarJordan.not_alternating_cross_of_disk_maximum_minimum_principle

end DifferentialGeometry.Topology.PlanarJordan

end

end

section

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Metric _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Topology.PlanarJordan

local notation "Plane" => Schoenflies.Plane

theorem exists_closed_cross_box_in_source_and_open_image
    (e : OpenPartialHomeomorph (ℝ × ℝ) Plane)
    (h0 : ((0 : ℝ), (0 : ℝ)) ∈ e.source) {D : Set Plane} (hD : IsOpen D)
    (himage : e (0, 0) ∈ D) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ η ∧
      Icc (-ε) ε ×ˢ _root_.Set.Icc (-ε) ε ⊆ e.source ∧ _root_.Set.MapsTo e (_root_.Set.Icc (-ε) ε ×ˢ _root_.Set.Icc (-ε) ε) D := by
  have he : ContinuousAt e (0 : ℝ × ℝ) := e.continuousOn.continuousAt (e.open_source.mem_nhds h0)
  have hnb : e.source ∩ e ⁻¹' D ∈ 𝓝 (0 : ℝ × ℝ) :=
    _root_.Filter.inter_mem (e.open_source.mem_nhds h0) (he.preimage_mem_nhds (hD.mem_nhds himage))
  obtain ⟨r, hr, hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnb
  let ε := _root_.Min.min r η
  have hε : 0 < ε := lt_min hr hη
  have hbox : _root_.Set.Icc (-ε) ε ×ˢ _root_.Set.Icc (-ε) ε ⊆ _root_.Metric.closedBall (0 : ℝ × ℝ) r := by
    intro p hp
    rw [_root_.Metric.mem_closedBall, Prod.dist_eq]
    change _root_.Max.max (_root_.Dist.dist p.1 0) (_root_.Dist.dist p.2 0) ≤ r
    rw [dist_zero_right, dist_zero_right, max_le_iff]
    exact ⟨(abs_le.mpr hp.1).trans (min_le_left _ _),
      (abs_le.mpr hp.2).trans (min_le_left _ _)⟩
  exact ⟨ε, hε, min_le_right _ _, fun p hp => (hrsub (hbox hp)).1,
    fun p hp => (hrsub (hbox hp)).2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.exists_closed_cross_box_in_source_and_open_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.exists_closed_cross_box_in_source_and_open_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.exists_closed_cross_box_in_source_and_open_image ``Submission.DifferentialGeometry.Topology.PlanarJordan.exists_closed_cross_box_in_source_and_open_image

theorem not_local_alternating_cross_of_disk_maximum_minimum_principle
    {R : ℝ} (hR : 0 < R) {u : Plane → ℝ}
    (hu : ContinuousOn u (_root_.Metric.closedBall (0 : Plane) R))
    (hboundary : ∀ x ∈ _root_.Metric.sphere (0 : Plane) R, u x = x 0)
    (hmax : ∀ Ω : Set (_root_.Metric.closedBall (0 : Plane) R), IsOpen Ω → IsCompact (closure Ω) →
      Ω ⊆ {x | ‖(x : Plane)‖ = R}ᶜ → ∀ c : ℝ,
        (∀ x ∈ frontier Ω, u x ≤ c) → ∀ x ∈ Ω, u x ≤ c)
    (hmin : ∀ Ω : Set (_root_.Metric.closedBall (0 : Plane) R), IsOpen Ω → IsCompact (closure Ω) →
      Ω ⊆ {x | ‖(x : Plane)‖ = R}ᶜ → ∀ c : ℝ,
        (∀ x ∈ frontier Ω, c ≤ u x) → ∀ x ∈ Ω, c ≤ u x)
    (e : OpenPartialHomeomorph (ℝ × ℝ) Plane)
    (hsource : ((0 : ℝ), (0 : ℝ)) ∈ e.source) (hcenter : e (0, 0) ∈ _root_.Metric.ball (0 : Plane) R)
    {η : ℝ} (hη : 0 < η)
    (hpositive : ∀ t : ℝ, 0 < |t| → |t| < η → u (e (0, 0)) < u (e (t, 0)))
    (hnegative : ∀ t : ℝ, 0 < |t| → |t| < η → u (e (0, t)) < u (e (0, 0))) : False := by
  obtain ⟨ε, hε, hεη, hbox, hmap⟩ := exists_closed_cross_box_in_source_and_open_image
    e hsource _root_.Metric.isOpen_ball hcenter (half_pos hη)
  apply not_alternating_cross_of_disk_maximum_minimum_principle hR hu hboundary hmax hmin
    e hε hbox hmap
  · intro t ht ht0
    exact hpositive t (abs_pos.mpr ht0) ((abs_le.mpr ht).trans_lt (hεη.trans_lt (half_lt_self hη)))
  · intro t ht ht0
    exact hnegative t (abs_pos.mpr ht0) ((abs_le.mpr ht).trans_lt (hεη.trans_lt (half_lt_self hη)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.not_local_alternating_cross_of_disk_maximum_minimum_principle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.not_local_alternating_cross_of_disk_maximum_minimum_principle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.not_local_alternating_cross_of_disk_maximum_minimum_principle ``Submission.DifferentialGeometry.Topology.PlanarJordan.not_local_alternating_cross_of_disk_maximum_minimum_principle

end DifferentialGeometry.Topology.PlanarJordan

end

end
