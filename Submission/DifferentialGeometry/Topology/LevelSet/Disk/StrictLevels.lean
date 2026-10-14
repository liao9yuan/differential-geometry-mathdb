import Submission.DifferentialGeometry.Topology.Connected.MaximumPrinciple
import Submission.DifferentialGeometry.Topology.Connected.BallInterior
import Submission.DifferentialGeometry.Topology.Connected.CircleCaps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem isPreconnected_ball_superlevel_of_maximum_principle
    {R : ℝ} (hR : 0 < R) {f : V → ℝ}
    (hf : ContinuousOn f (_root_.Metric.closedBall (0 : V) R))
    (hboundary : ∀ x ∈ _root_.Metric.sphere (0 : V) R, f x = x 0)
    (hmax : ∀ Ω : Set (_root_.Metric.closedBall (0 : V) R), IsOpen Ω → IsCompact (closure Ω) →
      Ω ⊆ {x | ‖(x : V)‖ = R}ᶜ → ∀ c : ℝ,
        (∀ x ∈ frontier Ω, f x ≤ c) → ∀ x ∈ Ω, f x ≤ c) (a : ℝ) :
    IsPreconnected (_root_.Metric.ball (0 : V) R ∩ {x | a < f x}) := by
  let D := _root_.Metric.closedBall (0 : V) R
  let : CompactSpace D := isCompact_iff_compactSpace.mp (_root_.ProperSpace.isCompact_closedBall (0 : V) R)
  let : LocallyPathConnectedSpace D := (convex_closedBall (0 : V) R).locallyPathConnectedSpace
  let B : Set D := {x | ‖(x : V)‖ = R}
  have hfc : Continuous (fun x : D => f x) := hf.domRestrict
  have hcompact : IsCompact {x : D | a ≤ f x} :=
    (isClosed_le continuous_const hfc).isCompact
  have hcap : IsPreconnected (B ∩ {x : D | a < f x}) := by
    apply _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    have heq : Subtype.val '' (B ∩ {x : D | a < f x}) =
        sphere (0 : V) R ∩ {x | a < x 0} := by
      ext x
      constructor
      · rintro ⟨y, ⟨hyR, hya⟩, rfl⟩
        have hy : (y : V) ∈ _root_.Metric.sphere (0 : V) R := mem_sphere_zero_iff_norm.mpr hyR
        exact ⟨hy, by simpa only [_root_.Set.mem_ofPred_eq, hboundary y hy] using hya⟩
      · rintro ⟨hxR, hxa⟩
        exact ⟨⟨x, _root_.Metric.sphere_subset_closedBall hxR⟩,
          ⟨mem_sphere_zero_iff_norm.mp hxR, by
            simpa only [_root_.Set.mem_ofPred_eq, hboundary x hxR] using hxa⟩, rfl⟩
    rw [heq]
    exact isPreconnected_sphere_inter_coordinate_gt hR.le a
  have hc := hfc.isPreconnected_gt_of_maximum_principle hcompact hmax hcap
  have himage : Subtype.val '' {x : D | a < f x} =
      closedBall (0 : V) R ∩ {x | a < f x} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hxD, hxa⟩
      exact ⟨⟨x, hxD⟩, hxa, rfl⟩
  exact hf.isPreconnected_ball_gt_of_closedBall hR
    (himage ▸ hc.image Subtype.val continuous_subtype_val.continuousOn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPreconnected_ball_superlevel_of_maximum_principle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPreconnected_ball_superlevel_of_maximum_principle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPreconnected_ball_superlevel_of_maximum_principle ``Submission.DifferentialGeometry.Topology.isPreconnected_ball_superlevel_of_maximum_principle

theorem isPreconnected_ball_sublevel_of_minimum_principle
    {R : ℝ} (hR : 0 < R) {f : V → ℝ}
    (hf : ContinuousOn f (_root_.Metric.closedBall (0 : V) R))
    (hboundary : ∀ x ∈ _root_.Metric.sphere (0 : V) R, f x = x 0)
    (hmin : ∀ Ω : Set (_root_.Metric.closedBall (0 : V) R), IsOpen Ω → IsCompact (closure Ω) →
      Ω ⊆ {x | ‖(x : V)‖ = R}ᶜ → ∀ c : ℝ,
        (∀ x ∈ frontier Ω, c ≤ f x) → ∀ x ∈ Ω, c ≤ f x) (a : ℝ) :
    IsPreconnected (_root_.Metric.ball (0 : V) R ∩ {x | f x < a}) := by
  let D := _root_.Metric.closedBall (0 : V) R
  let : CompactSpace D := isCompact_iff_compactSpace.mp (_root_.ProperSpace.isCompact_closedBall (0 : V) R)
  let : LocallyPathConnectedSpace D := (convex_closedBall (0 : V) R).locallyPathConnectedSpace
  let B : Set D := {x | ‖(x : V)‖ = R}
  have hfc : Continuous (fun x : D => f x) := hf.domRestrict
  have hcompact : IsCompact {x : D | f x ≤ a} :=
    (isClosed_le hfc continuous_const).isCompact
  have hcap : IsPreconnected (B ∩ {x : D | f x < a}) := by
    apply _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    have heq : Subtype.val '' (B ∩ {x : D | f x < a}) =
        sphere (0 : V) R ∩ {x | x 0 < a} := by
      ext x
      constructor
      · rintro ⟨y, ⟨hyR, hya⟩, rfl⟩
        have hy : (y : V) ∈ _root_.Metric.sphere (0 : V) R := mem_sphere_zero_iff_norm.mpr hyR
        exact ⟨hy, by simpa only [_root_.Set.mem_ofPred_eq, hboundary y hy] using hya⟩
      · rintro ⟨hxR, hxa⟩
        exact ⟨⟨x, _root_.Metric.sphere_subset_closedBall hxR⟩,
          ⟨mem_sphere_zero_iff_norm.mp hxR, by
            simpa only [_root_.Set.mem_ofPred_eq, hboundary x hxR] using hxa⟩, rfl⟩
    rw [heq]
    exact isPreconnected_sphere_inter_coordinate_lt hR.le a
  have hc := hfc.isPreconnected_lt_of_minimum_principle hcompact hmin hcap
  have himage : Subtype.val '' {x : D | f x < a} =
      closedBall (0 : V) R ∩ {x | f x < a} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hxD, hxa⟩
      exact ⟨⟨x, hxD⟩, hxa, rfl⟩
  exact hf.isPreconnected_ball_lt_of_closedBall hR
    (himage ▸ hc.image Subtype.val continuous_subtype_val.continuousOn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPreconnected_ball_sublevel_of_minimum_principle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPreconnected_ball_sublevel_of_minimum_principle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPreconnected_ball_sublevel_of_minimum_principle ``Submission.DifferentialGeometry.Topology.isPreconnected_ball_sublevel_of_minimum_principle

end DifferentialGeometry.Topology

end

end
