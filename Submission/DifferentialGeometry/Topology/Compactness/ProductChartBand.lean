import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.Compactness

open _root_.Set

theorem isCompact_coordinate_band_of_product_chart
    {N M : Type*} [TopologicalSpace N] [CompactSpace N] [TopologicalSpace M]
    (e : OpenPartialHomeomorph (N × ℝ) M) (a b : ℝ)
    (hsource : (_root_.Set.univ : Set N) ×ˢ _root_.Set.Icc a b ⊆ e.source) :
    IsCompact (e.target ∩ (fun x ↦ (e.symm x).2) ⁻¹' _root_.Set.Icc a b) := by
  have heq : e '' ((_root_.Set.univ : Set N) ×ˢ _root_.Set.Icc a b) =
      e.target ∩ (fun x ↦ (e.symm x).2) ⁻¹' _root_.Set.Icc a b := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨e.map_source (hsource hp), ?_⟩
      change (e.symm (e p)).2 ∈ _root_.Set.Icc a b
      rw [e.left_inv (hsource hp)]
      exact hp.2
    · rintro ⟨hx, hband⟩
      exact ⟨e.symm x, ⟨mem_univ _, hband⟩, e.right_inv hx⟩
  rw [← heq]
  exact (isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc).image_of_continuousOn
    (e.continuousOn.mono hsource)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Compactness.isCompact_coordinate_band_of_product_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Compactness.isCompact_coordinate_band_of_product_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Compactness.isCompact_coordinate_band_of_product_chart ``Submission.DifferentialGeometry.Topology.Compactness.isCompact_coordinate_band_of_product_chart

theorem closure_coordinate_band_subset_target_of_product_chart
    {N M : Type*} [TopologicalSpace N] [CompactSpace N] [TopologicalSpace M] [T2Space M]
    (e : OpenPartialHomeomorph (N × ℝ) M) (a b : ℝ)
    (hsource : (_root_.Set.univ : Set N) ×ˢ _root_.Set.Icc a b ⊆ e.source) :
    closure (e.target ∩ (fun x ↦ (e.symm x).2) ⁻¹' _root_.Set.Icc a b) ⊆ e.target := by
  rw [(isCompact_coordinate_band_of_product_chart e a b hsource).isClosed.closure_eq]
  exact _root_.Set.inter_subset_left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Compactness.closure_coordinate_band_subset_target_of_product_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Compactness.closure_coordinate_band_subset_target_of_product_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Compactness.closure_coordinate_band_subset_target_of_product_chart ``Submission.DifferentialGeometry.Topology.Compactness.closure_coordinate_band_subset_target_of_product_chart

end DifferentialGeometry.Topology.Compactness
