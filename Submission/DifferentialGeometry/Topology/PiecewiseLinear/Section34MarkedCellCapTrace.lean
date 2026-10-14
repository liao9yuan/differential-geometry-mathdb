import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedCapMatching

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem IsPLHomeomorphOn.cap_trace_of_spoke_ribbon
    {G : (ℝ × ℝ) × ℝ → E} {B P : Set E}
    (hG : IsPLHomeomorphOn G (spliceSquare ×ˢ _root_.Set.Icc (0 : ℝ) 1) B)
    (i : Fin 4) (a : ℝ) (ha : a ∈ _root_.Set.Icc (0 : ℝ) 1)
    (hstrip : G '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
      B ∩ P) :
    G '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({a} : Set ℝ)) =
      (G '' (spliceSquare ×ˢ ({a} : Set ℝ))) ∩ P := by
  have hsub := segment_fourSpokeModelLeaf_subset_spliceSquare i
  have hcap : G '' (spliceSquare ×ˢ ({a} : Set ℝ)) ⊆ B := by
    rintro _ ⟨x, hx, rfl⟩
    exact hG.bijOn.mapsTo ⟨hx.1, hx.2.symm ▸ ha⟩
  have hprod : segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({a} : Set ℝ) =
      (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩
        (spliceSquare ×ˢ ({a} : Set ℝ)) := by
    rw [_root_.Set.prod_inter_prod, inter_eq_left.mpr hsub,
      inter_eq_right.mpr (singleton_subset_iff.mpr ha)]
  rw [hprod, hG.bijOn.injOn.image_inter (_root_.Set.prod_mono hsub Subset.rfl)
    (_root_.Set.prod_mono Subset.rfl (singleton_subset_iff.mpr ha)), hstrip]
  ext x
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hcap h.1, h.2⟩, h.1⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.cap_trace_of_spoke_ribbon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.cap_trace_of_spoke_ribbon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.cap_trace_of_spoke_ribbon ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.cap_trace_of_spoke_ribbon

theorem splice_cap_arms_match_of_page_traces
    {G G' : (ℝ × ℝ) × ℝ → E} {B B' : Set E} {P : Fin 4 → Set E}
    (hG : IsPLHomeomorphOn G (spliceSquare ×ˢ _root_.Set.Icc (0 : ℝ) 1) B)
    (hG' : IsPLHomeomorphOn G' (spliceSquare ×ˢ _root_.Set.Icc (0 : ℝ) 1) B')
    (hcap : G '' (spliceSquare ×ˢ ({1} : Set ℝ)) = G' '' (spliceSquare ×ˢ ({0} : Set ℝ)))
    (hstrip : ∀ i,
      G '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ _root_.Set.Icc (0 : ℝ) 1) = B ∩ P i)
    (hstrip' : ∀ i,
      G' '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ _root_.Set.Icc (0 : ℝ) 1) = B' ∩ P i) :
    (∀ i, G '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({1} : Set ℝ)) =
      G' '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({0} : Set ℝ))) ∧
      ∀ i, G (fourSpokeModelLeaf i, 1) = G' (fourSpokeModelLeaf i, 0) := by
  have harmeq (i : Fin 4) :
      G '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({1} : Set ℝ)) =
        G' '' (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ×ˢ ({0} : Set ℝ)) := by
    rw [hG.cap_trace_of_spoke_ribbon i 1 (by norm_num) (hstrip i),
      hG'.cap_trace_of_spoke_ribbon i 0 (by norm_num) (hstrip' i), hcap]
  exact ⟨harmeq, splice_cap_leaf_eq_of_arm_eq hG hG' hcap harmeq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.splice_cap_arms_match_of_page_traces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.splice_cap_arms_match_of_page_traces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.splice_cap_arms_match_of_page_traces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.splice_cap_arms_match_of_page_traces

end DifferentialGeometry.Topology.PiecewiseLinear
