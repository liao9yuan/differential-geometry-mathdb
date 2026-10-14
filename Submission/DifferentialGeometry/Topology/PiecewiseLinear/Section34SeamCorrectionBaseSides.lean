import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCorrectionPlacement

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem inter_initial_arcs_of_common_ends
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ ε : ℝ → E} {A B : Set E}
    (hδ : IsPLHomeomorphOn δ (_root_.Set.Icc 0 1) A) (hε : IsPLHomeomorphOn ε (_root_.Set.Icc 0 1) B)
    (hεzero : ε 0 = δ 0) (hεone : ε 1 = δ 1) (hAB : A ∩ B = {δ 0, δ 1}) :
    (ε '' _root_.Set.Icc (0 : ℝ) (1 / 4) ∪ δ '' _root_.Set.Icc (0 : ℝ) (1 / 4)) ∩ A =
      δ '' _root_.Set.Icc (0 : ℝ) (1 / 4) ∧
    (ε '' _root_.Set.Icc (0 : ℝ) (1 / 4) ∪ δ '' _root_.Set.Icc (0 : ℝ) (1 / 4)) ∩ B =
      ε '' _root_.Set.Icc (0 : ℝ) (1 / 4) ∧
    Disjoint (δ '' _root_.Set.Icc (1 / 2 : ℝ) (3 / 4)) B := by
  have hs : _root_.Set.Icc (0 : ℝ) (1 / 4) ⊆ _root_.Set.Icc (0 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hz : (0 : ℝ) ∈ _root_.Set.Icc 0 (1 / 4) := by norm_num
  have ho : (1 : ℝ) ∈ _root_.Set.Icc 0 1 := by norm_num
  have hzI : (0 : ℝ) ∈ _root_.Set.Icc 0 1 := by norm_num
  have hδs := (_root_.Set.image_mono hs).trans hδ.image_eq.subset
  have hεs := (_root_.Set.image_mono hs).trans hε.image_eq.subset
  refine ⟨Subset.antisymm ?_ (fun x hx => ⟨Or.inr hx, hδs hx⟩),
    Subset.antisymm ?_ (fun x hx => ⟨Or.inl hx, hεs hx⟩), ?_⟩
  · rintro x ⟨hx | hx, hxA⟩
    · have he := hAB.subset ⟨hxA, hεs hx⟩
      rcases he with he | he
      · exact he.symm ▸ _root_.Set.mem_image_of_mem δ hz
      · obtain ⟨t, ht, htε⟩ := hx
        have hti := hε.bijOn.injOn (hs ht) ho (htε.trans (he.trans hεone.symm))
        linarith [ht.2]
    · exact hx
  · rintro x ⟨hx | hx, hxB⟩
    · exact hx
    · have he := hAB.subset ⟨hδs hx, hxB⟩
      rcases he with he | he
      · exact (he.trans hεzero.symm).symm ▸ _root_.Set.mem_image_of_mem ε hz
      · obtain ⟨t, ht, htδ⟩ := hx
        have hti := hδ.bijOn.injOn (hs ht) ho (htδ.trans he)
        linarith [ht.2]
  · apply disjoint_left.mpr
    rintro x ⟨t, ht, rfl⟩ hxB
    have htI : t ∈ _root_.Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    have he := hAB.subset ⟨hδ.bijOn.mapsTo htI, hxB⟩
    rcases he with he | he
    · have hti := hδ.bijOn.injOn htI hzI he
      linarith [ht.1]
    · have hti := hδ.bijOn.injOn htI ho he
      linarith [ht.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.inter_initial_arcs_of_common_ends then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.inter_initial_arcs_of_common_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.inter_initial_arcs_of_common_ends ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.inter_initial_arcs_of_common_ends

end DifferentialGeometry.Topology.PiecewiseLinear
