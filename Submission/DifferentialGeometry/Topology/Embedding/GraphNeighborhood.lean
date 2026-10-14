import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace Topology.IsInducing
open _root_.Topology _root_.Topology.IsInducing

open _root_.Topology _root_.Topology.IsInducing in
theorem exists_isOpen_inter_range_eq_graph
    {E F M : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace M]
    {e : M → E × F} (he : _root_.Topology.IsInducing e) (χ : OpenPartialHomeomorph E M)
    {s : Set E} (hs : IsOpen s) (hsource : s ⊆ χ.source)
    {q : E → F} (hgraph : ∀ y ∈ s, e (χ y) = (y, q y)) :
    ∃ U : Set (E × F), IsOpen U ∧ (fun y => (y, q y)) '' s ⊆ U ∧ U ⊆ s ×ˢ _root_.Set.univ ∧
      U ∩ _root_.Set.range e = U ∩ {z | z.2 = q z.1} := by
  obtain ⟨V, hV, hpre⟩ := he.isOpen_iff.mp (χ.isOpen_image_of_subset_source hs hsource)
  refine ⟨V ∩ s ×ˢ _root_.Set.univ, hV.inter (hs.prod isOpen_univ), ?_, _root_.Set.inter_subset_right, ?_⟩
  · rintro z ⟨a, ha, rfl⟩
    refine ⟨?_, ha, _root_.Set.mem_univ _⟩
    change (a, q a) ∈ V
    rw [← hgraph a ha]
    change χ a ∈ e ⁻¹' V
    rw [hpre]
    exact _root_.Set.mem_image_of_mem χ ha
  · ext z
    constructor
    · rintro ⟨hz, x, hx⟩
      have hxV : x ∈ e ⁻¹' V := by
        change e x ∈ V
        rw [hx]
        exact hz.1
      rw [hpre] at hxV
      obtain ⟨y, hy, hxy⟩ := hxV
      have heq : (y, q y) = z := (hgraph y hy).symm.trans (hxy ▸ hx)
      exact ⟨hz, heq ▸ rfl⟩
    · rintro ⟨hz, hq⟩
      refine ⟨hz, χ z.1, ?_⟩
      exact (hgraph z.1 hz.2.1).trans (Prod.ext rfl hq.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Topology.IsInducing.exists_isOpen_inter_range_eq_graph then
    throwError "Refusing to shadow existing declaration Topology.IsInducing.exists_isOpen_inter_range_eq_graph"
  Lean.modifyEnv fun env => Lean.addAlias env `Topology.IsInducing.exists_isOpen_inter_range_eq_graph ``Submission.Topology.IsInducing.exists_isOpen_inter_range_eq_graph

open _root_.Metric

open _root_.Topology _root_.Topology.IsInducing in
theorem exists_prod_closedBall_inter_range_eq_graph
    {E F M : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F] [TopologicalSpace M]
    {e : M → E × F} (he : _root_.Topology.IsInducing e) (χ : OpenPartialHomeomorph E M)
    {s : Set E} (hs : IsOpen s) (hsource : s ⊆ χ.source)
    {q : E → F} (hgraph : ∀ y ∈ s, e (χ y) = (y, q y)) {a : E} (ha : a ∈ s)
    (hq : ContinuousAt q a) :
    ∃ r : ℝ, 0 < r ∧ ∃ t : ℝ, 0 < t ∧ _root_.Metric.closedBall a r ⊆ s ∧
      (∀ y ∈ _root_.Metric.closedBall a r, q y ∈ _root_.Metric.ball (q a) t) ∧
      (_root_.Metric.closedBall a r ×ˢ _root_.Metric.closedBall (q a) t) ∩ _root_.Set.range e =
        (fun y => (y, q y)) '' _root_.Metric.closedBall a r := by
  obtain ⟨U, hU, hgraphU, hUs, hUr⟩ :=
    he.exists_isOpen_inter_range_eq_graph χ hs hsource hgraph
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp
    (hU.mem_nhds (hgraphU (_root_.Set.mem_image_of_mem _ ha)))
  obtain ⟨δ, hδ, hδq⟩ := Metric.mem_nhds_iff.mp
    (hq.preimage_mem_nhds (_root_.Metric.ball_mem_nhds (q a) (half_pos hR)))
  let r := _root_.Min.min (R / 2) (δ / 2)
  have hr : 0 < r := lt_min (half_pos hR) (half_pos hδ)
  have hrR : r < R := (min_le_left _ _).trans_lt (by linarith)
  have hrδ : r < δ := (min_le_right _ _).trans_lt (by linarith)
  have hprod : _root_.Metric.closedBall a r ×ˢ _root_.Metric.closedBall (q a) (R / 2) ⊆ U := by
    intro z hz
    apply hRU
    rw [_root_.Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_closedBall.mp hz.1).trans_lt hrR,
      (mem_closedBall.mp hz.2).trans_lt (by linarith)⟩
  have hrs : _root_.Metric.closedBall a r ⊆ s := by
    intro y hy
    exact (hUs (hprod (show (y, q a) ∈ _root_.Metric.closedBall a r ×ˢ _root_.Metric.closedBall (q a) (R / 2) from
      ⟨hy, _root_.Metric.mem_closedBall_self (half_pos hR).le⟩))).1
  have hrq : ∀ y ∈ _root_.Metric.closedBall a r, q y ∈ _root_.Metric.ball (q a) (R / 2) := by
    intro y hy
    exact hδq (_root_.Metric.closedBall_subset_ball hrδ hy)
  refine ⟨r, hr, R / 2, half_pos hR, hrs, hrq, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hze⟩
    have hzq : z.2 = q z.1 := by
      have h : z ∈ U ∩ _root_.Set.range e := ⟨hprod hz, hze⟩
      rw [hUr] at h
      exact h.2
    exact ⟨z.1, hz.1, Prod.ext rfl hzq.symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨hy, _root_.Metric.ball_subset_closedBall (hrq y hy)⟩, χ y, hgraph y (hrs hy)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Topology.IsInducing.exists_prod_closedBall_inter_range_eq_graph then
    throwError "Refusing to shadow existing declaration Topology.IsInducing.exists_prod_closedBall_inter_range_eq_graph"
  Lean.modifyEnv fun env => Lean.addAlias env `Topology.IsInducing.exists_prod_closedBall_inter_range_eq_graph ``Submission.Topology.IsInducing.exists_prod_closedBall_inter_range_eq_graph

end Topology.IsInducing
