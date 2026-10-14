import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCoordinateAlignment
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamCorrectionShortening

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem ContinuousWithinAt.exists_symmetric_interval_mapsTo
    {A : Type*} [TopologicalSpace A] {γ : ℝ → A} {B N : Set A} {d : ℝ}
    (hd : 0 < d) (hγ : ContinuousWithinAt γ (_root_.Set.Icc (-d) d) 0)
    (hB : _root_.Set.MapsTo γ (_root_.Set.Icc (-d) d) B) (hN : N ∈ 𝓝[B] (γ 0)) :
    ∃ e : ℝ, 0 < e ∧ e ≤ d ∧ _root_.Set.MapsTo γ (_root_.Set.Icc (-e) e) N := by
  have hpre := (hγ.tendsto_nhdsWithin hB) hN
  rw [nhdsWithin_eq_nhds.mpr (Icc_mem_nhds (by linarith : -d < 0) hd)] at hpre
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨min d (r / 2), lt_min hd (by linarith), min_le_left _ _, ?_⟩
  intro t ht
  apply hrN
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  have he := min_le_right d (r / 2)
  constructor <;> linarith [ht.1, ht.2]

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.ContinuousWithinAt
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.ContinuousWithinAt.exists_symmetric_interval_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.ContinuousWithinAt.exists_symmetric_interval_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.ContinuousWithinAt.exists_symmetric_interval_mapsTo ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.ContinuousWithinAt.exists_symmetric_interval_mapsTo

theorem exists_short_seam_matching_after_uniform_circle_correction
    {A Q E : Type*} [TopologicalSpace A]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C : Set Q} {R W : Set E} {B N : Set A} {d : ℝ} (hd : 0 < d)
    {κ : Q × A → E} {γ : ℝ → A} {ρ : Q × ℝ → E} {H₀ H₁ : E → E} {ν : Q → Q}
    (hγ : ContinuousWithinAt γ (_root_.Set.Icc (-d) d) 0) (hB : _root_.Set.MapsTo γ (_root_.Set.Icc (-d) d) B)
    (hN : N ∈ 𝓝[B] (γ 0)) (hH₀ : IsPLHomeomorphOn H₀ R R)
    (hH₁ : IsPLHomeomorphOn H₁ R R) (hν : IsPLHomeomorphOn ν C C)
    (hρ : IsPLHomeomorphOn ρ (C ×ˢ _root_.Set.Icc (-d) d) W)
    (hmatch : ∀ z ∈ C, ∀ t ∈ _root_.Set.Icc (-d) d, H₀ (κ (z, γ t)) = ρ (z, t))
    (hact : ∀ z ∈ C, ∀ p ∈ N, H₁ (H₀ (κ (z, p))) = H₀ (κ (ν z, p))) :
    ∃ e : ℝ, 0 < e ∧ e ≤ d ∧ IsPLHomeomorphOn (H₁ ∘ H₀) R R ∧
      IsPLHomeomorphOn (ρ ∘ Prod.map ν id) (C ×ˢ _root_.Set.Icc (-d) d) W ∧
      (∀ z ∈ C, ∀ t ∈ _root_.Set.Icc (-e) e, (H₁ ∘ H₀) (κ (z, γ t)) = ρ (ν z, t)) ∧
      ∀ T : Set ℝ, (ρ ∘ Prod.map ν id) '' (C ×ˢ T) = ρ '' (C ×ˢ T) := by
  obtain ⟨e, he, hed, heN⟩ :=
    ContinuousWithinAt.exists_symmetric_interval_mapsTo hd hγ hB hN
  refine ⟨e, he, hed, hH₀.trans hH₁,
    (hν.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id).trans hρ, ?_, ?_⟩
  · intro z hz t ht
    exact (hact z hz (γ t) (heN ht)).trans
      (hmatch (ν z) (hν.bijOn.mapsTo hz) t
        (_root_.Set.Icc_subset_Icc (neg_le_neg hed) hed ht))
  · intro T
    rw [_root_.Set.image_comp, _root_.Set.prodMap_image_prod, hν.image_eq, _root_.Set.image_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_short_seam_matching_after_uniform_circle_correction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_short_seam_matching_after_uniform_circle_correction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_short_seam_matching_after_uniform_circle_correction ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_short_seam_matching_after_uniform_circle_correction

end DifferentialGeometry.Topology.PiecewiseLinear
