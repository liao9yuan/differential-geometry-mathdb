import Submission.DifferentialGeometry.Analysis.ODE.Flow.Planar.PlanarFlowBox
import Submission.DifferentialGeometry.Topology.Flow.TransverseReturns

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Filter
open scoped _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis

theorem exists_transverse_returns_of_frequent_visits
    (φ : _root_.Flow ℝ ℂ) {v : ℂ → ℂ} (hv : ContDiff ℝ ∞ v)
    (hderiv : ∀ x t, HasDerivAt (fun s ↦ φ s x) (v (φ t x)) t)
    {K : Set ℂ} (hK : IsCompact K) (hnz : ∀ x ∈ K, v x ≠ 0)
    {z : ℂ} (hfreq : ∃ᶠ t in _root_.Filter.atTop, φ t z ∈ K) :
    ∃ x ∈ K, ∃ ε > 0, ∃ e : OpenPartialHomeomorph (ℝ × ℝ) ℂ,
      e.source = _root_.Set.Ioo (-ε) ε ×ˢ _root_.Set.Ioo (-ε) ε ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ p, e p = φ p.2 (x + p.1 • (Complex.I * v x))) ∧
      ∀ T : ℝ, ∃ t ≥ T, ∃ u ∈ _root_.Set.Ioo (-ε) ε,
        φ t z = x + u • (Complex.I * v x) := by
  obtain ⟨x, hx, hcluster⟩ := hK.exists_mapClusterPt_of_frequently hfreq
  obtain ⟨ε, hε, e, hsource, he, heinv, heq⟩ :=
    exists_smooth_planar_flowBox φ hv hderiv (hnz x hx)
  have hzero : e (0, 0) = x := by
    rw [heq]
    simp only [zero_smul, add_zero, φ.map_zero_apply]
  have hxTarget : x ∈ e.target := hzero ▸ e.map_source (by
    rw [hsource]
    exact ⟨⟨neg_neg_of_pos hε, hε⟩, ⟨neg_neg_of_pos hε, hε⟩⟩)
  have hvisits : ∀ T : ℝ, ∃ t ≥ T, φ t z ∈ e.target :=
    frequently_atTop.mp (mapClusterPt_iff_frequently.mp hcluster e.target
      (e.open_target.mem_nhds hxTarget))
  exact ⟨x, hx, ε, hε, e, hsource, he, heinv, heq,
    DifferentialGeometry.Topology.Flow.exists_transverse_hit_after φ e hsource heq hvisits⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_transverse_returns_of_frequent_visits then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_transverse_returns_of_frequent_visits"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_transverse_returns_of_frequent_visits ``Submission.DifferentialGeometry.Analysis.exists_transverse_returns_of_frequent_visits

theorem exists_transverse_returns_of_trapped_orbit
    (φ : _root_.Flow ℝ ℂ) {v : ℂ → ℂ} (hv : ContDiff ℝ ∞ v)
    (hderiv : ∀ x t, HasDerivAt (fun s ↦ φ s x) (v (φ t x)) t)
    {K : Set ℂ} (hK : IsCompact K) (hnz : ∀ x ∈ K, v x ≠ 0)
    {z : ℂ} (hstay : ∀ t ≥ 0, φ t z ∈ K) :
    ∃ x ∈ K, ∃ ε > 0, ∃ e : OpenPartialHomeomorph (ℝ × ℝ) ℂ,
      e.source = _root_.Set.Ioo (-ε) ε ×ˢ _root_.Set.Ioo (-ε) ε ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ p, e p = φ p.2 (x + p.1 • (Complex.I * v x))) ∧
      ∀ T : ℝ, ∃ t ≥ T, ∃ u ∈ _root_.Set.Ioo (-ε) ε,
        φ t z = x + u • (Complex.I * v x) := by
  exact exists_transverse_returns_of_frequent_visits φ hv hderiv hK hnz
    (((_root_.Filter.eventually_ge_atTop (0 : ℝ)).mono (fun t ht ↦ hstay t ht)).frequently)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_transverse_returns_of_trapped_orbit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_transverse_returns_of_trapped_orbit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_transverse_returns_of_trapped_orbit ``Submission.DifferentialGeometry.Analysis.exists_transverse_returns_of_trapped_orbit

end DifferentialGeometry.Analysis
