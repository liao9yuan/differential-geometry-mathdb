import Mathlib.Topology.MetricSpace.Sequences

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open _root_.Filter _root_.Metric _root_.Set
open scoped _root_.Topology

open _root_.DenseRange in
theorem DenseRange.tendsto_of_tendsto_dist
    {A I X : Type*} [PseudoMetricSpace X] {a : I → X} (ha : DenseRange a)
    {l : Filter A} {u : A → X} {x : X}
    (hu : ∀ i, _root_.Filter.Tendsto (fun n => _root_.Dist.dist (u n) (a i)) l (𝓝 (_root_.Dist.dist x (a i)))) :
    Tendsto u l (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨i, hi⟩ := ha.exists_dist_lt x (half_pos hε)
  have hnear : ∀ᶠ n in l, _root_.Dist.dist (u n) (a i) < ε - _root_.Dist.dist x (a i) :=
    (hu i).eventually (Iio_mem_nhds (by linarith : dist x (a i) < ε - dist x (a i)))
  filter_upwards [hnear] with n hn
  exact (dist_triangle_right (u n) x (a i)).trans_lt (by linarith)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DenseRange
  let env ← Lean.getEnv
  if env.contains `DenseRange.tendsto_of_tendsto_dist then
    throwError "Refusing to shadow existing declaration DenseRange.tendsto_of_tendsto_dist"
  Lean.modifyEnv fun env => Lean.addAlias env `DenseRange.tendsto_of_tendsto_dist ``Submission.DenseRange.tendsto_of_tendsto_dist

open _root_.DenseRange in
theorem DenseRange.exists_tendsto_of_tendsto_dist
    {I X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    {a : I → X} (ha : DenseRange a) {u : ℕ → X}
    (hu : ∀ i, ∃ r : ℝ, _root_.Filter.Tendsto (fun n => _root_.Dist.dist (u n) (a i)) _root_.Filter.atTop (𝓝 r)) :
    ∃ x : X, _root_.Filter.Tendsto u _root_.Filter.atTop (𝓝 x) := by
  obtain ⟨i, _⟩ := ha.exists_dist_lt (u 0) zero_lt_one
  obtain ⟨r, hr⟩ := hu i
  have hbounded : ∀ᶠ n in _root_.Filter.atTop, u n ∈ _root_.Metric.closedBall (a i) (r + 1) := by
    have hlt : ∀ᶠ n in _root_.Filter.atTop, _root_.Dist.dist (u n) (a i) < r + 1 :=
      hr.eventually (Iio_mem_nhds (lt_add_one r))
    filter_upwards [hlt] with n hn
    exact hn.le
  obtain ⟨x, _, φ, hφ, hx⟩ :=
    (_root_.ProperSpace.isCompact_closedBall (a i) (r + 1)).tendsto_subseq' hbounded.frequently
  refine ⟨x, ha.tendsto_of_tendsto_dist ?_⟩
  intro j
  obtain ⟨s, hs⟩ := hu j
  have hsub : _root_.Filter.Tendsto (fun n => _root_.Dist.dist (u (φ n)) (a j)) _root_.Filter.atTop (𝓝 (_root_.Dist.dist x (a j))) :=
    hx.dist tendsto_const_nhds
  have heq : s = _root_.Dist.dist x (a j) := tendsto_nhds_unique (hs.comp hφ.tendsto_atTop) hsub
  rwa [heq] at hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DenseRange.exists_tendsto_of_tendsto_dist then
    throwError "Refusing to shadow existing declaration DenseRange.exists_tendsto_of_tendsto_dist"
  Lean.modifyEnv fun env => Lean.addAlias env `DenseRange.exists_tendsto_of_tendsto_dist ``Submission.DenseRange.exists_tendsto_of_tendsto_dist

end
