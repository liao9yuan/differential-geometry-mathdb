import Submission.DifferentialGeometry.Topology.DenseEmbedding
import Submission.DifferentialGeometry.Topology.Compactness.ConvergentSeparators
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.Completion
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.RadialDistance
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckCurvatureDistance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Toponogov

variable {M : Type*} [MetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [SigmaCompactSpace M]
  (g : SmoothRiemannianMetric I3 M)
  (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
  (hsec : HasNonnegativeSectionalCurvature g)
  {q : UniformSpace.Completion M} (hq : q ∉ range (fun x : M => (x : UniformSpace.Completion M)))
  {r : ℝ} (hr : 0 < r) (hcompact : IsCompact (Metric.closedBall q r))
  (hcover : Metric.closedBall q r ⊆ insert q (range (fun x : M => (x : UniformSpace.Completion M))))
  (havoid : ∀ (beta : ℝ → UniformSpace.Completion M) (u v w : ℝ), u < v → v < w →
    (∀ s ∈ Icc u w, ∀ t ∈ Icc u w, dist (beta s) (beta t) = |s - t|) → beta v ≠ q)

include hmetric hsec hq hr hcompact hcover havoid in
private theorem exists_separated_radial_segments
    {eps : ℝ} {x : M} (nk : SpatialNeck g eps x)
    (hnear : ∀ y ∈ nk.map '' (_root_.Set.univ ×ˢ {(0 : ℝ)}), _root_.Dist.dist (y : UniformSpace.Completion M) q < r / 3) :
    ∃ L : ℝ, 0 < L ∧ L < r / 3 ∧ ∃ gamma mu : C(ℝ, UniformSpace.Completion M),
      gamma 0 = q ∧ mu 0 = q ∧
      (∀ s ∈ _root_.Set.Icc 0 L, ∀ t ∈ _root_.Set.Icc 0 L, _root_.Dist.dist (gamma s) (gamma t) = |s - t|) ∧
      (∀ s ∈ _root_.Set.Icc 0 L, ∀ t ∈ _root_.Set.Icc 0 L, _root_.Dist.dist (mu s) (mu t) = |s - t|) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ s ∈ _root_.Set.Ioc 0 L, ∀ t ∈ _root_.Set.Ioc 0 L,
        min s t * c ≤ _root_.Dist.dist (gamma s) (mu t) := by
  obtain ⟨y, z, hy, hz, hyz, heq⟩ := nk.exists_distinct_central_sphere_points_same_radius q
  have hLy : 0 < _root_.Dist.dist (y : UniformSpace.Completion M) q := dist_pos.mpr (fun h => hq ⟨y, h⟩)
  obtain ⟨gamma, hg0, hgL, hgd⟩ := exists_radial_segment_of_punctured_compact_ball
    g hmetric hcompact hcover y (by linarith only [hnear y hy, hr])
  obtain ⟨mu, hm0, hmL, hmd⟩ := exists_radial_segment_of_punctured_compact_ball
    g hmetric hcompact hcover z (by linarith only [hnear z hz, hr])
  rw [← heq] at hmL hmd
  let L := _root_.Dist.dist (y : UniformSpace.Completion M) q
  let paths : Bool → ℝ → UniformSpace.Completion M := fun b => if b then gamma else mu
  have hp0 (b : Bool) : paths b 0 = q := by cases b <;> assumption
  have hpd (b : Bool) : ∀ s ∈ _root_.Set.Icc 0 L, ∀ t ∈ _root_.Set.Icc 0 L,
      dist (paths b s) (paths b t) = |s - t| := by
    cases b
    · exact hmd
    · exact hgd
  have hmono := radialComparisonAngle_nonincreasing_of_completion_segments g hmetric hsec
    hq hcompact hcover havoid (L := fun _ : Bool => L)
    (fun _ => hLy) (fun _ => hnear y hy) hp0 hpd _root_.Bool.true _root_.Bool.false
  have hrad : IsRadialFamily q (fun _ : Bool => L) paths := by
    intro b s hs
    simpa only [hp0, sub_zero, abs_of_pos hs.1, dist_comm q] using
      hpd b s ⟨hs.1.le, hs.2⟩ 0 ⟨le_rfl, hLy.le⟩
  have hsep : 0 < _root_.Dist.dist (gamma L) (mu L) := by
    rw [hgL, hmL, UniformSpace.Completion.dist_eq]
    exact dist_pos.mpr hyz
  refine ⟨L, hLy, hnear y hy, gamma, mu, hg0, hm0, hgd, hmd,
    _root_.Dist.dist (gamma L) (mu L) / L, div_pos hsep hLy, ?_⟩
  intro s hs t ht
  exact min_mul_dist_div_le_dist_of_radialComparisonAngle_nonincreasing hLy hrad hmono hs ht

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_separated_radial_segments
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_separated_radial_segments target :: scope.openDecls } }


private theorem radius_div_scale_le_of_two_points
    {r h D c s t d : ℝ} (hh : 0 < h) (hc : 0 < c)
    (hs : r - D * h ≤ s) (ht : r - D * h ≤ t)
    (hd : d ≤ 2 * D * h) (hsep : _root_.Min.min s t * c ≤ d) :
    r / h ≤ D + 2 * D / c := by
  have hmin : r - D * h ≤ _root_.Min.min s t := le_min hs ht
  have hbound := (mul_le_mul_of_nonneg_right hmin hc.le).trans (hsep.trans hd)
  apply (div_le_iff₀ hh).mpr
  apply (mul_le_mul_iff_left₀ hc).mp
  field_simp at *
  nlinarith only [hbound]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.radius_div_scale_le_of_two_points
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.radius_div_scale_le_of_two_points target :: scope.openDecls } }

include hmetric hsec hq hr hcompact hcover havoid in
theorem exists_scalar_distance_upper_bound_of_convergent_neck_separators
    {A : ℕ → Set M} (hA : ∀ n, IsCompact (A n))
    (hlim : ∀ U ∈ 𝓝 q, ∀ᶠ n in _root_.Filter.atTop,
      (fun x : M => (x : UniformSpace.Completion M)) '' A n ⊆ U)
    (hnhds : _root_.Insert.insert q (⋃ n, (fun x : M => (x : UniformSpace.Completion M)) '' A n) ∈ 𝓝 q)
    {eps : ℝ} {x : ℕ → M}
    (hnecks : ∀ᶠ N in _root_.Filter.atTop, ∃ nk : SpatialNeck g eps (x N),
      frontier (⋃ n, A (n + N)) ⊆ nk.map '' (_root_.Set.univ ×ˢ {(0 : ℝ)}))
    (hx : _root_.Filter.Tendsto (fun n => (x n : UniformSpace.Completion M)) _root_.Filter.atTop (𝓝 q))
    (hscalar : _root_.Filter.Tendsto (fun n => metricScalarAt g (x n)) _root_.Filter.atTop _root_.Filter.atTop) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in _root_.Filter.atTop,
      metricScalarAt g (x n) * _root_.Dist.dist q (x n : UniformSpace.Completion M) ^ 2 ≤ C := by
  have hball {n : ℕ} (nk : SpatialNeck g eps (x n)) {y : M}
      (hy : y ∈ nk.map '' (_root_.Set.univ ×ˢ {(0 : ℝ)})) :
      _root_.Dist.dist (y : UniformSpace.Completion M) (x n : UniformSpace.Completion M) ≤
        7 / Real.sqrt (metricScalarAt g (x n)) := by
    have hb := nk.central_sphere_subset_closedBall hy
    change riemannianEDistOf g (x n) y ≤ ENNReal.ofReal _ at hb
    rw [← hmetric, edist_dist] at hb
    rw [UniformSpace.Completion.dist_eq, dist_comm]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
  have hradius : _root_.Filter.Tendsto (fun n => 7 / Real.sqrt (metricScalarAt g (x n))) _root_.Filter.atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hscalar)
  have hsmall : _root_.Filter.Tendsto (fun n => _root_.Dist.dist (x n : UniformSpace.Completion M) q +
      7 / Real.sqrt (metricScalarAt g (x n))) _root_.Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_add] using (tendsto_iff_dist_tendsto_zero.mp hx).add hradius
  obtain ⟨N, ⟨nk, _⟩, hN⟩ := (hnecks.and
    (hsmall.eventually (eventually_lt_nhds (by linarith only [hr] : (0 : ℝ) < r / 3)))).exists
  obtain ⟨L, hL, _, gamma, mu, hg0, hm0, hgd, hmd, c, hc, hsep⟩ :=
    exists_separated_radial_segments g hmetric hsec hq hr hcompact hcover havoid nk (by
      intro y hy
      have ht := dist_triangle (y : UniformSpace.Completion M) (x N : UniformSpace.Completion M) q
      linarith only [ht, hball nk hy, hN])
  have hradg (s : ℝ) (hs : s ∈ _root_.Set.Ioc 0 L) : _root_.Dist.dist (gamma s) q = s := by
    simpa only [hg0, sub_zero, abs_of_pos hs.1] using hgd s ⟨hs.1.le, hs.2⟩ 0 ⟨le_rfl, hL.le⟩
  have hradm (s : ℝ) (hs : s ∈ _root_.Set.Ioc 0 L) : _root_.Dist.dist (mu s) q = s := by
    simpa only [hm0, sub_zero, abs_of_pos hs.1] using hmd s ⟨hs.1.le, hs.2⟩ 0 ⟨le_rfl, hL.le⟩
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ThreeSpace M
  have he : _root_.Topology.IsOpenEmbedding (fun x : M => (x : UniformSpace.Completion M)) :=
    UniformSpace.Completion.isDenseEmbedding_coe.isOpenEmbedding
  have hgend : gamma L ≠ q := dist_pos.mp (by rw [hradg L ⟨hL, le_rfl⟩]; exact hL)
  have hmend : mu L ≠ q := dist_pos.mp (by rw [hradm L ⟨hL, le_rfl⟩]; exact hL)
  have hcrossg := DifferentialGeometry.Topology.eventually_exists_frontier_intersection_of_convergent_separators
    he hq hA hlim hnhds hL gamma.continuous.continuousOn hg0 hgend
  have hcrossm := DifferentialGeometry.Topology.eventually_exists_frontier_intersection_of_convergent_separators
    he hq hA hlim hnhds hL mu.continuous.continuousOn hm0 hmend
  refine ⟨(7 + 14 / c) ^ 2, by positivity, ?_⟩
  filter_upwards [hnecks, hcrossg, hcrossm] with n hn hng hnm
  obtain ⟨nk, hfront⟩ := hn
  obtain ⟨s, hs, y, hy, hgy⟩ := hng
  obtain ⟨t, ht, z, hz, hmz⟩ := hnm
  have hyb := hball nk (hfront hy)
  have hzb := hball nk (hfront hz)
  rw [← hgy] at hyb
  rw [← hmz] at hzb
  have hsbound : _root_.Dist.dist q (x n : UniformSpace.Completion M) -
      7 * (1 / Real.sqrt (metricScalarAt g (x n))) ≤ s := by
    have hh := dist_triangle (x n : UniformSpace.Completion M) (gamma s) q
    rw [dist_comm (x n : UniformSpace.Completion M) (gamma s), dist_comm (x n : UniformSpace.Completion M) q,
      hradg s hs] at hh
    simp only [div_eq_mul_inv, one_mul] at hyb ⊢
    linarith only [hh, hyb]
  have htbound : _root_.Dist.dist q (x n : UniformSpace.Completion M) -
      7 * (1 / Real.sqrt (metricScalarAt g (x n))) ≤ t := by
    have hh := dist_triangle (x n : UniformSpace.Completion M) (mu t) q
    rw [dist_comm (x n : UniformSpace.Completion M) (mu t), dist_comm (x n : UniformSpace.Completion M) q,
      hradm t ht] at hh
    simp only [div_eq_mul_inv, one_mul] at hzb ⊢
    linarith only [hh, hzb]
  have hdist : _root_.Dist.dist (gamma s) (mu t) ≤ 2 * 7 * (1 / Real.sqrt (metricScalarAt g (x n))) := by
    have hh := dist_triangle (gamma s) (x n : UniformSpace.Completion M) (mu t)
    rw [dist_comm (x n : UniformSpace.Completion M) (mu t)] at hh
    simp only [div_eq_mul_inv, one_mul] at hyb hzb ⊢
    linarith only [hh, hyb, hzb]
  have hQ : 0 < Real.sqrt (metricScalarAt g (x n)) := Real.sqrt_pos.mpr nk.Q_pos
  have hbound := radius_div_scale_le_of_two_points (one_div_pos.mpr hQ) hc
    hsbound htbound hdist (hsep s hs t ht)
  simp only [one_div, div_inv_eq_mul] at hbound
  have hsq := pow_le_pow_left₀ (mul_nonneg dist_nonneg hQ.le) hbound 2
  rw [mul_pow, Real.sq_sqrt nk.Q_pos.le] at hsq
  nlinarith only [hsq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_scalar_distance_upper_bound_of_convergent_neck_separators then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_scalar_distance_upper_bound_of_convergent_neck_separators"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_scalar_distance_upper_bound_of_convergent_neck_separators ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_scalar_distance_upper_bound_of_convergent_neck_separators

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
