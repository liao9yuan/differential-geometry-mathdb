import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.LimitingRadialAngleKernel
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.Completion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckPacking
import Submission.DifferentialGeometry.Topology.Compactness.ConvergentSeparators
import Submission.DifferentialGeometry.Topology.DenseEmbedding
import Submission.DifferentialGeometry.Topology.MetricSpace.TotallyBounded

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal
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
  {r : ℝ} (hcompact : IsCompact (Metric.closedBall q r))
  (hcover : Metric.closedBall q r ⊆ insert q (range (fun x : M => (x : UniformSpace.Completion M))))
  (havoid : ∀ (beta : ℝ → UniformSpace.Completion M) (u v w : ℝ), u < v → v < w →
    (∀ s ∈ Icc u w, ∀ t ∈ Icc u w, dist (beta s) (beta t) = |s - t|) → beta v ≠ q)

include hmetric hsec hq hcompact hcover havoid in
theorem exists_card_bound_of_separated_radial_segments
    {A : ℕ → Set M} (hA : ∀ n, IsCompact (A n))
    (hlim : ∀ U ∈ 𝓝 q, ∀ᶠ n in _root_.Filter.atTop,
      (fun x : M => (x : UniformSpace.Completion M)) '' A n ⊆ U)
    (hnhds : _root_.Insert.insert q (⋃ n, (fun x : M => (x : UniformSpace.Completion M)) '' A n) ∈ 𝓝 q)
    {eps : ℝ} {x : ℕ → M}
    (hnecks : ∀ᶠ N in _root_.Filter.atTop, ∃ nk : SpatialNeck g eps (x N),
      frontier (⋃ n, A (n + N)) ⊆ nk.map '' (_root_.Set.univ ×ˢ {(0 : ℝ)}))
    (hx : _root_.Filter.Tendsto (fun n => (x n : UniformSpace.Completion M)) _root_.Filter.atTop (𝓝 q))
    (hscalar : _root_.Filter.Tendsto (fun n => metricScalarAt g (x n)) _root_.Filter.atTop _root_.Filter.atTop)
    (hquant : ∀ᶠ n in _root_.Filter.atTop, 196 < metricScalarAt g (x n) * _root_.Dist.dist q (x n : UniformSpace.Completion M) ^ 2)
    {delta : ℝ} (hdelta : 0 < delta) (hdeltapi : delta ≤ Real.pi) :
    ∃ N : ℕ, ∀ {ι : Type*} [Finite ι] (L : ι → ℝ) (gamma : ι → C(ℝ, UniformSpace.Completion M)),
      (∀ i, 0 < L i) → (∀ i, L i < r / 3) → (∀ i, gamma i 0 = q) →
      (∀ i, ∀ s ∈ _root_.Set.Icc 0 (L i), ∀ t ∈ _root_.Set.Icc 0 (L i), _root_.Dist.dist (gamma i s) (gamma i t) = |s - t|) →
      (Pairwise fun i j => delta ≤ limitingRadialAngle L (fun i => gamma i) i j) → Nat.card ι ≤ N := by
  classical
  have hsin : 0 < Real.sin (delta / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  obtain ⟨N, hpack⟩ := exists_uniform_central_sphere_packing_bound
    (show 0 < 14 * Real.sin (delta / 4) by positivity)
  refine ⟨N, fun {ι} _ L gamma hL hLr hzero hdist hsep => ?_⟩
  let _ : Fintype ι := Fintype.ofFinite ι
  have hrad : IsRadialFamily q L (fun i => gamma i) := by
    intro i s hs
    simpa only [hzero, sub_zero, abs_of_pos hs.1, dist_comm q] using
      hdist i s ⟨hs.1.le, hs.2⟩ 0 ⟨le_rfl, (hL i).le⟩
  have hmono (i j : ι) := radialComparisonAngle_nonincreasing_of_completion_segments
    g hmetric hsec hq hcompact hcover havoid hL hLr hzero hdist i j
  let rho (n : ℕ) := _root_.Dist.dist (x n : UniformSpace.Completion M) q + 7 / Real.sqrt (metricScalarAt g (x n))
  have hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [rho, Function.comp_apply, zero_add] using (tendsto_iff_dist_tendsto_zero.mp hx).add
      ((tendsto_const_nhds (x := (7 : ℝ))).div_atTop (Real.tendsto_sqrt_atTop.comp hscalar))
  have hcmp (i j : ι) : ∀ᶠ n in _root_.Filter.atTop, i ≠ j →
      ∀ s ∈ _root_.Set.Ioc 0 (L i), ∀ t ∈ _root_.Set.Ioc 0 (L j), s ≤ rho n → t ≤ rho n →
        delta / 2 < radialComparisonAngle (fun i => gamma i) i j s t := by
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => False.elim (h hij)
    have hlt : delta / 2 < limitingRadialAngle L (fun i => gamma i) i j :=
      (half_lt_self hdelta).trans_le (hsep hij)
    obtain ⟨v, hv, hvgt⟩ := exists_lt_of_lt_csSup
      (positiveRectangleValues_radial_nonempty (fun i => gamma i) (hL i) (hL j)) hlt
    obtain ⟨s0, hs0, t0, ht0, rfl⟩ := hv
    filter_upwards [hrho.eventually (eventually_lt_nhds (lt_min hs0.1 ht0.1))] with n hn
    intro _ s hs t ht hsn htn
    have hss : s ≤ s0 := hsn.trans (hn.le.trans (min_le_left _ _))
    have htt : t ≤ t0 := htn.trans (hn.le.trans (min_le_right _ _))
    exact hvgt.trans_le (((hmono i j).1 hs hs0 ht0 hss).trans ((hmono i j).2 hs ht ht0 htt))
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ThreeSpace M
  have he : _root_.Topology.IsOpenEmbedding (fun x : M => (x : UniformSpace.Completion M)) :=
    UniformSpace.Completion.isDenseEmbedding_coe.isOpenEmbedding
  have hcross (i : ι) : ∀ᶠ n in _root_.Filter.atTop,
      ∃ s ∈ _root_.Set.Ioc 0 (L i), ∃ y ∈ frontier (⋃ k, A (k + n)), gamma i s = (y : UniformSpace.Completion M) := by
    apply DifferentialGeometry.Topology.eventually_exists_frontier_intersection_of_convergent_separators
      he hq hA hlim hnhds (hL i) (gamma i).continuous.continuousOn (hzero i)
    intro hz
    have hh := hrad i (L i) ⟨hL i, le_rfl⟩
    change _root_.Dist.dist q (gamma i (L i)) = L i at hh
    rw [hz, dist_self] at hh
    exact (hL i).ne hh
  have hcrossAll := Filter.eventually_all.mpr hcross
  have hcmpAll := Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hcmp i))
  obtain ⟨n, hn, hqn, hxn, hcn⟩ := (hnecks.and (hquant.and (hcrossAll.and hcmpAll))).exists
  obtain ⟨nk, hfront⟩ := hn
  choose t ht y hy hgy using hxn
  have hysphere (i : ι) := hfront (hy i)
  have hQ : 0 < Real.sqrt (metricScalarAt g (x n)) := Real.sqrt_pos.mpr nk.Q_pos
  have hball (i : ι) : _root_.Dist.dist (y i : UniformSpace.Completion M) (x n : UniformSpace.Completion M) ≤
      7 / Real.sqrt (metricScalarAt g (x n)) := by
    have hb := nk.central_sphere_subset_closedBall (hysphere i)
    change riemannianEDistOf g (x n) (y i) ≤ ENNReal.ofReal _ at hb
    rw [← hmetric, edist_dist] at hb
    rw [UniformSpace.Completion.dist_eq, dist_comm]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
  have hyrad (i : ι) : _root_.Dist.dist (y i : UniformSpace.Completion M) q = t i := by
    rw [← hgy i, dist_comm]
    exact hrad i (t i) (ht i)
  have hsmall (i : ι) : t i ≤ rho n := by
    have hh := dist_triangle (y i : UniformSpace.Completion M) (x n : UniformSpace.Completion M) q
    rw [hyrad] at hh
    exact hh.trans (by dsimp [rho]; linarith only [hball i])
  have hroot : 14 < Real.sqrt (metricScalarAt g (x n)) * _root_.Dist.dist q (x n : UniformSpace.Completion M) := by
    apply (sq_lt_sq₀ (by norm_num) (mul_nonneg hQ.le dist_nonneg)).mp
    rw [mul_pow, Real.sq_sqrt nk.Q_pos.le]
    norm_num only [show (14 : ℝ) ^ 2 = 196 by norm_num]
    exact hqn
  have hfar (i : ι) : 7 < Real.sqrt (metricScalarAt g (x n)) * t i := by
    have htri := dist_triangle q (y i : UniformSpace.Completion M) (x n : UniformSpace.Completion M)
    rw [dist_comm q (y i : UniformSpace.Completion M), hyrad] at htri
    have hb := (mul_le_mul_of_nonneg_left (hball i) hQ.le)
    have ht' := mul_le_mul_of_nonneg_left htri hQ.le
    rw [mul_div_cancel₀ _ hQ.ne'] at hb
    rw [mul_add] at ht'
    linarith only [hb, ht', hroot]
  have hseparated (i j : ι) (hij : i ≠ j) :
      14 * Real.sin (delta / 4) ≤ Real.sqrt (metricScalarAt g (x n)) * _root_.Dist.dist (y i) (y j) := by
    by_contra hnsep
    have hlow := hcn i j hij (t i) (ht i) (t j) (ht j) (hsmall i) (hsmall j)
    have hmin : 7 ≤ Real.sqrt (metricScalarAt g (x n)) * _root_.Min.min (t i) (t j) := by
      rcases le_total (t i) (t j) with hij | hji
      · rw [min_eq_left hij]; exact (hfar i).le
      · rw [min_eq_right hji]; exact (hfar j).le
    have hside : _root_.Dist.dist (y i) (y j) ≤ 2 * Real.sin ((delta / 2) / 2) * _root_.Min.min (t i) (t j) := by
      apply (mul_le_mul_iff_left₀ hQ).mp
      have hh := mul_le_mul_of_nonneg_left hmin (show 0 ≤ 2 * Real.sin (delta / 4) by positivity)
      rw [show delta / 2 / 2 = delta / 4 by ring]
      linarith only [hh, lt_of_not_ge hnsep]
    have hup := comparisonAngle_le_of_side_le_sin_mul_min (ht i).1 (ht j).1 dist_nonneg
      (theta := delta / 2) ⟨by positivity, by linarith [Real.pi_pos]⟩ hside
    have heq : radialComparisonAngle (fun i => gamma i) i j (t i) (t j) =
        comparisonAngle (t i) (t j) (_root_.Dist.dist (y i) (y j)) := by
      simp only [radialComparisonAngle, hgy, UniformSpace.Completion.dist_eq]
    rw [heq] at hlow
    exact (not_lt_of_ge hup) hlow
  have hyinj : Function.Injective y := by
    intro i j heq
    by_contra hij
    have hh := hseparated i j hij
    rw [heq, dist_self, _root_.MulZeroClass.mul_zero] at hh
    exact (not_le.mpr (by positivity : 0 < 14 * Real.sin (delta / 4))) hh
  let S : Finset M := Finset.univ.image y
  have hS : (S : Set M) ⊆ nk.map '' (_root_.Set.univ ×ˢ {(0 : ℝ)}) := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact hysphere i
  have hSsep : (S : Set M).Pairwise (fun a b =>
      14 * Real.sin (delta / 4) ≤ Real.sqrt (metricScalarAt g (x n)) * _root_.Dist.dist a b) := by
    intro a ha b hb hab
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    exact hseparated i j (fun hij => hab (congrArg y hij))
  have hcard := hpack nk hmetric S hS hSsep
  simpa only [S, Finset.card_image_of_injective _ hyinj, Finset.card_univ, Nat.card_eq_fintype_card] using hcard

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_card_bound_of_separated_radial_segments then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_card_bound_of_separated_radial_segments"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_card_bound_of_separated_radial_segments ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_card_bound_of_separated_radial_segments

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Toponogov

theorem totallyBounded_limiting_directions_of_convergent_neck_separators
    {M : Type*} [MetricSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [SigmaCompactSpace M] (g : SmoothRiemannianMetric I3 M)
    (hmetric : ∀ x y : M, _root_.EDist.edist x y = riemannianEDistOf g x y)
    (hsec : HasNonnegativeSectionalCurvature g)
    {q : UniformSpace.Completion M} (hq : q ∉ _root_.Set.range (fun x : M => (x : UniformSpace.Completion M)))
    {r : ℝ} (hcompact : IsCompact (Metric.closedBall q r))
    (hcover : Metric.closedBall q r ⊆ _root_.Insert.insert q (_root_.Set.range (fun x : M => (x : UniformSpace.Completion M))))
    (havoid : ∀ (beta : ℝ → UniformSpace.Completion M) (u v w : ℝ), u < v → v < w →
      (∀ s ∈ _root_.Set.Icc u w, ∀ t ∈ _root_.Set.Icc u w, _root_.Dist.dist (beta s) (beta t) = |s - t|) → beta v ≠ q)
    {A : ℕ → Set M} (hA : ∀ n, IsCompact (A n))
    (hlim : ∀ U ∈ 𝓝 q, ∀ᶠ n in _root_.Filter.atTop,
      (fun x : M => (x : UniformSpace.Completion M)) '' A n ⊆ U)
    (hnhds : _root_.Insert.insert q (⋃ n, (fun x : M => (x : UniformSpace.Completion M)) '' A n) ∈ 𝓝 q)
    {eps : ℝ} {x : ℕ → M}
    (hnecks : ∀ᶠ N in _root_.Filter.atTop, ∃ nk : SpatialNeck g eps (x N),
      frontier (⋃ n, A (n + N)) ⊆ nk.map '' (_root_.Set.univ ×ˢ {(0 : ℝ)}))
    (hx : _root_.Filter.Tendsto (fun n => (x n : UniformSpace.Completion M)) _root_.Filter.atTop (𝓝 q))
    (hscalar : _root_.Filter.Tendsto (fun n => metricScalarAt g (x n)) _root_.Filter.atTop _root_.Filter.atTop)
    (hquant : ∀ᶠ n in _root_.Filter.atTop, 196 < metricScalarAt g (x n) * _root_.Dist.dist q (x n : UniformSpace.Completion M) ^ 2)
    {ι : Type*} (L : ι → ℝ) (gamma : ι → C(ℝ, UniformSpace.Completion M))
    (hL : ∀ i, 0 < L i) (hLr : ∀ i, L i < r / 3) (hzero : ∀ i, gamma i 0 = q)
    (hdist : ∀ i, ∀ s ∈ _root_.Set.Icc 0 (L i), ∀ t ∈ _root_.Set.Icc 0 (L i), _root_.Dist.dist (gamma i s) (gamma i t) = |s - t|)
    (K : AngleKernel ι) (hK : ∀ i j, K.angle i j = limitingRadialAngle L (fun i => gamma i) i j) :
    let _ := K.metricSpace
    TotallyBounded (_root_.Set.univ : Set (Quotient K.setoid)) := by
  classical
  let _ := K.metricSpace
  apply Metric.totallyBounded_of_finset_card_le
  intro eta heta
  obtain ⟨N, hN⟩ := exists_card_bound_of_separated_radial_segments g hmetric hsec hq hcompact hcover havoid
    hA hlim hnhds hnecks hx hscalar hquant (lt_min heta Real.pi_pos) (min_le_right eta Real.pi)
  refine ⟨N, fun S _ hS => ?_⟩
  choose rep hrep using K.classOf_surjective
  have hsep : Pairwise fun i j : S => _root_.Min.min eta Real.pi ≤
      limitingRadialAngle (fun i : S => L (rep i)) (fun i : S => gamma (rep i)) i j := by
    intro i j hij
    have hne : (i : Quotient K.setoid) ≠ j := fun h => hij (Subtype.ext h)
    have hh := hS i.property j.property hne
    have heq : _root_.Dist.dist (i : Quotient K.setoid) (j : Quotient K.setoid) = K.angle (rep i) (rep j) := by
      change K.dist i j = _
      calc
        _ = K.dist (K.classOf (rep i)) (K.classOf (rep j)) := congrArg₂ K.dist (hrep i).symm (hrep j).symm
        _ = _ := K.dist_mk _ _
    change eta ≤ _root_.Dist.dist (i : Quotient K.setoid) (j : Quotient K.setoid) at hh
    rw [heq, hK] at hh
    exact (min_le_left eta Real.pi).trans hh
  have hh := hN (fun i : S => L (rep i)) (fun i : S => gamma (rep i))
    (fun i => hL (rep i)) (fun i => hLr (rep i)) (fun i => hzero (rep i))
    (fun i => hdist (rep i)) hsep
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.totallyBounded_limiting_directions_of_convergent_neck_separators then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.totallyBounded_limiting_directions_of_convergent_neck_separators"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.totallyBounded_limiting_directions_of_convergent_neck_separators ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.totallyBounded_limiting_directions_of_convergent_neck_separators

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
