import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckBusemannInward
import Mathlib.Topology.Order.IntermediateValue
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckOutwardSubsequence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckPositiveTopology
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckCoreSize
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.RayComparisonAngle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
set_option autoImplicit false

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

theorem SpatialNeckSideData.exists_pos_ray_mem_slice
    {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
    {p : N} {epsilon : ℝ} {W : SpatialNeckWitness h yStar p epsilon}
    (D : SpatialNeckSideData W) {c : ℝ≥0 → N} (hc : Isometry c)
    (s : ℝ) (hs : |s| < epsilon⁻¹ + 1) (hstart : c 0 ∈ D.lower s) :
    ∃ t : ℝ≥0, 0 < t ∧
      c t ∈ W.embedding '' {q : spatialNeckBuffer epsilon | q.val.2 = s} := by
  let _ : ConnectedSpace ℝ≥0 :=
    isConnected_iff_connectedSpace.mp (isConnected_Ici : IsConnected (_root_.Set.Ici (0 : ℝ)))
  obtain ⟨_, _, hlowOpen, huppOpen, hdisjoint, hcover, _⟩ := D.slice_spec s hs
  have hstartAvoid : c 0 ∉ W.embedding '' {q : spatialNeckBuffer epsilon | q.val.2 = s} := by
    have hm : c 0 ∈ D.lower s ∪ D.upper s := Or.inl hstart
    rwa [hcover] at hm
  have hex : ∃ t : ℝ≥0,
      c t ∈ W.embedding '' {q : spatialNeckBuffer epsilon | q.val.2 = s} := by
    by_contra! havoid
    have hsub : _root_.Set.range c ⊆ D.lower s ∪ D.upper s := by
      rw [hcover]
      rintro z ⟨t, rfl⟩
      exact havoid t
    have hlower : _root_.Set.range c ⊆ D.lower s :=
      (isConnected_range hc.continuous).isPreconnected.subset_left_of_subset_union
        hlowOpen huppOpen hdisjoint hsub ⟨c 0, _root_.Set.mem_range_self 0, hstart⟩
    obtain ⟨t, ht⟩ := (D.ray_eventually_upper hc s hs).exists
    exact Set.disjoint_left.mp hdisjoint (hlower (_root_.Set.mem_range_self t)) ht
  obtain ⟨t, ht⟩ := hex
  have htne : t ≠ 0 := by
    intro heq
    exact hstartAvoid (heq ▸ ht)
  exact ⟨t, lt_of_le_of_ne (show 0 ≤ t from bot_le) (Ne.symm htne), ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.exists_pos_ray_mem_slice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.exists_pos_ray_mem_slice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.exists_pos_ray_mem_slice ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSideData.exists_pos_ray_mem_slice

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
end

end

section
set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
  [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [IsRiemannianManifold I N]

theorem eventually_rays_cross_spatialNeck_core_of_scaled_distance_tendsto_atTop
    {g : SmoothRiemannianMetric I N} {marks : ℕ → SpatialNeckSphere}
    {centers : ℕ → N} {epsilon : ℝ}
    (W : ∀ i : ℕ, SpatialNeckWitness g (marks i) (centers i) epsilon)
    (hEnorm : IsMetricNorm (I := I) g) (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) g)
    (p : N) (hescape : _root_.Filter.Tendsto (fun i => _root_.Dist.dist p (centers i)) _root_.Filter.atTop _root_.Filter.atTop)
    (hscaled : _root_.Filter.Tendsto (fun i => Real.sqrt (metricScalarAt (I := I) g (centers i)) *
      _root_.Dist.dist p (centers i)) _root_.Filter.atTop _root_.Filter.atTop)
    {c d : ℝ≥0 → N} (hc : Isometry c) (hd : Isometry d)
    (hc0 : c 0 = p) (hd0 : d 0 = p) :
    ∀ᶠ i in _root_.Filter.atTop, ∃ s t : ℝ≥0, 0 < s ∧ 0 < t ∧
      c s ∈ (W i).core ∧ d t ∈ (W i).core ∧
      _root_.Dist.dist (centers i) (c s) ≤ spatialNeckCoreRadiusConstant epsilon /
        Real.sqrt (metricScalarAt (I := I) g (centers i)) ∧
      _root_.Dist.dist (centers i) (d t) ≤ spatialNeckCoreRadiusConstant epsilon /
        Real.sqrt (metricScalarAt (I := I) g (centers i)) := by
  classical
  let _ : NoncompactSpace N := ⟨by
    intro hcompact
    obtain ⟨B, hB⟩ := (Metric.isBounded_iff_subset_closedBall p).mp hcompact.isBounded
    obtain ⟨i, hi⟩ := (hescape.eventually_gt_atTop B).exists
    have hh : _root_.Dist.dist (centers i) p ≤ B := hB (_root_.Set.mem_univ _)
    rw [dist_comm] at hh
    linarith⟩
  choose W' hchoice hsphere hcore himage hside using
    fun i : ℕ => (W i).exists_ordered_compact_end_sides hsec
  let D : ∀ i : ℕ, SpatialNeckSideData (W' i) := fun i => Classical.choice (hside i)
  have havoid : ∀ᶠ i in _root_.Filter.atTop, p ∉ (W' i).core := by
    filter_upwards [hscaled.eventually_gt_atTop (spatialNeckCoreRadiusConstant epsilon)] with i hi
    intro hpin
    have hh := (W' i).core_dist_le hEnorm hsmall hpin
    rw [dist_comm] at hh
    have hroot : 0 < Real.sqrt (metricScalarAt (I := I) g (centers i)) :=
      Real.sqrt_pos.mpr (W i).scalar_pos
    have hprod := (le_div_iff₀ hroot).mp hh
    nlinarith
  have hescape' : _root_.Filter.Tendsto centers _root_.Filter.atTop (_root_.Filter.cocompact N) :=
    tendsto_cocompact_of_tendsto_dist_comp_atTop p (by
      simpa only [dist_comm] using hescape)
  have hlower := eventually_mem_spatialNeck_lower W' D hEnorm hsmall hsec.toNonnegative
    hc p havoid hescape'
  have hzero : |(0 : ℝ)| < epsilon⁻¹ + 1 := by
    have heps := (W 0).epsilon_pos
    rw [abs_zero]
    positivity
  filter_upwards [hlower] with i hi
  obtain ⟨s, hspos, hs⟩ := (D i).exists_pos_ray_mem_slice hc 0 hzero (hc0.symm ▸ hi)
  obtain ⟨t, htpos, ht⟩ := (D i).exists_pos_ray_mem_slice hd 0 hzero (hd0.symm ▸ hi)
  have hsCore : c s ∈ (W' i).core := by
    obtain ⟨z, hz, hzs⟩ := hs
    exact ⟨z, spatialNeckCentralDomain_subset_core epsilon (W' i).epsilon_pos hz, hzs⟩
  have htCore : d t ∈ (W' i).core := by
    obtain ⟨z, hz, hzt⟩ := ht
    exact ⟨z, spatialNeckCentralDomain_subset_core epsilon (W' i).epsilon_pos hz, hzt⟩
  exact ⟨s, t, hspos, htpos, (hcore i) ▸ hsCore, (hcore i) ▸ htCore,
    (W' i).core_dist_le hEnorm hsmall hsCore,
    (W' i).core_dist_le hEnorm hsmall htCore⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_rays_cross_spatialNeck_core_of_scaled_distance_tendsto_atTop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_rays_cross_spatialNeck_core_of_scaled_distance_tendsto_atTop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_rays_cross_spatialNeck_core_of_scaled_distance_tendsto_atTop ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_rays_cross_spatialNeck_core_of_scaled_distance_tendsto_atTop

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
end

end

section
set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
  [RiemannianBundle (fun q : N => TangentSpace I q)]
  [IsContinuousRiemannianBundle E (fun q : N => TangentSpace I q)]
  [IsRiemannianManifold I N]

theorem tendsto_rays_comparisonAngle_zero_of_spatialNecks
    {g : SmoothRiemannianMetric I N} {marks : ℕ → SpatialNeckSphere}
    {centers : ℕ → N} {epsilon : ℝ}
    (W : ∀ i : ℕ, SpatialNeckWitness g (marks i) (centers i) epsilon)
    (hEnorm : IsMetricNorm (I := I) g) (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (hsec : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) g)
    (p : N) (hescape : _root_.Filter.Tendsto (fun i => _root_.Dist.dist p (centers i)) _root_.Filter.atTop _root_.Filter.atTop)
    (hscaled : _root_.Filter.Tendsto (fun i => Real.sqrt (metricScalarAt (I := I) g (centers i)) *
      _root_.Dist.dist p (centers i)) _root_.Filter.atTop _root_.Filter.atTop)
    {c d : ℝ≥0 → N} (hc : Isometry c) (hd : Isometry d)
    (hc0 : c 0 = p) (hd0 : d 0 = p) :
    _root_.Filter.Tendsto (fun i => Geometry.Comparison.Toponogov.comparisonAngle
      (_root_.Dist.dist p (centers i)) (_root_.Dist.dist p (centers i))
      (_root_.Dist.dist (c (_root_.NNDist.nndist p (centers i))) (d (_root_.NNDist.nndist p (centers i))))) _root_.Filter.atTop (𝓝 0) := by
  let r : ℕ → ℝ≥0 := fun i => _root_.NNDist.nndist p (centers i)
  let B : ℕ → ℝ := fun i => spatialNeckCoreRadiusConstant epsilon /
    Real.sqrt (metricScalarAt (I := I) g (centers i))
  have hr : ∀ᶠ i in _root_.Filter.atTop, 0 < r i := by
    filter_upwards [hescape.eventually_gt_atTop 0] with i hi
    exact hi
  have hz : ∀ᶠ i in _root_.Filter.atTop, _root_.Dist.dist p (centers i) = (r i : ℝ) :=
    Eventually.of_forall fun _ => rfl
  have hcross : ∀ᶠ i in _root_.Filter.atTop, ∃ s t : ℝ≥0,
      dist (c s) (centers i) ≤ B i ∧ _root_.Dist.dist (d t) (centers i) ≤ B i := by
    filter_upwards [eventually_rays_cross_spatialNeck_core_of_scaled_distance_tendsto_atTop
      W hEnorm hsmall hsec p hescape hscaled hc hd hc0 hd0] with i hi
    obtain ⟨s, t, hs, ht, hsc, htc, hsd, htd⟩ := hi
    exact ⟨s, t, by simpa only [dist_comm] using hsd, by simpa only [dist_comm] using htd⟩
  have hthin : _root_.Filter.Tendsto (fun i => B i / (r i : ℝ)) _root_.Filter.atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := spatialNeckCoreRadiusConstant epsilon)).mul
      (tendsto_inv_atTop_zero.comp hscaled)
    simpa only [B, r, coe_nndist, div_div, div_eq_mul_inv, Function.comp_apply, mul_inv_rev,
      mul_assoc, mul_comm, mul_left_comm, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.zero_mul] using hh
  exact Geometry.Comparison.Toponogov.tendsto_comparisonAngle_zero_of_rays_near_common_points
    hc hd hc0 hd0 r centers B hr hz hcross hthin

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_rays_comparisonAngle_zero_of_spatialNecks then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_rays_comparisonAngle_zero_of_spatialNecks"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_rays_comparisonAngle_zero_of_spatialNecks ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.tendsto_rays_comparisonAngle_zero_of_spatialNecks

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
end

end
