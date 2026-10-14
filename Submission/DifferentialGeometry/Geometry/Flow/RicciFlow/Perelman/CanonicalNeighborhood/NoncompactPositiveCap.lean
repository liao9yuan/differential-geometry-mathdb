import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.EscapingStrongNecks
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckCapPlacement
import Submission.DifferentialGeometry.Geometry.Comparison.HopfRinow.MinimizingRay
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckSides
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Boundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation (axialZero)
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_localCap_at_base_of_noncompact_ancient_positive
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hnoncompact : NoncompactSpace F.M)
    (hsec : HasPositiveSectionalCurvature (F.S.base.metric 0)) (p : F.M)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon < 1 / 11)
    (K : Set F.M) (hK : IsCompact K) :
    ∃ (mark : SpatialNeckSphere) (v : F.M) (strong : StrongNeckWitness F.S mark v 0 epsilon)
      (nk : StrongNeck F.S epsilon v 0),
      nk.map.source = spatialNeckBuffer epsilon ∧ nk.map.target = _root_.Set.range strong.embedding ∧
      nk.center = mark ∧ (∀ z : spatialNeckBuffer epsilon, nk.map z.val = strong.embedding z) ∧
      ∃ (neck : StrongNeck F.S epsilon v 0) (U : Set F.M) (cap : LocalCap F.S epsilon p 0 U),
        (neck = nk ∨ neck = nk.axialReflection) ∧ K ⊆ interior cap.core.carrier ∧
        U = cap.core.carrier ∪ neck.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
        cap.tube = neck.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧ cap.tube_map = neck.map ∧
        ∃ j : Fin cap.chain.count, cap.chain.centers j = v ∧ HEq (cap.chain.necks j) neck ∧
          cap.chain.lo j = 0 ∧ cap.chain.hi j = 1 ∧ v ∈ cap.tube := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let _ : ConnectedSpace F.M := hF.connected
  let _ : NoncompactSpace F.M := hnoncompact
  let g := F.S.base.metric 0
  have hcomplete : RiemannianMetricComplete (I := I3) g := ⟨hF.complete 0 (by simp)⟩
  let _ : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I3 F.M
  let _ : T3Space F.M := inferInstance
  let _ : _root_.Bundle.RiemannianBundle (fun z : F.M => TangentSpace I3 z) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle ThreeSpace (fun z : F.M => TangentSpace I3 z) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let _ : EMetricSpace F.M := EMetricSpace.ofRiemannianMetric I3 F.M
  let _ : CompleteSpace F.M := hcomplete.complete
  have hEnorm : IsMetricNorm g := fun z v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g z v
  let _ : MetricSpace F.M := HopfRinow.riemMetricSpace (I := I3) (M := F.M)
  let _ : IsRiemannianManifold I3 F.M := ⟨fun z w => by
    rw [edist_dist, HopfRinow.riemMetric_dist_eq (I := I3)]
    exact ENNReal.ofReal_toReal (Exponential.riemannianEDist_ne_top z w)⟩
  obtain ⟨_soul, psi, _hsoul⟩ := Geometry.Topology.exists_diffeomorph_euclidean_three_of_positiveSectionalCurvature
    g hEnorm hsec (by simp [ThreeSpace])
  obtain ⟨mark, centers, strong, spatial, hsphere, hcores, hescape, _hscaled⟩ :=
    ancient_kappa_three_exists_disjoint_escaping_neckWitnesses_of_diffeomorph_euclidean F hF ⟨psi⟩ p
      hepsilon (hepsilonSmall.trans (by norm_num)) spatialNeckControlEpsilon_pos le_rfl
  have hescapeDist : _root_.Filter.Tendsto (fun i => _root_.Dist.dist (centers i) p) _root_.Filter.atTop atTop := by
    have heq (i : ℕ) : _root_.Dist.dist (centers i) p = (riemannianEDistOf g p (centers i)).toReal := by
      rw [dist_comm, HopfRinow.riemMetric_dist_eq (I := I3), riemannianEDistOf_eq_riemannianEDist g hEnorm]
    simpa only [heq] using hescape
  have hescape' : _root_.Filter.Tendsto centers _root_.Filter.atTop (_root_.Filter.cocompact F.M) :=
    tendsto_cocompact_of_tendsto_dist_comp_atTop p hescapeDist
  obtain ⟨c, hc, _hc0⟩ := exists_isometric_ray g hEnorm p
  obtain ⟨i, nk, hsrc, htgt, hcenter, hmap, _hcentral, neck, U, cap, hneck, hinside,
      _hcore, hU, htube, hcapmap, hchain⟩ := exists_localCap_of_disjoint_escaping_neckWitnesses
    strong spatial hsphere hEnorm le_rfl hepsilonSmall hsec hc hcores hescape' psi p K hK
  exact ⟨mark, centers i, strong i, nk, hsrc, htgt, hcenter, hmap, neck, U, cap,
    hneck, hinside, hU, htube, hcapmap, hchain⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_localCap_at_base_of_noncompact_ancient_positive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_localCap_at_base_of_noncompact_ancient_positive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_localCap_at_base_of_noncompact_ancient_positive ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_localCap_at_base_of_noncompact_ancient_positive

theorem exists_deep_localCap_at_base_of_noncompact_ancient_positive
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hnoncompact : NoncompactSpace F.M)
    (hsec : HasPositiveSectionalCurvature (F.S.base.metric 0)) (p : F.M)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon < 1 / 11)
    (H : ℝ) :
    ∃ (mark : SpatialNeckSphere) (v : F.M) (strong : StrongNeckWitness F.S mark v 0 epsilon)
      (nk : StrongNeck F.S epsilon v 0),
      nk.map.source = spatialNeckBuffer epsilon ∧ nk.map.target = _root_.Set.range strong.embedding ∧
      nk.center = mark ∧ (∀ z : spatialNeckBuffer epsilon, nk.map z.val = strong.embedding z) ∧
      ∃ (neck : StrongNeck F.S epsilon v 0) (U : Set F.M) (cap : LocalCap F.S epsilon p 0 U),
        (neck = nk ∨ neck = nk.axialReflection) ∧ (∀ y ∈ cap.tube, H / Real.sqrt (F.S.scalar 0 p) ≤ metricDistance (F.S.base.metric 0) p y) ∧
        U = cap.core.carrier ∪ neck.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
        cap.tube = neck.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧ cap.tube_map = neck.map ∧
        ∃ j : Fin cap.chain.count, cap.chain.centers j = v ∧ HEq (cap.chain.necks j) neck ∧
          cap.chain.lo j = 0 ∧ cap.chain.hi j = 1 ∧ v ∈ cap.tube := by
  let _ : ConnectedSpace F.M := hF.connected
  have hcomplete : RiemannianMetricComplete (F.S.base.metric 0) := ⟨hF.complete 0 (by simp)⟩
  let R := H / Real.sqrt (F.S.scalar 0 p)
  let K := riemannianClosedBallOf (F.S.base.metric 0) p R
  have hK : IsCompact K := hcomplete.closedEBall_isCompact p R
  obtain ⟨mark, v, strong, nk, hsrc, htgt, hcenter, hmap, neck, U, cap, hneck,
    hinside, hU, htube, hcapmap, hchain⟩ := exists_localCap_at_base_of_noncompact_ancient_positive
      F hF hnoncompact hsec p hepsilon hepsilonSmall K hK
  have hdepth := cap.tube_depth_of_ball_subset_core_interior (F.S.base.metric 0)
    (fun y hy => hinside (show y ∈ K from
      (show riemannianEDistOf (F.S.base.metric 0) p y < ENNReal.ofReal R from hy).le))
  exact ⟨mark, v, strong, nk, hsrc, htgt, hcenter, hmap, neck, U, cap, hneck,
    hdepth, hU, htube, hcapmap, hchain⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_deep_localCap_at_base_of_noncompact_ancient_positive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_deep_localCap_at_base_of_noncompact_ancient_positive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_deep_localCap_at_base_of_noncompact_ancient_positive ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_deep_localCap_at_base_of_noncompact_ancient_positive

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation (axialZero)
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_localCap_ball_sandwich_of_noncompact_ancient_positive
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hnoncompact : NoncompactSpace F.M)
    (hsec : HasPositiveSectionalCurvature (F.S.base.metric 0)) (p : F.M)
    {alpha : ℝ} (ha : 0 < alpha) (H : ℝ) :
    ∃ eps : ℝ, 0 < eps ∧ eps < alpha ∧
      ∃ (mark : SpatialNeckSphere) (v : F.M) (strong : StrongNeckWitness F.S mark v 0 eps)
        (nk : StrongNeck F.S eps v 0),
        nk.map.source = spatialNeckBuffer eps ∧ nk.map.target = _root_.Set.range strong.embedding ∧
        nk.center = mark ∧ (∀ z : spatialNeckBuffer eps, nk.map z.val = strong.embedding z) ∧
        ∃ (neck : StrongNeck F.S eps v 0) (U : Set F.M) (cap : LocalCap F.S eps p 0 U) (r : ℝ),
          (neck = nk ∨ neck = nk.axialReflection) ∧
          (Real.sqrt (F.S.scalar 0 p))⁻¹ ≤ r ∧
          riemannianBallOf (F.S.base.metric 0) p r ⊆ U ∧
          U ⊆ riemannianBallOf (F.S.base.metric 0) p (2 * r) ∧
          (∀ y ∈ cap.tube, _root_.Max.max 10000 H / Real.sqrt (F.S.scalar 0 p) ≤ metricDistance (F.S.base.metric 0) p y) ∧
          cap.tube_map = neck.map ∧ cap.chain.count = 1 ∧
          (∀ j : Fin cap.chain.count, cap.chain.centers j = v ∧ HEq (cap.chain.necks j) neck ∧
            cap.chain.lo j = 0 ∧ cap.chain.hi j = 1) ∧ v ∈ cap.tube := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let _ : ConnectedSpace F.M := hF.connected
  let _ : NoncompactSpace F.M := hnoncompact
  let g := F.S.base.metric 0
  have hcomplete : RiemannianMetricComplete (I := I3) g := ⟨hF.complete 0 (by simp)⟩
  let _ : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I3 F.M
  let _ : T3Space F.M := inferInstance
  let _ : _root_.Bundle.RiemannianBundle (fun z : F.M => TangentSpace I3 z) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle ThreeSpace (fun z : F.M => TangentSpace I3 z) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let _ : EMetricSpace F.M := EMetricSpace.ofRiemannianMetric I3 F.M
  let _ : CompleteSpace F.M := hcomplete.complete
  have hEnorm : IsMetricNorm g := fun z v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g z v
  let _ : MetricSpace F.M := HopfRinow.riemMetricSpace (I := I3) (M := F.M)
  let _ : IsRiemannianManifold I3 F.M := ⟨fun z w => by
    rw [edist_dist, HopfRinow.riemMetric_dist_eq (I := I3)]
    exact ENNReal.ofReal_toReal (Exponential.riemannianEDist_ne_top z w)⟩
  obtain ⟨_soul, psi, _hsoul⟩ := Geometry.Topology.exists_diffeomorph_euclidean_three_of_positiveSectionalCurvature
    g hEnorm hsec (by simp [ThreeSpace])
  have hintrinsic (x y : F.M) : _root_.Dist.dist x y = metricDistance (F.S.base.metric 0) x y := by
    rw [HopfRinow.riemMetric_dist_eq (I := I3), metricDistance, riemannianEDistOf_eq_riemannianEDist g hEnorm]
  obtain ⟨eta0, Cout, heta0, hCout, houter⟩ := exists_localCapOfCompactSide_outer_radius.{u}
  obtain ⟨Cd, hCd, hdiam⟩ := metricDistance_core_le_of_neckCoreDiameterBound.{u} neckCoreDiameterBound_holds
  let eps := _root_.Min.min (alpha / 2) (_root_.Min.min eta0 (1 / 44 : ℝ))
  have heps : 0 < eps := lt_min (by positivity) (lt_min heta0 (by norm_num))
  have hepsa : eps < alpha := (min_le_left _ _).trans_lt (by linarith)
  have heps0 : eps ≤ eta0 := (min_le_right _ _).trans (min_le_left _ _)
  have hepsSmall : eps < 1 / 11 := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num)
  obtain ⟨mark, centers, strong, spatial, hsphere, hcores, hescape, hscaled⟩ :=
    ancient_kappa_three_exists_disjoint_escaping_neckWitnesses_of_diffeomorph_euclidean F hF ⟨psi⟩ p
      heps (hepsSmall.trans (by norm_num)) spatialNeckControlEpsilon_pos le_rfl
  have hescapeDist : _root_.Filter.Tendsto (fun i => _root_.Dist.dist p (centers i)) _root_.Filter.atTop atTop := by
    simpa only [hintrinsic, metricDistance] using hescape
  have hscaledDist : _root_.Filter.Tendsto (fun i => Real.sqrt (F.S.scalar 0 (centers i)) * _root_.Dist.dist p (centers i)) _root_.Filter.atTop atTop := by
    simpa only [hintrinsic, metricDistance] using hscaled
  have hescape' : _root_.Filter.Tendsto centers _root_.Filter.atTop (_root_.Filter.cocompact F.M) :=
    tendsto_cocompact_of_tendsto_dist_comp_atTop p (by simpa only [dist_comm] using hescapeDist)
  obtain ⟨c, hc, hc0⟩ := exists_isometric_ray g hEnorm p
  let diamB := Metric.diam {x : F.M | Geometry.Topology.busemann c x ≤ 0}
  have hdiamB : 0 ≤ diamB := Metric.diam_nonneg
  let R := _root_.Max.max 10000 H / Real.sqrt (F.S.scalar 0 p)
  have hQp : 0 < F.S.scalar 0 p := ancientKappa_scalar_pos F hF le_rfl p
  have hRp : 0 < R := div_pos (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) (Real.sqrt_pos.mpr hQp)
  have hRroot : (Real.sqrt (F.S.scalar 0 p))⁻¹ ≤ R := by
    rw [← one_div]
    exact div_le_div_of_nonneg_right (by linarith [le_max_left (10000 : ℝ) H]) (Real.sqrt_nonneg _)
  have hfar := hescapeDist.eventually_gt_atTop (16 * (diamB + R))
  have hscaleFar := hscaledDist.eventually_gt_atTop (16 * (Cout + Cd))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hfar.and hscaleFar)
  let tail : ℕ → ℕ := fun i => N + i
  have htail : StrictMono tail := fun i j hij => Nat.add_lt_add_left hij N
  obtain ⟨i, nk, hsrc, htgt, hcenter, hmap, _hcentral, neck, hneck, ho, hinside⟩ :=
    exists_oriented_strongNeck_of_disjoint_escaping_neckWitnesses
      (fun i => strong (tail i)) (fun i => spatial (tail i)) (fun i => hsphere (tail i))
      hEnorm le_rfl hepsSmall hsec hc
      (fun i j hij => hcores (fun h => hij (htail.injective h)))
      (hescape'.comp htail.tendsto_atTop) psi p ∅ isCompact_empty
  have hp : p ∈ (neck.bicollarSides psi (axialZero (inv_pos.mpr neck.eps_pos))).compactSide := hinside (_root_.Set.mem_insert p ∅)
  obtain ⟨core⟩ := neck.nonempty_capCore_compactSide psi (axialZero (inv_pos.mpr neck.eps_pos))
  let cap := neck.localCapOfCompactSide psi ho core p hp
  let U := cap.core.carrier ∪ cap.tube
  let l := _root_.Dist.dist p (centers (tail i))
  let qroot := Real.sqrt (F.S.scalar 0 (centers (tail i)))
  have hqroot : 0 < qroot := Real.sqrt_pos.mpr neck.Q_pos
  have hl : 16 * (diamB + R) < l := (hN (tail i) (Nat.le_add_right N i)).1
  have hl0 : 0 < l := by linarith
  have hsl : 16 * (Cout + Cd) < qroot * l := (hN (tail i) (Nat.le_add_right N i)).2
  have hCsmall : Cout / qroot < l / 16 := (div_lt_iff₀ hqroot).mpr (by nlinarith)
  have hCdsmall : Cd / qroot < l / 16 := (div_lt_iff₀ hqroot).mpr (by nlinarith)
  have hBsmall : diamB < l / 16 := by linarith
  let r := (3 / 4 : ℝ) * l
  have hrpos : 0 < r := by dsimp only [r]; positivity
  have hrR : R ≤ r := by dsimp only [r]; linarith
  have hfront (y : F.M) (hy : y ∈ frontier cap.core.carrier) : r ≤ metricDistance (F.S.base.metric 0) p y := by
    have hy0 : y ∈ neck.map '' (_root_.Set.univ ×ˢ ({0} : Set ℝ)) := cap.inner_boundary.symm ▸ hy
    have hycore : y ∈ neck.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-10 : ℝ) 10) := by
      obtain ⟨z, hz, rfl⟩ := hy0
      refine ⟨z, ⟨hz.1, ?_⟩, rfl⟩
      have hz0 : z.2 = 0 := hz.2
      rw [hz0]
      norm_num
    have hvcore : centers (tail i) ∈ neck.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-10 : ℝ) 10) :=
      ⟨(neck.center, 0), ⟨mem_univ _, by norm_num⟩, neck.center_eq⟩
    have hh := hdiam F.M ancientTimeInterval F.S eps (centers (tail i)) 0 neck y hycore (centers (tail i)) hvcore
    rw [← hintrinsic] at hh
    have htri := dist_triangle p y (centers (tail i))
    rw [← hintrinsic]
    change _root_.Dist.dist y (centers (tail i)) ≤ Cd / qroot at hh
    change l ≤ _root_.Dist.dist p y + _root_.Dist.dist y (centers (tail i)) at htri
    dsimp only [r]
    linarith
  have hballcore : riemannianBallOf (F.S.base.metric 0) p r ⊆ interior cap.core.carrier :=
    Geometry.Metric.riemannianEDistOf_ball_subset_of_le_frontier_distance (F.S.base.metric 0) cap.center_inside
      (fun y hy => (ENNReal.ofReal_le_iff_le_toReal (riemannianEDistOf_ne_top (F.S.base.metric 0) p y)).mpr (hfront y hy))
  have hdepth := cap.tube_depth_of_ball_subset_core_interior (F.S.base.metric 0) hballcore
  have hout := (houter F.M ancientTimeInterval F.S eps 0 (centers (tail i)) neck psi ho core p hp
    heps0 hintrinsic hsec.toNonnegative c hc hc0).2
  have houterball : U ⊆ riemannianBallOf (F.S.base.metric 0) p (2 * r) := by
    intro y hy
    have hh := hout y hy
    change _root_.Dist.dist p y ≤ l + Cout / qroot + diamB at hh
    have hlt : metricDistance (F.S.base.metric 0) p y < 2 * r := by
      rw [← hintrinsic]
      dsimp only [r]
      linarith
    change riemannianEDistOf (F.S.base.metric 0) p y < ENNReal.ofReal (2 * r)
    rw [← ENNReal.ofReal_toReal (riemannianEDistOf_ne_top (F.S.base.metric 0) p y)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 2 * r)).mpr hlt
  have hcapdata := neck.localCapOfCompactSide_selected_neck psi ho core p hp
  exact ⟨eps, heps, hepsa, mark, centers (tail i), strong (tail i), nk, hsrc, htgt, hcenter, hmap,
    neck, U, cap, r, hneck, hRroot.trans hrR,
    fun y hy => Or.inl (interior_subset (hballcore hy)), houterball,
    fun y hy => hrR.trans (hdepth y hy), hcapdata.2.1, hcapdata.2.2.1, (fun j => ⟨(hcapdata.2.2.2.1 j).1, heq_of_eq (hcapdata.2.2.2.1 j).2.1,
      (hcapdata.2.2.2.1 j).2.2⟩), hcapdata.2.2.2.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_localCap_ball_sandwich_of_noncompact_ancient_positive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_localCap_ball_sandwich_of_noncompact_ancient_positive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_localCap_ball_sandwich_of_noncompact_ancient_positive ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_localCap_ball_sandwich_of_noncompact_ancient_positive

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
