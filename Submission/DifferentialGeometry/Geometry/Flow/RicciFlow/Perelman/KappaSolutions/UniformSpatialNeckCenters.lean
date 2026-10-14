import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.EscapingSpatialNeckCenters
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckWitnessConversion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderNecks
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalCurvatureTrichotomy
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.OrientedCylinderExclusion
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.CompactScalarBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientKappaFixedCompactness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_spatial_neck_of_noncompact_ancient_oriented_pointed_limit
    {X : PointedRiemannianSeq.{u, 0, 0} I3}
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hbase : PointedFlowScalarAtBase F 1)
    (hnoncompact : NoncompactSpace F.M) {subseq : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps X (F.atTime 0) subseq)
    (orient : ∀ i, TangentOrientationSection (X.obj i).M)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hsmall : epsilon < 1 / 11) :
    ∃ p : F.M, Nonempty (SpatialNeck (F.S.base.metric 0) epsilon p) := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rcases (xor_iff_or_and_not_and _ _).mp
      (ancientKappa_three_dimensional_split_branch F hF hdim) with ⟨hbranch, _⟩
  rcases hbranch with hpositive | ⟨C, hmodel⟩
  · have hsec : HasPositiveSectionalCurvature (F.S.base.metric 0) :=
      (hasPositiveSectionalCurvature_iff_forall_curvatureOperatorPositiveAt
        (F.S.base.metric 0) hdim).mpr (hpositive 0 le_rfl)
    obtain ⟨mark, centers, necks, _, _⟩ :=
      ancient_kappa_three_exists_escaping_spatial_neck_centers_of_positive_sectional
        F hF hnoncompact hsec F.basepoint hepsilon
    obtain ⟨W⟩ := necks 0
    obtain ⟨nk, _⟩ := W.exists_spatialNeck hepsilon hsmall le_rfl
    exact ⟨centers 0, ⟨nk⟩⟩
  · rcases hmodel with htrivial | hantipodal | hdiagonal
    · obtain ⟨mark, d, hmarked, hmetric, hnecks⟩ :=
        exists_strongNeck_of_shrinkingCylinderCover_trivialModel F C htrivial hbase
      obtain ⟨nk, _, _⟩ := hnecks epsilon hepsilon hsmall
      exact ⟨F.basepoint, ⟨nk.toSpatialNeck⟩⟩
    · obtain ⟨d, hd⟩ := hantipodal.1
      exact (pointedLimit_not_antipodalProduct_diffeomorph Phi orient ⟨d⟩).elim
    · exact exists_spatialNeck_of_shrinkingCylinderCover_diagonalModel
        F C hdiagonal hbase hepsilon hsmall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_spatial_neck_of_noncompact_ancient_oriented_pointed_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_spatial_neck_of_noncompact_ancient_oriented_pointed_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_spatial_neck_of_noncompact_ancient_oriented_pointed_limit ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_spatial_neck_of_noncompact_ancient_oriented_pointed_limit

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_comparable_spatial_neck_centers_of_noncompact_ancient_oriented_pointed_limit
    {X : PointedRiemannianSeq.{u, 0, 0} I3}
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval) {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hbase : PointedFlowScalarAtBase F 1)
    (hnoncompact : NoncompactSpace F.M)
    {subseq : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps X (F.atTime 0) subseq)
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i)
    (orient : ∀ i, TangentOrientationSection (X.obj i).M)
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ (p : F.M) (r c B : ℝ), 0 < r ∧ 0 < c ∧ 0 < B ∧
      ∀ᶠ i in _root_.Filter.atTop,
        Phi.map i p ∈ riemannianClosedBallOf (X.obj (subseq i)).metric
          (X.obj (subseq i)).basepoint r ∧
        c ≤ metricScalarAt (X.obj (subseq i)).metric (Phi.map i p) ∧
        metricScalarAt (X.obj (subseq i)).metric (Phi.map i p) ≤ B ∧
        Nonempty (SpatialNeck (X.obj (subseq i)).metric (2 * alpha) (Phi.map i p)) := by
  have htol : neckModelTolerance alpha < 1 / 11 :=
    (neckModelTolerance_le alpha).trans_lt (by linarith)
  obtain ⟨p, ⟨nk⟩⟩ := exists_spatial_neck_of_noncompact_ancient_oriented_pointed_limit
    F hF hbase hnoncompact Phi orient (neckModelTolerance_pos ha) htol
  let _ : PreconnectedSpace (F.atTime 0).M := hF.connected.toPreconnectedSpace
  have hcomplete : MetricComplete (F.atTime 0) := hF.complete 0 (by simp)
  have href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric := by
    intro i
    rw [hcanonical i]
    exact canonicalSourceData_referenceMetric_eq_limitMetric Phi i
  obtain ⟨r, hr, hcapture⟩ := Phi.exists_eventually_image_compact_subset_ball
    C href hcomplete (K := {p}) isCompact_singleton
  let q := metricScalarAt (F.S.base.metric 0) p
  have hq : 0 < q := nk.Q_pos
  have hscalar := pointedScalar_tendsto_of_metricCG_canonical_domains C hcanonical p
  have hlow : ∀ᶠ i in _root_.Filter.atTop, q / 2 < metricScalarAt (X.obj (subseq i)).metric (Phi.map i p) :=
    hscalar.eventually (Ioi_mem_nhds (by change q / 2 < q; linarith))
  have hhigh : ∀ᶠ i in _root_.Filter.atTop, metricScalarAt (X.obj (subseq i)).metric (Phi.map i p) < 2 * q :=
    hscalar.eventually (Iio_mem_nhds (by change q < 2 * q; linarith))
  refine ⟨p, r, q / 2, 2 * q, hr, by positivity, by positivity, ?_⟩
  filter_upwards [hcapture, hlow, hhigh,
    nk.eventually_transport_of_metric_convergence C hcanonical ha hsmall]
    with i hc hl hh hn
  exact ⟨hc.2 ⟨p, _root_.Set.mem_singleton p, rfl⟩, hl.le, hh.le, ⟨hn.choose⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_comparable_spatial_neck_centers_of_noncompact_ancient_oriented_pointed_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_comparable_spatial_neck_centers_of_noncompact_ancient_oriented_pointed_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_comparable_spatial_neck_centers_of_noncompact_ancient_oriented_pointed_limit ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_comparable_spatial_neck_centers_of_noncompact_ancient_oriented_pointed_limit

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_uniform_compact_or_spatial_neck_of_oriented_ancient_kappa
    (kappa : ℝ) {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
        IsAncientKappaSolution kappa F → PointedFlowScalarAtBase F 1 →
        TangentOrientationSection F.M →
        (CompactSpace F.M ∧ ∀ p : F.M,
          p ∈ riemannianClosedBallOf (F.S.base.metric 0) F.basepoint r ∧
          C⁻¹ ≤ F.S.scalar 0 p ∧ F.S.scalar 0 p ≤ C) ∨
        ∃ p : F.M,
          p ∈ riemannianClosedBallOf (F.S.base.metric 0) F.basepoint r ∧
          C⁻¹ ≤ F.S.scalar 0 p ∧ F.S.scalar 0 p ≤ C ∧
          Nonempty (SpatialNeck (F.S.base.metric 0) (2 * alpha) p) := by
  classical
  by_contra hnone
  have hbad (n : ℕ) : ∃ F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
      ∃ o : TangentOrientationSection F.M,
      IsAncientKappaSolution kappa F ∧ PointedFlowScalarAtBase F 1 ∧
      ¬ ((CompactSpace F.M ∧ ∀ p : F.M,
          p ∈ riemannianClosedBallOf (F.S.base.metric 0) F.basepoint ((n : ℝ) + 1) ∧
          ((n : ℝ) + 1)⁻¹ ≤ F.S.scalar 0 p ∧ F.S.scalar 0 p ≤ (n : ℝ) + 1) ∨
        ∃ p : F.M,
          p ∈ riemannianClosedBallOf (F.S.base.metric 0) F.basepoint ((n : ℝ) + 1) ∧
          ((n : ℝ) + 1)⁻¹ ≤ F.S.scalar 0 p ∧ F.S.scalar 0 p ≤ (n : ℝ) + 1 ∧
          Nonempty (SpatialNeck (F.S.base.metric 0) (2 * alpha) p)) := by
    by_contra hno
    push Not at hno
    exact hnone ⟨(n : ℝ) + 1, (n : ℝ) + 1, by positivity, by positivity,
      fun F hF hbase o => hno F o hF hbase⟩
  choose X orient hX hbase hbad using hbad
  obtain ⟨L, phi, hphi, Phi, hL, hLbase, hKL, hconv, hcmp⟩ :=
    exists_ancientKappa_fixed_kappa_compactness X hX hbase
  let F := Phi.atTime (X := ancientPointedFlowSeq X) (L := L) 0
  obtain ⟨C0, hC0⟩ := hconv 0 le_rfl
  have hthreshold : _root_.Filter.Tendsto (fun i => (phi i : ℝ) + 1) _root_.Filter.atTop atTop :=
    (_root_.Filter.tendsto_atTop_add_const_right _root_.Filter.atTop 1 tendsto_natCast_atTop_atTop).comp hphi.tendsto_atTop
  by_cases hcompact : CompactSpace L.M
  · let _ : PreconnectedSpace (L.atTime (I := I3) 0).M := hL.connected.toPreconnectedSpace
    have hcompact0 : CompactSpace (L.atTime (I := I3) 0).M := hcompact
    let _ : CompactSpace (L.atTime (I := I3) 0).M := hcompact0
    obtain ⟨r, c, B, hr, hc, hB, hmodels⟩ :=
      exists_eventually_scalar_bounds_and_bounded_radius_of_compact_positive_limit
        (L := L.atTime (I := I3) 0) F C0 hC0
        (fun i => (hX (phi i)).connected.toPreconnectedSpace)
        (fun p => ancientKappa_scalar_pos L hL le_rfl p)
    have hlarge : ∀ᶠ i in _root_.Filter.atTop, _root_.Max.max r (_root_.Max.max B c⁻¹) ≤ (phi i : ℝ) + 1 :=
      hthreshold.eventually (_root_.Filter.eventually_ge_atTop _)
    obtain ⟨i, hi, hlargei⟩ := (hmodels.and hlarge).exists
    have hinv : ((phi i : ℝ) + 1)⁻¹ ≤ c := by
      have hle : c⁻¹ ≤ (phi i : ℝ) + 1 := (le_max_right B c⁻¹).trans
        ((le_max_right r (_root_.Max.max B c⁻¹)).trans hlargei)
      simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hc) hle
    apply hbad (phi i)
    refine Or.inl ⟨hi.1, ?_⟩
    intro p
    exact ⟨riemannianClosedBallOf_mono _ _ ((le_max_left _ _).trans hlargei) (hi.2 p).1,
      hinv.trans (hi.2 p).2.1, (hi.2 p).2.2.trans ((le_max_left B c⁻¹).trans
        ((le_max_right r (_root_.Max.max B c⁻¹)).trans hlargei))⟩
  · have hnoncompact : NoncompactSpace L.M := ⟨fun h => hcompact ⟨h⟩⟩
    obtain ⟨p, r, c, B, hr, hc, hB, hcenters⟩ :=
      exists_comparable_spatial_neck_centers_of_noncompact_ancient_oriented_pointed_limit
        L hL hLbase hnoncompact F C0 hC0 orient ha hsmall
    have hlarge : ∀ᶠ i in _root_.Filter.atTop, _root_.Max.max r (_root_.Max.max B c⁻¹) ≤ (phi i : ℝ) + 1 :=
      hthreshold.eventually (_root_.Filter.eventually_ge_atTop _)
    obtain ⟨i, hi, hlargei⟩ := (hcenters.and hlarge).exists
    have hinv : ((phi i : ℝ) + 1)⁻¹ ≤ c := by
      have hle : c⁻¹ ≤ (phi i : ℝ) + 1 := (le_max_right B c⁻¹).trans
        ((le_max_right r (_root_.Max.max B c⁻¹)).trans hlargei)
      simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hc) hle
    apply hbad (phi i)
    refine Or.inr ⟨F.map i p, ?_, hinv.trans hi.2.1, ?_, hi.2.2.2⟩
    · exact riemannianClosedBallOf_mono _ _ ((le_max_left _ _).trans hlargei) hi.1
    · exact hi.2.2.1.trans ((le_max_left B c⁻¹).trans
        ((le_max_right r (_root_.Max.max B c⁻¹)).trans hlargei))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_compact_or_spatial_neck_of_oriented_ancient_kappa then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_compact_or_spatial_neck_of_oriented_ancient_kappa"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_compact_or_spatial_neck_of_oriented_ancient_kappa ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_uniform_compact_or_spatial_neck_of_oriented_ancient_kappa

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
