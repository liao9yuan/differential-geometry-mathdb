import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointArmBounds
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.MinimizingArms
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedSourceRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabRicciCoefficientLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RecenteredScalarBoundReduction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.InverseSpatialNeckTransfer
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Comparison.Toponogov
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private theorem sectional_nonnegative_of_secLower_zero
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] (g : SmoothRiemannianMetric I3 M)
    (h : SecLower g 0 _root_.Set.univ) : HasNonnegativeSectionalCurvature g := by
  apply (hasNonnegativeSectionalCurvature_iff g).mpr
  intro x v w
  have hvec : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
    funext i
    fin_cases i <;> simp [vec4]
  simpa only [_root_.MulZeroClass.zero_mul, metricRm04StandardAt_apply, hvec] using h x (_root_.Set.mem_univ x) v w

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.sectional_nonnegative_of_secLower_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.sectional_nonnegative_of_secLower_zero target :: scope.openDecls } }

theorem exists_spatialNeck_of_backwardExtension_comparisonAngle
    (kappa : ℝ) {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ epsStar R : ℝ, 0 < epsStar ∧ 0 < R ∧
      ∀ {eps sigma : ℝ} {Phi : ℝ → ℝ}, eps ≤ epsStar →
        ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
          (J : RealTimeInterval) (B : BackwardExtension L J),
          ∀ s ∈ J.carrier, ∀ y p z : L.space.M,
            4 < B.solution.scalar s y →
            R < Real.sqrt (B.solution.scalar s y) * metricDistance (B.solution.base.metric s) y p →
            R < Real.sqrt (B.solution.scalar s y) * metricDistance (B.solution.base.metric s) y z →
            Real.pi / 3 ≤ comparisonAngle (metricDistance (B.solution.base.metric s) y p)
              (metricDistance (B.solution.base.metric s) y z)
              (metricDistance (B.solution.base.metric s) p z) →
            Nonempty (SpatialNeck (B.solution.base.metric s) (2 * alpha) y) := by
  let beta := neckModelTolerance alpha / 2
  have hb : 0 < beta := half_pos (neckModelTolerance_pos ha)
  have hbsmall : beta < 1 / 44 := by
    have htol := neckModelTolerance_le alpha
    dsimp only [beta]
    linarith
  obtain ⟨Lmin, Lmax, epsStar, C, hLmin, hLmax, hepsStar, _hepsSmall, _hC, hneck⟩ :=
    exists_good_point_neck_arm_bounds.{u} kappa hb hbsmall
      (by positivity : 0 < Real.pi / 6)
  refine ⟨epsStar, Lmax, hepsStar, hLmin.trans hLmax, ?_⟩
  intro eps sigma pinching heps X L J B s hs y p z hq hlongp hlongz hang
  let _ : ConnectedSpace L.space.M := L.connected
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let P : PointedRiemannianManifold.{u, 0, 0} I3 :=
    { L.space with metric := B.solution.base.metric s }
  let f := L.subseq ∘ B.subseq
  let F := X.toFlowSequence.sliceMaps (subsequenceMaps L.maps B.subseq B.strictMono)
    B.solution.base.metric s
  obtain ⟨Ct, hcanonical⟩ := B.convergence.exists_canonical_metric_convergence hs
  have hcomplete : MetricComplete P := B.complete s hs
  have href : ∀ i, (Ct.domain i).referenceMetric = (Ct.domain i).limitMetric := by
    intro i
    rw [hcanonical i]
    exact canonicalSourceData_referenceMetric_eq_limitMetric F i
  have hsec : HasNonnegativeSectionalCurvature P.metric :=
    sectional_nonnegative_of_secLower_zero P.metric (B.nonnegative s hs)
  let q := B.solution.scalar s y
  have hqpos : 0 < q := by dsimp [q]; linarith
  let m := (Lmin + Lmax) / 2
  have hmlo : Lmin < m := by dsimp [m]; linarith
  have hmhi : m < Lmax := by dsimp [m]; linarith
  have hmpos : 0 < m := hLmin.trans hmlo
  let r := m / Real.sqrt q
  have hr : 0 < r := div_pos hmpos (Real.sqrt_pos.mpr hqpos)
  have hrp : r < metricDistance P.metric y p := by
    apply (div_lt_iff₀ (Real.sqrt_pos.mpr hqpos)).mpr
    rw [mul_comm]
    exact hmhi.trans hlongp
  have hrz : r < metricDistance P.metric y z := by
    apply (div_lt_iff₀ (Real.sqrt_pos.mpr hqpos)).mpr
    rw [mul_comm]
    exact hmhi.trans hlongz
  have hangle : Real.pi / 6 < comparisonAngle (metricDistance P.metric y p)
      (metricDistance P.metric y z) (metricDistance P.metric p z) :=
    (by nlinarith [Real.pi_pos] : Real.pi / 6 < Real.pi / 3).trans_le hang
  have htime := eventually_mem_backwardWindow B hs
  have hsource : ∀ᶠ i in _root_.Filter.atTop,
      MetricComplete ((X.toFlowSequence.atTime s).obj (f i)) := by
    filter_upwards [htime] with i hi
    apply X.complete (f i) s
    rw [X.carrier_eq]
    exact ⟨by have hleft : -(X.depth (f i) / 2) ≤ s := hi.1
              linarith [hleft, X.depth_pos (f i)], hi.2⟩
  have harms := eventually_exists_minimizingArms_comparisonAngle_lt Ct href hcomplete
    hsec hsource (fun i => X.connected (f i)) y p z hr hrp hrz hangle
  have hscalar : _root_.Filter.Tendsto (fun i => (X.term (f i)).S.scalar s (F.map i y)) _root_.Filter.atTop (𝓝 q) :=
    pointedScalar_tendsto_of_metricCG_canonical_domains Ct hcanonical y
  have hhigh : ∀ᶠ i in _root_.Filter.atTop, 2 < (X.term (f i)).S.scalar s (F.map i y) :=
    hscalar.eventually (Ioi_mem_nhds (by dsimp [q]; linarith))
  have hnormalize : Real.sqrt q * r = m := by
    dsimp only [r]
    rw [mul_div_cancel₀ _ (Real.sqrt_pos.mpr hqpos).ne']
  have hnormalized : _root_.Filter.Tendsto (fun i => Real.sqrt ((X.term (f i)).S.scalar s (F.map i y)) * r)
      atTop (𝓝 m) := by
    rw [← hnormalize]
    exact hscalar.sqrt.mul_const r
  have hsamples : ∀ᶠ i in _root_.Filter.atTop,
      Real.sqrt ((X.term (f i)).S.scalar s (F.map i y)) * r ∈ _root_.Set.Icc Lmin Lmax :=
    (hnormalized.eventually (Ioo_mem_nhds hmlo hmhi)).mono fun _ hi => ⟨hi.1.le, hi.2.le⟩
  obtain ⟨rho, hrho, hcapture⟩ := F.exists_eventually_image_compact_subset_ball Ct href
    hcomplete (K := {y}) isCompact_singleton
  have hinverse := eventually_spatialNeck_inverse_transport_of_mem_closedBall Ct hcanonical
    hcomplete ha hsmall rho hrho.le
  obtain ⟨i, htimei, hhighi, hsamplei, harmi, hcapturei, hinversei⟩ :=
    (htime.and (hhigh.and (hsamples.and (harms.and (hcapture.and hinverse))))).exists
  have htimegood : s ∈ _root_.Set.Icc (-X.depth (f i)) 0 :=
    ⟨by have hleft : -(X.depth (f i) / 2) ≤ s := htimei.1
        linarith [hleft, X.depth_pos (f i)], htimei.2⟩
  obtain ⟨W, _orient, _horient⟩ := X.higher_good (f i) s htimegood (F.map i y) hhighi.le
  have hregular := X.regular_window_of_higher_good (f i) htimegood hhighi.le W
  obtain ⟨a, b, _ha, _hb, _hap, _hbz, hra, hrb, hab⟩ := harmi
  obtain ⟨neck, _path, _intersection, _tailA, _tailB, _diam⟩ :=
    hneck (X.interval (f i)) (X.term (f i)) (X.orientation (f i)) eps (F.map i y) s W
      heps hregular a b r r ⟨hr, hra.le⟩ ⟨hr, hrb.le⟩ hsamplei hsamplei hab.le
  have htol : 2 * beta = neckModelTolerance alpha := by dsimp only [beta]; ring
  have nk : SpatialNeck ((X.term (f i)).S.base.metric s) (neckModelTolerance alpha)
      (F.map i y) := htol ▸ neck.toSpatialNeck
  obtain ⟨result, _hmap⟩ := hinversei y (hcapturei.1 (_root_.Set.mem_singleton y))
    (hcapturei.2 ⟨y, _root_.Set.mem_singleton y, rfl⟩) (by change 2 ≤ B.solution.scalar s y; linarith) nk
  exact ⟨result⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatialNeck_of_backwardExtension_comparisonAngle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatialNeck_of_backwardExtension_comparisonAngle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatialNeck_of_backwardExtension_comparisonAngle ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_spatialNeck_of_backwardExtension_comparisonAngle

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
