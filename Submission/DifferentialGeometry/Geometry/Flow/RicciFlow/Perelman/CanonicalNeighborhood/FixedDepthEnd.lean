import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedRescaledLimit
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.ScalarRescaling
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedRescaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem exists_terminal_rescaled_local_backward_limit_of_pos_depth_scale_lower_bounds {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
      ∀ X : FlowSequence.{u}, ∀ depth scale : ℕ → ℝ,
      ∀ H0 S0 : ℝ, 0 < H0 → 0 < S0 →
      (∀ i, H0 ≤ depth i) → (∀ i, S0 ≤ scale i) →
      (∀ i, (X.interval i).carrier = _root_.Set.Icc (-(2 * depth i)) 0) →
      (∀ i, (X.interval i).regular = _root_.Set.Ioo (-(2 * depth i)) 0) →
      (∀ i, ConnectedSpace (X.term i).M) →
      ∀ orientation : ∀ i, TangentOrientationSection (X.term i).M,
      (∀ i t, t ∈ (X.interval i).carrier → MetricComplete ((X.term i).atTime t)) →
      (∀ i, ∃ C : ℝ, PointedFlowRmNormSqBounded (X.term i) C) →
      (∀ i, ParabolicallyKappaNoncollapsedBelowScale (X.term i).S
        (modelNoncollapseFactor * kappa) (Real.sqrt (scale i) * sigma)) →
      (∀ i, PhiAlmostNonnegative (X.term i).S (X.interval i).carrier
        (rescalePinchingFunction (scale i) Phi)) →
      (∀ i t, t ∈ _root_.Set.Icc (-depth i) 0 → ∀ x,
        2 ≤ (X.term i).S.scalar t x → OrientedWitness (X.term i).S (orientation i) eps kappa x t) →
      ∀ f : ℕ → ℕ,
      ∀ L : PointedRiemannianManifold.{u, 0, 0} I3,
      ∀ maps : PointedRiemannianConvergenceMaps (X.atTime 0) L f,
      ∀ conv : MetricConvergenceData maps,
      (∀ i, conv.domain i = CanonicalMetricCompactness.canonicalSourceData maps i) →
      ∀ W : TopologicalSpace.Opens L.M, ∀ x : ℕ → W,
      ∀ R : ℝ, 0 < R →
      (∀ n, 2 ≤ metricScalarAt L.metric (x n : L.M)) →
      _root_.Filter.Tendsto (fun n => metricScalarAt L.metric (x n : L.M)) _root_.Filter.atTop _root_.Filter.atTop →
      (∀ n, IsCompact (riemannianClosedBallOf (L.metric.restrictOpen W) (x n)
        (4 * R / Real.sqrt (metricScalarAt L.metric (x n : L.M))))) →
      ∃ j k : ℕ → ℕ, StrictMono j ∧ StrictMono k ∧
      ∃ hq : ∀ n, 1 ≤ (X.term (f (k n))).S.scalar 0
        (maps.partialDiffeomorph (k n) (x (j n) : L.M)),
      let q := fun n => (X.term (f (k n))).S.scalar 0
        (maps.partialDiffeomorph (k n) (x (j n) : L.M))
      let H := fun n => scaleMetric (q n) (lt_of_lt_of_le zero_lt_one (hq n))
        (L.metric.restrictOpen W)
      _root_.Filter.Tendsto (fun n => q n / metricScalarAt L.metric (x (j n) : L.M)) _root_.Filter.atTop (𝓝 1) ∧
      ∃ P : PointedRiemannianManifold.{0, 0, 0} I3,
      ∃ hpath : PathConnectedSpace P.M,
      ∃ tau : ℝ, ∃ htau : 0 < tau,
      ∃ S : SolutionOn (I := I3) (M := P.M) (RealTimeInterval.closed (-tau) 0 (by linarith)),
      ∃ C : ℕ → PartialDiffeomorph I3 I3 P.M W ∞,
        IsSolutionOn S ∧ S.base.metric 0 = P.metric ∧
        (∀ t ∈ _root_.Set.Icc (-tau) 0, SecLower (S.base.metric t) 0 _root_.Set.univ) ∧
        metricScalarAt P.metric P.basepoint = 1 ∧
        (∀ n, C n P.basepoint = x (j n)) ∧
        ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf P.metric P.basepoint r) ∧
          (∀ᶠ n in _root_.Filter.atTop, riemannianClosedBallOf P.metric P.basepoint r ⊆ (C n).source ∧
            riemannianClosedBallOf (H n) (x (j n)) (r / 4) ⊆
              (C n) '' riemannianClosedBallOf P.metric P.basepoint r) ∧
          ∀ eta : ℝ, 0 < eta → ∀ᶠ n in _root_.Filter.atTop,
            ∀ a ∈ riemannianClosedBallOf P.metric P.basepoint r,
              ∀ b ∈ riemannianClosedBallOf P.metric P.basepoint r,
                |metricDistance (H n) (C n a) (C n b) - metricDistance P.metric a b| < eta := by
  obtain ⟨epsStar, hepsStar, hflow⟩ := exists_local_backward_limit_with_end_comparison.{u, u} hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X depth scale H0 S0 hH0 hS0 hdepth hscale
    hcarrier hregular hconnected orientation hcomplete hsource hnoncollapse hpinching hgood
    f L maps conv hcanonical W x R hR hQ hQlim hcompact
  obtain ⟨k, hk, hq, hratio, hcmp⟩ := exists_scalar_rescaled_source_comparison
    (X.atTime 0) f L maps conv hcanonical W x hR hQ hcompact
  let q := fun n => (X.term (f (k n))).S.scalar 0 (maps.partialDiffeomorph (k n) (x n : L.M))
  have hq1 (n) : 1 ≤ q n := hq n
  have hratio' : _root_.Filter.Tendsto (fun n => q n / metricScalarAt L.metric (x n : L.M)) _root_.Filter.atTop (𝓝 1) := hratio
  have hqInf : _root_.Filter.Tendsto q _root_.Filter.atTop atTop := by
    apply _root_.Filter.tendsto_atTop_mono' _root_.Filter.atTop _ (hQlim.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    filter_upwards [hratio'.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))] with n hn
    have hp : 0 < metricScalarAt L.metric (x n : L.M) := by linarith [hQ n]
    have hh := (lt_div_iff₀ hp).mp hn
    linarith
  let X' := X.reindex (f ∘ k)
  let centers : ∀ n, (X'.term n).M := fun n => maps.partialDiffeomorph (k n) (x n : L.M)
  obtain ⟨ell, hell, hpos, hzero, Y, hY, _, _⟩ :=
    X'.exists_normalized_terminalCurvatureRescale_of_pos_lower_bounds
      (depth ∘ f ∘ k) (scale ∘ f ∘ k) hH0 hS0
      (fun n => hdepth (f (k n))) (fun n => hscale (f (k n)))
      (fun n => hcarrier (f (k n))) (fun n => hregular (f (k n)))
      (fun n => hconnected (f (k n))) (fun n => orientation (f (k n)))
      (fun n => hcomplete (f (k n))) (fun n => hsource (f (k n)))
      (fun n => hnoncollapse (f (k n))) (fun n => hpinching (f (k n)))
      (fun n => hgood (f (k n))) centers hqInf
  let Z := (X'.reindex ell).terminalCurvatureRescale (fun n => centers (ell n)) hpos hzero
  have hYZ : Y.toFlowSequence = Z := hY
  have hflowY := hflow eps heps hle sigma hsigma Phi hPhi Y
  rw [hYZ] at hflowY
  let H := fun n => scaleMetric (q (ell n)) (zero_lt_one.trans_le (hq1 (ell n)))
    (L.metric.restrictOpen W)
  let inc := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) W ⟨x 0⟩
  let B : ∀ n, PartialDiffeomorph I3 I3 W (Z.term n).M ∞ :=
    fun n => inc.trans (maps.partialDiffeomorph (k (ell n)))
  have hZmetric (n) : (Z.term n).S.base.metric 0 =
      scaleMetric (q (ell n)) (zero_lt_one.trans_le (hq1 (ell n)))
        ((X.term (f (k (ell n)))).S.base.metric 0) := by
    simp only [Z, FlowSequence.terminalCurvatureRescale, parabolicSolution, parabolicFamily,
      parabolicTime, zero_div, add_zero]
    rfl
  have hBbase (n) : B n (x (ell n)) = (Z.term n).basepoint := rfl
  have hBsource (n) : riemannianClosedBallOf (H n) (x (ell n)) R ⊆ (B n).source :=
    (hcmp (ell n)).2.1
  have hBcapture (n) : riemannianClosedBallOf ((Z.term n).S.base.metric 0)
      (Z.term n).basepoint (R / 4) ⊆ (B n) '' riemannianClosedBallOf (H n) (x (ell n)) R := by
    rw [hZmetric, ← hBbase]
    exact (hcmp (ell n)).2.2.2.1
  have hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in _root_.Filter.atTop,
      ∀ y ∈ riemannianClosedBallOf (H n) (x (ell n)) R, ∀ v : TangentSpace I3 y,
        (1 - eta) * (H n).inner y v v ≤ ((Z.term n).S.base.metric 0).inner (B n y)
          (mfderiv I3 I3 (B n) y v) (mfderiv I3 I3 (B n) y v) ∧
        ((Z.term n).S.base.metric 0).inner (B n y)
          (mfderiv I3 I3 (B n) y v) (mfderiv I3 I3 (B n) y v) ≤
            (1 + eta) * (H n).inner y v v := by
    intro eta heta
    have hlim : _root_.Filter.Tendsto (fun n : ℕ => 1 / ((ell n : ℝ) + 2)) _root_.Filter.atTop (𝓝 0) :=
      (tendsto_const_nhds.div_atTop
        (_root_.Filter.tendsto_atTop_add_const_right _root_.Filter.atTop 2 tendsto_natCast_atTop_atTop)).comp hell.tendsto_atTop
    filter_upwards [hlim.eventually (eventually_lt_nhds heta)] with n hn
    intro y hy v
    rw [hZmetric]
    have hh := (hcmp (ell n)).2.2.1 y hy v
    have hg := metric_inner_self_nonneg (H n) y v
    exact ⟨(mul_le_mul_of_nonneg_right (by linarith : 1 - eta ≤ 1 - 1 / ((ell n : ℝ) + 2)) hg).trans hh.1,
      hh.2.trans (mul_le_mul_of_nonneg_right (by linarith : 1 + 1 / ((ell n : ℝ) + 2) ≤ 1 + eta) hg)⟩
  obtain ⟨j, hj, P, hpath, tau, htau, S, C, hS, hterminal, hsec, hscalar, hbase, r, hr,
    hK, hcapture, hdist⟩ := hflowY W H (fun n => x (ell n)) B R hR hBsource hBbase hBcapture hBconv
  refine ⟨ell ∘ j, k ∘ ell ∘ j, hell.comp hj, hk.comp (hell.comp hj),
    fun n => hq1 (ell (j n)), ?_⟩
  dsimp only
  exact ⟨hratio'.comp (hell.comp hj).tendsto_atTop, P, hpath, tau, htau, S, C, hS, hterminal,
    hsec, hscalar, hbase, r, hr, hK, hcapture, hdist⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminal_rescaled_local_backward_limit_of_pos_depth_scale_lower_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminal_rescaled_local_backward_limit_of_pos_depth_scale_lower_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminal_rescaled_local_backward_limit_of_pos_depth_scale_lower_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminal_rescaled_local_backward_limit_of_pos_depth_scale_lower_bounds

private local instance pointedLimitRegular (L : PointedRiemannianManifold.{u, 0, 0} I3) :
    RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.pointedLimitRegular
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.pointedLimitRegular target :: scope.openDecls } }

theorem exists_local_backward_limit_on_end_of_pos_depth_scale_lower_bounds {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
      ∀ X : FlowSequence.{u}, ∀ depth scale : ℕ → ℝ,
      ∀ H0 S0 : ℝ, 0 < H0 → 0 < S0 →
      (∀ i, H0 ≤ depth i) → (∀ i, S0 ≤ scale i) →
      (∀ i, (X.interval i).carrier = _root_.Set.Icc (-(2 * depth i)) 0) →
      (∀ i, (X.interval i).regular = _root_.Set.Ioo (-(2 * depth i)) 0) →
      (∀ i, ConnectedSpace (X.term i).M) →
      ∀ orientation : ∀ i, TangentOrientationSection (X.term i).M,
      (∀ i t, t ∈ (X.interval i).carrier → MetricComplete ((X.term i).atTime t)) →
      (∀ i, ∃ C : ℝ, PointedFlowRmNormSqBounded (X.term i) C) →
      (∀ i, ParabolicallyKappaNoncollapsedBelowScale (X.term i).S
        (modelNoncollapseFactor * kappa) (Real.sqrt (scale i) * sigma)) →
      (∀ i, PhiAlmostNonnegative (X.term i).S (X.interval i).carrier
        (rescalePinchingFunction (scale i) Phi)) →
      (∀ i t, t ∈ _root_.Set.Icc (-depth i) 0 → ∀ x,
        2 ≤ (X.term i).S.scalar t x → OrientedWitness (X.term i).S (orientation i) eps kappa x t) →
      ∀ f : ℕ → ℕ,
      ∀ L : PointedRiemannianManifold.{u, 0, 0} I3,
      ∀ maps : PointedRiemannianConvergenceMaps (X.atTime 0) L f,
      ∀ conv : MetricConvergenceData maps,
      (∀ i, conv.domain i = CanonicalMetricCompactness.canonicalSourceData maps i) →
      ∀ W : TopologicalSpace.Opens L.M, ∀ hW : PathConnectedSpace W,
      let _ : PathConnectedSpace W := hW
      let _ : PseudoMetricSpace W := (L.metric.restrictOpen W).toPseudoMetricSpace
      let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
      ∀ q0 : UniformSpace.Completion W, ∀ d : ℝ, 0 < d →
        IsCompact (Metric.closedBall q0 d) →
        Metric.closedBall q0 d ⊆ _root_.Insert.insert q0 (_root_.Set.range (fun x : W => (x : UniformSpace.Completion W))) →
      ∀ x : ℕ → W, _root_.Filter.Tendsto (fun n => (x n : UniformSpace.Completion W)) _root_.Filter.atTop (𝓝 q0) →
        _root_.Filter.Tendsto (fun n => metricScalarAt L.metric (x n : L.M)) _root_.Filter.atTop _root_.Filter.atTop →
      ∀ c : ℝ, 0 < c →
        (∀ᶠ n in _root_.Filter.atTop, c ≤ metricScalarAt L.metric (x n : L.M) *
          _root_.Dist.dist (x n : UniformSpace.Completion W) q0 ^ 2) →
      ∃ j k : ℕ → ℕ, StrictMono j ∧ StrictMono k ∧
      ∃ hq : ∀ n, 1 ≤ (X.term (f (k n))).S.scalar 0
        (maps.partialDiffeomorph (k n) (x (j n) : L.M)),
      let q := fun n => (X.term (f (k n))).S.scalar 0
        (maps.partialDiffeomorph (k n) (x (j n) : L.M))
      let H := fun n => scaleMetric (q n) (lt_of_lt_of_le zero_lt_one (hq n))
        (L.metric.restrictOpen W)
      _root_.Filter.Tendsto (fun n => q n / metricScalarAt L.metric (x (j n) : L.M)) _root_.Filter.atTop (𝓝 1) ∧
      ∃ P : PointedRiemannianManifold.{0, 0, 0} I3,
      ∃ hpath : PathConnectedSpace P.M,
      ∃ tau : ℝ, ∃ htau : 0 < tau,
      ∃ S : SolutionOn (I := I3) (M := P.M) (RealTimeInterval.closed (-tau) 0 (by linarith)),
      ∃ C : ℕ → PartialDiffeomorph I3 I3 P.M W ∞,
        IsSolutionOn S ∧ S.base.metric 0 = P.metric ∧
        (∀ t ∈ _root_.Set.Icc (-tau) 0, SecLower (S.base.metric t) 0 _root_.Set.univ) ∧
        metricScalarAt P.metric P.basepoint = 1 ∧
        (∀ n, C n P.basepoint = x (j n)) ∧
        ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf P.metric P.basepoint r) ∧
          (∀ᶠ n in _root_.Filter.atTop, riemannianClosedBallOf P.metric P.basepoint r ⊆ (C n).source ∧
            riemannianClosedBallOf (H n) (x (j n)) (r / 4) ⊆
              (C n) '' riemannianClosedBallOf P.metric P.basepoint r) ∧
          ∀ eta : ℝ, 0 < eta → ∀ᶠ n in _root_.Filter.atTop,
            ∀ a ∈ riemannianClosedBallOf P.metric P.basepoint r,
              ∀ b ∈ riemannianClosedBallOf P.metric P.basepoint r,
                |metricDistance (H n) (C n a) (C n b) - metricDistance P.metric a b| < eta := by
  obtain ⟨epsStar, hepsStar, hflow⟩ :=
    exists_terminal_rescaled_local_backward_limit_of_pos_depth_scale_lower_bounds.{u} hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X depth scale H0 S0 hH0 hS0 hdepth hscale
    hcarrier hregular hconnected orientation hcomplete hsource hnoncollapse hpinching hgood
    f L maps conv hcanonical W hW
  let _ : PathConnectedSpace W := hW
  dsimp only
  let _ : PseudoMetricSpace W := (L.metric.restrictOpen W).toPseudoMetricSpace
  let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
  intro q0 d hd hKd hcover x hx hQ c hc hquant
  let R := Real.sqrt c / 16
  have hR : 0 < R := div_pos (Real.sqrt_pos.mpr hc) (by norm_num)
  have hsmall : (2 * (4 * R)) ^ 2 < c := by
    dsimp only [R]
    nlinarith [Real.sq_sqrt hc.le]
  have hballs := UniformSpace.Completion.coe_isometry.eventually_isCompact_scaled_closedBall
    hd hKd hcover hx (show 0 < 4 * R by positivity)
    (hquant.mono fun _ hn => hsmall.trans_le hn)
  have hcpt : ∀ᶠ n in _root_.Filter.atTop,
      IsCompact (riemannianClosedBallOf (L.metric.restrictOpen W) (x n)
        (4 * R / Real.sqrt (metricScalarAt L.metric (x n : L.M)))) := by
    filter_upwards [hballs] with n hn
    have heq : riemannianClosedBallOf (L.metric.restrictOpen W) (x n)
        (4 * R / Real.sqrt (metricScalarAt L.metric (x n : L.M))) =
        Metric.closedBall (x n) (4 * R / Real.sqrt (metricScalarAt L.metric (x n : L.M))) := by
      ext y
      change riemannianEDistOf (L.metric.restrictOpen W) (x n) y ≤ ENNReal.ofReal _ ↔ _root_.Dist.dist y (x n) ≤ _
      have hmetric : _root_.EDist.edist (x n) y = riemannianEDistOf (L.metric.restrictOpen W) (x n) y := rfl
      rw [← hmetric, edist_dist, ENNReal.ofReal_le_ofReal_iff (by positivity), dist_comm]
    exact heq.symm ▸ hn.2.1
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hcpt.and (hQ.eventually_ge_atTop 2))
  let x' := fun n => x (n + N)
  have hshift : StrictMono (fun n : ℕ => n + N) := fun _ _ hij => Nat.add_lt_add_right hij N
  obtain ⟨j, k, hj, hk, hq, hratio, P, hpath, tau, htau, S, C, hS, hterminal, hsec,
    hscalar, hbase, r, hr, hK, hcapture, hdist⟩ :=
    hflow eps heps hle sigma hsigma Phi hPhi X depth scale H0 S0 hH0 hS0 hdepth hscale
      hcarrier hregular hconnected orientation hcomplete hsource hnoncollapse hpinching hgood
      f L maps conv hcanonical W x' R hR (fun n => (hN (n + N) (by omega)).2)
      (hQ.comp hshift.tendsto_atTop) (fun n => (hN (n + N) (by omega)).1)
  refine ⟨fun n => j n + N, k, hshift.comp hj, hk, hq, ?_⟩
  dsimp only
  exact ⟨hratio, P, hpath, tau, htau, S, C, hS, hterminal, hsec, hscalar,
    hbase, r, hr, hK, hcapture, hdist⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_local_backward_limit_on_end_of_pos_depth_scale_lower_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_local_backward_limit_on_end_of_pos_depth_scale_lower_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_local_backward_limit_on_end_of_pos_depth_scale_lower_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_local_backward_limit_on_end_of_pos_depth_scale_lower_bounds

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
