import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedEscapeLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedSegmentNecks
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedSpatialNecks

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
set_option autoImplicit false
noncomputable section

open _root_.Filter _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_terminal_pointed_limit_with_missing_endpoint_and_spatialNecks
    {kappa : ℝ} (hkappa : 0 < kappa) {A : ℝ} (hA : 0 ≤ A)
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ epsStar c : ℝ, 0 < epsStar ∧ 0 < c ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ¬ BoundedAtDistance X → ∃ f : ℕ → ℕ, ∃ hf : StrictMono f,
              ∃ F : FiniteControlledRadius (X.reindex f hf), ∃ r : ℕ → ℝ,
                (∀ k, 0 < r k ∧ r k < F.radius) ∧ _root_.Filter.Tendsto r _root_.Filter.atTop (nhds F.radius) ∧
                ∃ L : PointedRiemannianManifold.{u, 0, 0} (I := I3),
                ∃ hL : PathConnectedSpace L.M,
                let _ : PathConnectedSpace L.M := hL
                ∃ maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f,
                  ∃ C : PointedRiemannianConverges (X.toFlowSequence.atTime 0) L f maps,
                  (∀ k, C.metrics.domain k = CanonicalMetricCompactness.canonicalSourceData maps k) ∧
                  (∀ k, maps.target k = riemannianBallOf ((X.term (f k)).S.base.metric 0)
                    (X.term (f k)).basepoint (r k)) ∧
                  (∀ eta : ℝ, 0 < eta → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
                    ∀ x ∈ maps.source k, ∀ v : TangentSpace I3 x,
                      (1 - eta) * L.metric.inner x v v ≤
                        ((X.term (f k)).S.base.metric 0).inner (maps.partialDiffeomorph k x)
                          (mfderiv I3 I3 (maps.partialDiffeomorph k) x v)
                          (mfderiv I3 I3 (maps.partialDiffeomorph k) x v) ∧
                      ((X.term (f k)).S.base.metric 0).inner (maps.partialDiffeomorph k x)
                          (mfderiv I3 I3 (maps.partialDiffeomorph k) x v)
                          (mfderiv I3 I3 (maps.partialDiffeomorph k) x v) ≤
                        (1 + eta) * L.metric.inner x v v) ∧
                  (∀ R : ℝ, 0 ≤ R → R < F.radius →
                    IsCompact (riemannianClosedBallOf L.metric L.basepoint R)) ∧
                  metricScalarAt L.metric L.basepoint = 1 ∧
                  (∀ (x : L.M) (v w : TangentSpace I3 x),
                    0 ≤ metricRm04StandardAt L.metric x v w w v) ∧
                    let _ : EMetricSpace L.M := L.emetricSpace
                    let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
                      (fun x y => riemannianEDistOf_ne_top L.metric x y)
                    ∃ phi : ℕ → ℕ, ∃ (γ : ∀ n, ℝ → (X.term (f (phi n))).M)
                      (s : ℕ → ℝ) (g : C(_root_.Set.Ico 0 F.radius, L.M)),
                      StrictMono phi ∧ Isometry g ∧ g ⟨0, le_rfl, F.radius_pos⟩ = L.basepoint ∧
                      (∀ n,
                        let ell := metricDistance ((X.term (f (phi n))).S.base.metric 0)
                          (X.term (f (phi n))).basepoint (F.points (phi n))
                        s n ∈ _root_.Set.Ico 0 ell ∧ γ n 0 = (X.term (f (phi n))).basepoint ∧
                          γ n ell = F.points (phi n) ∧ ContMDiff 𝓘(ℝ, ℝ) I3 ∞ (γ n) ∧
                          (∀ t, IsGeodesicAt ((X.term (f (phi n))).S.base.metric 0) (γ n) t) ∧
                          (∀ t, ((X.term (f (phi n))).S.base.metric 0).inner (γ n t)
                            (mfderiv 𝓘(ℝ, ℝ) I3 (γ n) t 1)
                            (mfderiv 𝓘(ℝ, ℝ) I3 (γ n) t 1) = 1) ∧
                          (∀ t ∈ _root_.Set.Icc 0 ell, ∀ v ∈ _root_.Set.Icc 0 ell,
                            metricDistance ((X.term (f (phi n))).S.base.metric 0)
                              (γ n t) (γ n v) = |t - v|) ∧
                          (X.term (f (phi n))).S.scalar 0 (γ n (s n)) = 2 ∧
                          (∀ t ∈ _root_.Set.Ioc (s n) ell, 2 < (X.term (f (phi n))).S.scalar 0 (γ n t)) ∧
                          c < ell - s n) ∧
                      (∀ A : Set (_root_.Set.Ico 0 F.radius), IsCompact A → TendstoUniformlyOn
                        (fun n (t : _root_.Set.Ico 0 F.radius) => (maps.partialDiffeomorph (phi n)).symm (γ n t))
                        g _root_.Filter.atTop A) ∧
                      (∀ x : L.M, ¬ _root_.Filter.Tendsto g
                        (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 F.radius → ℝ) (𝓝 F.radius)) (𝓝 x)) ∧
                      _root_.Filter.Tendsto (fun t => metricScalarAt L.metric (g t))
                        (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 F.radius → ℝ) (𝓝 F.radius)) _root_.Filter.atTop ∧
                      ∃ q : UniformSpace.Completion L.M,
                        _root_.Filter.Tendsto (fun t => (g t : UniformSpace.Completion L.M))
                          (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 F.radius → ℝ) (𝓝 F.radius)) (𝓝 q) ∧
                        (∀ t : _root_.Set.Ico 0 F.radius, _root_.Dist.dist q (g t : UniformSpace.Completion L.M) =
                          F.radius - t) ∧
                        (q ∉ _root_.Set.range (fun x : L.M => (x : UniformSpace.Completion L.M))) ∧
                        (∀ t : _root_.Set.Ico 0 F.radius, 2 < metricScalarAt L.metric (g t) →
                          A ^ 2 ≤ metricScalarAt L.metric (g t) *
                            _root_.Dist.dist q (g t : UniformSpace.Completion L.M) ^ 2) ∧
                        ∀ᶠ (tau : _root_.Set.Ico 0 F.radius) in
                          _root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 F.radius → ℝ) (𝓝 F.radius),
                          Nonempty (SpatialNeck L.metric (2 * alpha) (g tau)) := by
  have htol : 0 < neckModelTolerance alpha / 2 := half_pos (neckModelTolerance_pos ha)
  have htolSmall : neckModelTolerance alpha / 2 < 1 / 32 := by
    have hh := neckModelTolerance_le alpha
    linarith
  obtain ⟨B, epsNeck, hB, hepsNeck, hneck⟩ :=
    exists_eventually_strongNeck_at_pointed_images_near_scalar_blowup_endpoint.{u}
      kappa htol htolSmall
  obtain ⟨D, hD, htransport⟩ := exists_spatialNeck_of_pointed_strongNecks_on_compact_ball.{u} ha hsmall
  obtain ⟨epsEscape, c, hepsEscape, hc, hescape⟩ :=
    exists_terminal_pointed_limit_with_missing_endpoint_of_not_boundedAtDistance.{u}
      hkappa (A := _root_.Max.max A (_root_.Max.max B (4 * D))) (hA.trans (le_max_left _ _))
  refine ⟨min epsEscape epsNeck, c, lt_min hepsEscape hepsNeck, hc, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X hnot
  obtain ⟨f, hf, F, r, hr, hrT, L, hL, maps, C, hcanonical, htargets, hmetrics,
    hcompact, hbase, hsec, phi, γ, s, g, hphi, hg, hgbase, hγ, hconv, hno, hblow,
    q, hq, hdist, hmissing, hquant⟩ := hescape eps heps (hle.trans (min_le_left _ _))
      sigma hsigma Phi hPhi X hnot
  let _ : PathConnectedSpace L.M := hL
  let _ : EMetricSpace L.M := L.emetricSpace
  let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
    (fun x y => riemannianEDistOf_ne_top L.metric x y)
  let ell : ℕ → ℝ := fun n => metricDistance ((X.term (f (phi n))).S.base.metric 0)
    (X.term (f (phi n))).basepoint (F.points (phi n))
  have hell : _root_.Filter.Tendsto ell _root_.Filter.atTop (𝓝 F.radius) := F.distance_limit.comp hphi.tendsto_atTop
  let Θ := maps.compSubseq phi hphi
  have hcanonical' (n : ℕ) : (C.metrics.compSubseq phi hphi).domain n =
      CanonicalMetricCompactness.canonicalSourceData Θ n := by
    change (C.metrics.domain (phi n)).compSubseq phi hphi n = _
    rw [hcanonical (phi n)]
    rfl
  have hstay (tau : _root_.Set.Ico 0 F.radius) : ∀ᶠ n in _root_.Filter.atTop, γ n tau ∈ Θ.target n := by
    filter_upwards [hphi.tendsto_atTop (hrT.eventually (eventually_gt_nhds tau.property.2)),
      hell.eventually (eventually_gt_nhds tau.property.2)] with n hn hn'
    change γ n tau ∈ maps.target (phi n)
    rw [htargets]
    change riemannianEDistOf ((X.term (f (phi n))).S.base.metric 0)
      (X.term (f (phi n))).basepoint (γ n tau) < ENNReal.ofReal (r (phi n))
    let _ : ConnectedSpace (X.term (f (phi n))).M := X.connected (f (phi n))
    have hdist' := (hγ n).2.2.2.2.2.2.1 0
      ⟨le_rfl, tau.property.1.trans hn'.le⟩ tau ⟨tau.property.1, hn'.le⟩
    rw [(hγ n).2.1] at hdist'
    simp only [zero_sub, abs_neg, abs_of_nonneg tau.property.1] at hdist'
    have heq := (ENNReal.ofReal_toReal (riemannianEDistOf_ne_top
      ((X.term (f (phi n))).S.base.metric 0) (X.term (f (phi n))).basepoint (γ n tau))).symm
    change _ = ENNReal.ofReal (metricDistance _ _ _) at heq
    rw [hdist'] at heq
    rw [heq]
    exact ENNReal.ofReal_lt_ofReal_iff (hr (phi n)).1 |>.mpr hn
  have hBquant (tau : _root_.Set.Ico 0 F.radius) (hR : 2 < metricScalarAt L.metric (g tau)) :
      B ^ 2 ≤ metricScalarAt L.metric (g tau) * (F.radius - tau) ^ 2 := by
    have hh := (pow_le_pow_left₀ hB.le
      ((le_max_left B (4 * D)).trans (le_max_right A (_root_.Max.max B (4 * D)))) 2).trans (hquant tau hR)
    simpa only [hdist tau] using hh
  have hnecks := hneck eps sigma Phi X (hle.trans (min_le_right _ _))
    (f ∘ phi) γ ell F.radius F.radius_pos hell
    (fun n => (hγ n).2.2.2.2.2.2.1) L Θ (C.metrics.compSubseq phi hphi) hcanonical' g
    hstay (fun tau => (hconv {tau} isCompact_singleton).tendsto_at (_root_.Set.mem_singleton tau))
    hblow hBquant
  refine ⟨f, hf, F, r, hr, hrT, L, hL, maps, C, hcanonical, htargets, hmetrics,
    hcompact, hbase, hsec, phi, γ, s, g, hphi, hg, hgbase, hγ, hconv, hno, hblow,
    q, hq, hdist, hmissing, ?_, ?_⟩
  · intro tau hR
    exact (pow_le_pow_left₀ hA (le_max_left A (_root_.Max.max B (4 * D))) 2).trans (hquant tau hR)
  · filter_upwards [hblow.eventually (_root_.Filter.eventually_gt_atTop 2), hnecks] with tau hQ hn
    have hQpos : 0 < metricScalarAt L.metric (g tau) := by linarith
    let R : ℝ := (F.radius - tau) / 2
    have hgap : 0 < F.radius - tau := sub_pos.mpr tau.property.2
    have hR : 0 < R := half_pos hgap
    have hradial : riemannianEDistOf L.metric L.basepoint (g tau) = ENNReal.ofReal tau := by
      have hh := hg.dist_eq ⟨0, le_rfl, F.radius_pos⟩ tau
      rw [hgbase, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
        abs_of_nonneg tau.property.1] at hh
      change _root_.EDist.edist L.basepoint (g tau) = _
      rw [edist_dist, hh]
    have hclosed : IsClosed (riemannianClosedBallOf L.metric (g tau) R) := by
      change IsClosed {y | _root_.EDist.edist (g tau) y ≤ ENNReal.ofReal R}
      exact isClosed_le (continuous_const.edist continuous_id) continuous_const
    have hKR : IsCompact (riemannianClosedBallOf L.metric (g tau) R) := by
      apply (hcompact (tau + R) (by linarith [tau.property.1])
        (by dsimp only [R]; linarith)).of_isClosed_subset hclosed
      intro y hy
      change riemannianEDistOf L.metric L.basepoint y ≤ ENNReal.ofReal (tau + R)
      calc
        _ ≤ riemannianEDistOf L.metric L.basepoint (g tau) +
            riemannianEDistOf L.metric (g tau) y := riemannianEDistOf_triangle _ _ _ _
        _ ≤ ENNReal.ofReal tau + ENNReal.ofReal R := add_le_add hradial.le hy
        _ = ENNReal.ofReal (tau + R) :=
          (ENNReal.ofReal_add tau.property.1 hR.le).symm
    have hDquant : (4 * D) ^ 2 ≤ metricScalarAt L.metric (g tau) * (F.radius - tau) ^ 2 := by
      have hh := (pow_le_pow_left₀ (by positivity : 0 ≤ 4 * D)
        ((le_max_right B (4 * D)).trans (le_max_right A (_root_.Max.max B (4 * D)))) 2).trans
        (hquant tau hQ)
      simpa only [hdist tau] using hh
    have hmul : 4 * D ≤ Real.sqrt (metricScalarAt L.metric (g tau)) * (F.radius - tau) := by
      apply (sq_le_sq₀ (by positivity : 0 ≤ 4 * D)
        (mul_nonneg (Real.sqrt_nonneg _) hgap.le)).mp
      rw [mul_pow (Real.sqrt (metricScalarAt L.metric (g tau))) (F.radius - tau) 2,
        Real.sq_sqrt hQpos.le]
      exact hDquant
    have hfit : D < Real.sqrt (metricScalarAt L.metric (g tau)) * R := by
      dsimp only [R]
      nlinarith
    apply htransport X.toFlowSequence (f ∘ phi) L Θ (C.metrics.compSubseq phi hphi)
      hcanonical' (g tau) hQpos R hR hKR hfit
    have heq : 2 * (neckModelTolerance alpha / 2) = neckModelTolerance alpha := by ring
    simpa only [heq] using hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminal_pointed_limit_with_missing_endpoint_and_spatialNecks then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminal_pointed_limit_with_missing_endpoint_and_spatialNecks"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminal_pointed_limit_with_missing_endpoint_and_spatialNecks ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminal_pointed_limit_with_missing_endpoint_and_spatialNecks

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end
