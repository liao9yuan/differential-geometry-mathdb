import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedWindowedSegment
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FixedDepthEnd
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.ConeExclusion
import Submission.DifferentialGeometry.Geometry.Neck.FiniteEnd

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter
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

private local instance pointedLimitRegular (L : PointedRiemannianManifold.{u, 0, 0} I3) :
    RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.pointedLimitRegular
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.pointedLimitRegular target :: scope.openDecls } }

theorem end_cone_exclusion_of_pos_depth_scale_lower_bounds {kappa : ℝ} (hkappa : 0 < kappa) :
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
      (∃ B : ℝ, ∀ᶠ n in _root_.Filter.atTop, metricScalarAt L.metric (x n : L.M) *
        _root_.Dist.dist (x n : UniformSpace.Completion W) q0 ^ 2 ≤ B) →
      Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation q0 d) → False := by
  obtain ⟨epsStar, hepsStar, hproduce⟩ :=
    exists_local_backward_limit_on_end_of_pos_depth_scale_lower_bounds.{u} hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X depth scale H0 S0 hH0 hS0 hdepth hscale
    hcarrier hregular hconnected orientation hcomplete hsource hnoncollapse hpinching hgood
    f L maps conv hcanonical W hW
  let _ : PathConnectedSpace W := hW
  dsimp only
  let _ : PseudoMetricSpace W := (L.metric.restrictOpen W).toPseudoMetricSpace
  let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
  intro q0 d hd hKd hcover x hx hQ c hc hlower hupper hcone
  obtain ⟨j, k, hj, _, hq, hratio, P, hpath, tau, htau, S, C, hS, hterminal,
    hsec, hscalar, hbase, r, hr, hK, hcapture, hdist⟩ :=
    hproduce eps heps hle sigma hsigma Phi hPhi X depth scale H0 S0 hH0 hS0
      hdepth hscale hcarrier hregular hconnected orientation hcomplete hsource
      hnoncollapse hpinching hgood f L maps conv hcanonical W hW
      q0 d hd hKd hcover x hx hQ c hc hlower
  let A := fun n => (X.term (f (k n))).S.scalar 0
    (maps.partialDiffeomorph (k n) (x (j n) : L.M))
  have hA (n : ℕ) : 0 < A n := lt_of_lt_of_le zero_lt_one (hq n)
  exact rescaled_end_cone_exclusion (L.metric.restrictOpen W) (fun _ _ => rfl)
    hcone.some x j hj A hA (fun n => metricScalarAt L.metric (x n : L.M))
    hQ hratio hc hlower hupper P hpath tau htau S (fun n y => C n y) hS hterminal
    hsec (by rw [hscalar]; norm_num) hbase r hr hK
    (hcapture.mono fun _ h => h.2) hdist

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.end_cone_exclusion_of_pos_depth_scale_lower_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.end_cone_exclusion_of_pos_depth_scale_lower_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.end_cone_exclusion_of_pos_depth_scale_lower_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.end_cone_exclusion_of_pos_depth_scale_lower_bounds

theorem finite_ray_exclusion_of_pos_depth_scale_lower_bounds {kappa : ℝ} (hkappa : 0 < kappa) :
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
      ∀ hL : PathConnectedSpace L.M,
      let _ : PathConnectedSpace L.M := hL
      let _ : EMetricSpace L.M := L.emetricSpace
      let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
        (fun x y => riemannianEDistOf_ne_top L.metric x y)
      ∀ b alpha : ℝ, 0 < b → 0 < alpha → alpha < 1 / 2000000 →
      (∀ (x : L.M) (v w : TangentSpace I3 x),
        0 ≤ metricRm04StandardAt L.metric x v w w v) →
      ∀ g : C(_root_.Set.Ico 0 b, L.M), Isometry g →
      _root_.Filter.Tendsto (fun t => metricScalarAt L.metric (g t))
        (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 b → ℝ) (𝓝 b)) _root_.Filter.atTop →
      ∀ q : UniformSpace.Completion L.M,
      _root_.Filter.Tendsto (fun t => (g t : UniformSpace.Completion L.M))
        (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 b → ℝ) (𝓝 b)) (𝓝 q) →
      (∀ᶠ t : _root_.Set.Ico 0 b in _root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 b → ℝ) (𝓝 b),
        Nonempty (SpatialNeck L.metric alpha (g t))) → False := by
  obtain ⟨epsStar, hepsStar, hexclude⟩ :=
    end_cone_exclusion_of_pos_depth_scale_lower_bounds.{u} hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X depth scale H0 S0 hH0 hS0 hdepth hscale
    hcarrier hregular hconnected orientation hcomplete hsource hnoncollapse hpinching hgood
    f L maps conv hcanonical hL
  let _ : PathConnectedSpace L.M := hL
  dsimp only
  let _ : EMetricSpace L.M := L.emetricSpace
  let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
    (fun x y => riemannianEDistOf_ne_top L.metric x y)
  intro b alpha hb ha hsmall hsec g hg hblow q hq hnecks
  obtain ⟨W, hW, hrest⟩ := exists_punctured_cone_end_of_spatial_necks L.metric
    (fun _ _ => rfl) hb ha hsmall hsec g hg hblow q hq hnecks
  let _ : PathConnectedSpace W := hW
  let mW : MetricSpace W :=
    let _ : PseudoMetricSpace W := (L.metric.restrictOpen W).toPseudoMetricSpace
    MetricSpace.ofT0PseudoMetricSpace W
  let _ : MetricSpace W := mW
  let _ : PseudoMetricSpace W := mW.toPseudoMetricSpace
  let _ : UniformSpace W := mW.toPseudoMetricSpace.toUniformSpace
  let eW : PseudoEMetricSpace W :=
    @PseudoMetricSpace.toPseudoEMetricSpace W mW.toPseudoMetricSpace
  let _ : WeakPseudoEMetricSpace W :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace W eW
  obtain ⟨qW, delta, hdelta, _, _, hcompact, hcover, x, times, _, _, hx, _,
    hQ, hlower, hupper, hcone⟩ := hrest
  have hQ' : _root_.Filter.Tendsto (fun n => metricScalarAt L.metric (x n : L.M)) _root_.Filter.atTop atTop := by
    simpa only [metricScalarAt_restrictOpen] using hQ
  have hlower' : ∀ᶠ n in _root_.Filter.atTop,
      ((2 * alpha)⁻¹) ^ 2 / 8 ≤ metricScalarAt L.metric (x n : L.M) *
        dist (x n : UniformSpace.Completion W) qW ^ 2 := by
    exact Eventually.of_forall fun n => by
      simpa only [metricScalarAt_restrictOpen] using hlower n
  have hupper' : ∃ B : ℝ, ∀ᶠ n in _root_.Filter.atTop,
      metricScalarAt L.metric (x n : L.M) *
        dist (x n : UniformSpace.Completion W) qW ^ 2 ≤ B := by
    obtain ⟨B, _, hB⟩ := hupper
    exact ⟨B, by simpa only [metricScalarAt_restrictOpen] using hB⟩
  exact hexclude eps heps hle sigma hsigma Phi hPhi X depth scale H0 S0 hH0 hS0
    hdepth hscale hcarrier hregular hconnected orientation hcomplete hsource
    hnoncollapse hpinching hgood f L maps conv hcanonical W hW qW delta hdelta
    hcompact hcover x hx hQ' (((2 * alpha)⁻¹) ^ 2 / 8) (by positivity)
    hlower' hupper' hcone

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_ray_exclusion_of_pos_depth_scale_lower_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_ray_exclusion_of_pos_depth_scale_lower_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_ray_exclusion_of_pos_depth_scale_lower_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_ray_exclusion_of_pos_depth_scale_lower_bounds

theorem finite_ray_exclusion_of_minimizing_segment_convergence {kappa : ℝ} (hkappa : 0 < kappa) :
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
      ∀ hL : PathConnectedSpace L.M,
      let _ : PathConnectedSpace L.M := hL
      let _ : EMetricSpace L.M := L.emetricSpace
      let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
        (fun x y => riemannianEDistOf_ne_top L.metric x y)
      ∀ b : ℝ, 0 < b →
      ∀ ell : ℕ → ℝ, _root_.Filter.Tendsto ell _root_.Filter.atTop (𝓝 b) →
      (∀ R : ℝ, 0 ≤ R → R < b →
        IsCompact (riemannianClosedBallOf L.metric L.basepoint R)) →
      ∀ gamma : ∀ n, ℝ → (X.term (f n)).M,
      (∀ n, gamma n 0 = (X.term (f n)).basepoint) →
      (∀ n, ∀ s ∈ _root_.Set.Icc 0 (ell n), ∀ t ∈ _root_.Set.Icc 0 (ell n),
        riemannianEDistOf ((X.term (f n)).S.base.metric 0) (gamma n s) (gamma n t) =
          ENNReal.ofReal |s - t|) →
      (∀ (x : L.M) (v w : TangentSpace I3 x),
        0 ≤ metricRm04StandardAt L.metric x v w w v) →
      ∀ g : C(_root_.Set.Ico 0 b, L.M), Isometry g →
      (∀ t : _root_.Set.Ico 0 b,
        _root_.Filter.Tendsto (fun n => (maps.partialDiffeomorph n).symm (gamma n t)) _root_.Filter.atTop (𝓝 (g t))) →
      _root_.Filter.Tendsto (fun n => (X.term (f n)).S.scalar 0 (gamma n (ell n))) _root_.Filter.atTop _root_.Filter.atTop →
      _root_.Filter.Tendsto (fun t => metricScalarAt L.metric (g t))
        (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 b → ℝ) (𝓝 b)) _root_.Filter.atTop →
      ∀ q : UniformSpace.Completion L.M,
      _root_.Filter.Tendsto (fun t => (g t : UniformSpace.Completion L.M))
        (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 b → ℝ) (𝓝 b)) (𝓝 q) →
      False := by
  obtain ⟨epsEnd, hepsEnd, hexclude⟩ :=
    finite_ray_exclusion_of_pos_depth_scale_lower_bounds.{u} hkappa
  obtain ⟨epsNeck, hepsNeck, hneck⟩ :=
    exists_spatial_necks_on_limit_segment_of_windowed_models.{u} kappa
      (alpha := 1 / 4000000) (by norm_num) (by norm_num)
  refine ⟨min epsEnd epsNeck, lt_min hepsEnd hepsNeck, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X depth scale H0 S0 hH0 hS0 hdepth hscale
    hcarrier hregular hconnected orientation hcomplete hsource hnoncollapse hpinching hgood
    f L maps conv hcanonical hL
  let _ : PathConnectedSpace L.M := hL
  dsimp only
  let _ : EMetricSpace L.M := L.emetricSpace
  let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
    (fun x y => riemannianEDistOf_ne_top L.metric x y)
  intro b hb ell hell hcompact gamma hstart hmin hsec g hg hconv hy hblow q hq
  have hmodels (tau : _root_.Set.Ico 0 b) : ∀ᶠ n in _root_.Filter.atTop,
      2 ≤ (X.term (f n)).S.scalar 0 (gamma n tau) →
        ∃ W : WindowedModelWitness eps kappa (X.term (f n)).S (gamma n tau) 0,
          (∀ s ∈ _root_.Set.Ioo (-modelDepth eps) 0,
            parabolicTime 0 ((X.term (f n)).S.scalar 0 (gamma n tau)) s ∈
              (X.interval (f n)).regular) ∧
          Nonempty (TangentOrientationSection W.model.M) := by
    apply Eventually.of_forall
    intro n hQ
    have hdepthpos : 0 < depth (f n) := hH0.trans_le (hdepth (f n))
    obtain ⟨W, o, _⟩ := hgood (f n) 0 ⟨by linarith only [hdepthpos], le_rfl⟩
      (gamma n tau) hQ
    refine ⟨W, ?_, ⟨o⟩⟩
    intro s hs
    have hQpos := W.scalar_pos
    have hstartWindow := W.window_mem (left_mem_Icc.mpr
      (sub_le_self 0 (inv_nonneg.mpr (mul_nonneg W.eps_pos.le hQpos.le))))
    rw [hcarrier (f n)] at hstartWindow
    rw [hregular (f n)]
    have hdivide : -(eps * (X.term (f n)).S.scalar 0 (gamma n tau))⁻¹ <
        s / ((X.term (f n)).S.scalar 0 (gamma n tau)) := by
      have hh := (div_lt_div_iff_of_pos_right hQpos).mpr hs.1
      simpa only [modelDepth, neg_div, div_eq_mul_inv, mul_inv_rev, mul_comm, neg_mul] using hh
    exact ⟨by dsimp only [parabolicTime]; linarith [hstartWindow.1],
      by dsimp only [parabolicTime]; linarith [div_neg_of_neg_of_pos hs.2 hQpos]⟩
  have hnecks := hneck X f L maps conv hcanonical b hb ell hell hcompact gamma
    hstart hmin g hconv hy hblow eps (hle.trans (min_le_right _ _)) hmodels
  exact hexclude eps heps (hle.trans (min_le_left _ _)) sigma hsigma Phi hPhi X depth scale
    H0 S0 hH0 hS0 hdepth hscale hcarrier hregular hconnected orientation hcomplete hsource
    hnoncollapse hpinching hgood f L maps conv hcanonical hL b (1 / 4000000)
    hb (by norm_num) (by norm_num) hsec g hg hblow q hq hnecks

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_ray_exclusion_of_minimizing_segment_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_ray_exclusion_of_minimizing_segment_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_ray_exclusion_of_minimizing_segment_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finite_ray_exclusion_of_minimizing_segment_convergence

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
