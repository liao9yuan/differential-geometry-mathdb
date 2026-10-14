import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardTerminalGeometry
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarEscape
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Curves
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Connected
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scalar
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedCurvatureOperator
import Submission.DifferentialGeometry.Geometry.Curvature.Nonnegative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instNeZeroNatFinrankRealE3 : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instNeZeroNatFinrankRealE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instNeZeroNatFinrankRealE3 target :: scope.openDecls } }

theorem exists_standard_terminal_isometric_segment_of_scalar_escape
    (S : ℕ → PartialStandardSolution) (time : ℕ → ℝ) (point y : ℕ → E3)
    {tau rho : ℝ} (htau : 0 < tau) (hrho : 0 < rho)
    (htime : ∀ i, time i ∈ (S i).domain ∧ tau ≤ time i ∧ time i < 1)
    (hscalar : ∀ r : ℝ, 0 < r → r < rho → ∃ A : ℝ, ∀ᶠ i in _root_.Filter.atTop,
      ∀ z ∈ riemannianClosedBallOf ((S i).metric (time i)) (point i) r,
        metricScalarAt ((S i).metric (time i)) z ≤ A)
    (hdistance : _root_.Filter.Tendsto (fun i => (riemannianEDistOf ((S i).metric (time i))
      (point i) (y i)).toReal) _root_.Filter.atTop (𝓝 rho))
    (hblowup : _root_.Filter.Tendsto (fun i => metricScalarAt ((S i).metric (time i)) (y i)) _root_.Filter.atTop _root_.Filter.atTop) :
    let X : PointedRiemannianSeq (𝓡 3) :=
      ⟨fun i => ((S i).pointedFlow.atTime (time i)).repoint (point i)⟩
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ radius : ℕ → ℝ,
      (∀ k, 0 < radius k ∧ radius k < rho) ∧ _root_.Filter.Tendsto radius _root_.Filter.atTop (𝓝 rho) ∧
      ∃ L : PointedRiemannianManifold (𝓡 3), ∃ _ : PathConnectedSpace L.M,
      ∃ maps : PointedRiemannianConvergenceMaps X L f,
      ∃ C : PointedRiemannianConverges X L f maps,
        (∀ k, C.metrics.domain k = CanonicalMetricCompactness.canonicalSourceData maps k) ∧
        (∀ k, maps.target k = riemannianBallOf ((S (f k)).metric (time (f k)))
          (point (f k)) (radius k)) ∧
        (∀ x : L.M, riemannianEDistOf L.metric L.basepoint x < ENNReal.ofReal rho) ∧
        (∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          ∀ x ∈ maps.source k, ∀ v : TangentSpace (𝓡 3) x,
            (1 - eps) * L.metric.inner x v v ≤
              ((S (f k)).metric (time (f k))).inner (maps.partialDiffeomorph k x)
                (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v)
                (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v) ∧
              ((S (f k)).metric (time (f k))).inner (maps.partialDiffeomorph k x)
                (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v)
                (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph k) x v) ≤
              (1 + eps) * L.metric.inner x v v) ∧
        (∀ r : ℝ, 0 ≤ r → r < rho →
          IsCompact (riemannianClosedBallOf L.metric L.basepoint r)) ∧
        (∀ (x : L.M) (v w : TangentSpace (𝓡 3) x),
          0 ≤ metricRm04StandardAt L.metric x v w w v) ∧
        let _ : EMetricSpace L.M := L.emetricSpace
        let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
          (fun x z => riemannianEDistOf_ne_top L.metric x z)
        ∃ (phi : ℕ → ℕ) (gamma : ℕ → ℝ → E3) (g : C(_root_.Set.Ico 0 rho, L.M)),
          StrictMono phi ∧ Isometry g ∧ g ⟨0, le_rfl, hrho⟩ = L.basepoint ∧
          (∀ n,
            let ell := (riemannianEDistOf ((S (f (phi n))).metric (time (f (phi n))))
              (point (f (phi n))) (y (f (phi n)))).toReal
            gamma n 0 = point (f (phi n)) ∧ gamma n ell = y (f (phi n)) ∧
              ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ (gamma n) ∧
              ∀ s ∈ _root_.Set.Icc 0 ell, ∀ t ∈ _root_.Set.Icc 0 ell,
                riemannianEDistOf ((S (f (phi n))).metric (time (f (phi n))))
                  (gamma n s) (gamma n t) = ENNReal.ofReal |s - t|) ∧
          (∀ A : Set (_root_.Set.Ico 0 rho), IsCompact A → TendstoUniformlyOn
            (fun n (t : _root_.Set.Ico 0 rho) => (maps.partialDiffeomorph (phi n)).symm (gamma n t))
            g _root_.Filter.atTop A) ∧
          (∀ t : _root_.Set.Ico 0 rho, ∀ᶠ n in _root_.Filter.atTop, gamma n t ∈ maps.target (phi n)) ∧
          (∀ t : _root_.Set.Ico 0 rho, _root_.Filter.Tendsto
            (fun n => metricScalarAt ((S (f (phi n))).metric (time (f (phi n)))) (gamma n t))
            _root_.Filter.atTop (𝓝 (metricScalarAt L.metric (g t)))) ∧
          _root_.Filter.Tendsto (fun t => metricScalarAt L.metric (g t))
            (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 rho → ℝ) (𝓝 rho)) _root_.Filter.atTop ∧
          _root_.Filter.Tendsto g (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 rho → ℝ) (𝓝 rho)) (_root_.Filter.cocompact L.M) ∧
          (∀ x : L.M, ¬ _root_.Filter.Tendsto g
            (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 x)) ∧
          ∃ q : UniformSpace.Completion L.M,
            _root_.Filter.Tendsto (fun t => (g t : UniformSpace.Completion L.M))
              (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 q) ∧
            (∀ t : _root_.Set.Ico 0 rho, _root_.Dist.dist q (g t : UniformSpace.Completion L.M) = rho - t) ∧
            q ∉ _root_.Set.range (fun x : L.M => (x : UniformSpace.Completion L.M)) := by
  let X : PointedRiemannianSeq (𝓡 3) :=
    ⟨fun i => ((S i).pointedFlow.atTime (time i)).repoint (point i)⟩
  obtain ⟨f, hf, radius, hradius, hradiusconv, L, maps, C, hcanonical, htargets,
    hradial, hmetrics, hcompact⟩ :=
    exists_standard_terminal_pointed_convergence_within_radius S time point htau hrho htime hscalar
  have hL : PathConnectedSpace L.M :=
    maps.path_connected_space_of_frequently_path_connected_targets
      (Eventually.frequently (Eventually.of_forall fun n => by
        rw [htargets n]
        exact isPathConnected_riemannianBallOf ((S (f n)).metric (time (f n)))
          (point (f n)) (hradius n).1))
  let _ : PathConnectedSpace L.M := hL
  have hoperator : ∀ x : L.M, metricAlgebraicCurvatureTensorAt L.metric x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := 𝓡 3) := by
    apply Perelman.KappaSolutions.curvatureOperator_nonnegative_of_canonical_metricCGConvergence
      C.metrics hcanonical
    intro K hK
    exact Eventually.of_forall fun k z _ _ =>
      (S (f k)).curvatureOperator_nonnegative (time (f k)) (htime (f k)).1 (maps.map k z)
  have hsec (x : L.M) (v w : TangentSpace (𝓡 3) x) :
      0 ≤ metricRm04StandardAt L.metric x v w w v := by
    have hh := (mem_algebraicCurvatureOperatorNonnegativeCone.mp (hoperator x))
      1 (fun _ => 1) (fun _ => v) (fun _ => w)
    simpa only [algebraicCurvatureOperatorQuadraticEval, Fin.sum_univ_one, one_mul,
      tensor04StandardAt_apply, metricAlgebraicCurvatureTensorAt_coe,
      metricRm04StandardAt_apply] using hh
  have hlower (eps : ℝ) (heps : 0 < eps) : ∀ᶠ n in _root_.Filter.atTop,
      ∀ x ∈ maps.source n, ∀ v : TangentSpace (𝓡 3) x,
        (1 - eps) * L.metric.inner x v v ≤
          ((S (f n)).metric (time (f n))).inner (maps.partialDiffeomorph n x)
            (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph n) x v)
            (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph n) x v) := by
    obtain ⟨N, hN⟩ := hmetrics eps heps
    filter_upwards [_root_.Filter.eventually_ge_atTop N] with n hn
    exact fun x hx v => (hN n hn x hx v).1
  have hupper : ∀ K : Set L.M, IsCompact K → ∀ D : ℝ, 1 < D → ∀ᶠ n in _root_.Filter.atTop,
      ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
        ((S (f n)).metric (time (f n))).inner (maps.partialDiffeomorph n x)
          (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph n) x v)
          (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph n) x v) ≤ D ^ 2 * L.metric.inner x v v := by
    intro K hK D hD
    obtain ⟨N, hN⟩ := Perelman.KappaSolutions.exists_pointed_full_ambient_quadratic_control C.metrics
      (fun n => by rw [hcanonical n]; rfl) K hK (D ^ 2 - 1) (by nlinarith)
    filter_upwards [_root_.Filter.eventually_ge_atTop N] with n hn
    intro x hx v
    have hh := (abs_le.mp ((hN n hn).2 x hx v)).2
    change ((S (f n)).metric (time (f n))).inner (maps.partialDiffeomorph n x)
      (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph n) x v)
      (mfderiv (𝓡 3) (𝓡 3) (maps.partialDiffeomorph n) x v) - L.metric.inner x v v ≤
        (D ^ 2 - 1) * L.metric.inner x v v at hh
    nlinarith
  let _ : EMetricSpace L.M := L.emetricSpace
  let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
    (fun x z => riemannianEDistOf_ne_top L.metric x z)
  obtain ⟨gamma, hgamma, phi, g, hphi, hg, hgbase, hconv, hescape, hmissing⟩ :=
    maps.exists_isometric_segment_subseq_limit_with_missing_endpoint_of_complete
      (fun n => (S (f n)).complete (time (f n)) (htime (f n)).1)
      (fun _ => by change PreconnectedSpace E3; infer_instance)
      hrho radius (fun n => (hradius n).1) hradiusconv (fun n => y (f n))
      (hdistance.comp hf.tendsto_atTop) (fun n => (htargets n).symm.subset)
      hlower hupper hcompact hradial
  change ℕ → ℝ → E3 at gamma
  let ell (n : ℕ) := (riemannianEDistOf ((S (f n)).metric (time (f n)))
    (point (f n)) (y (f n))).toReal
  have hell : _root_.Filter.Tendsto ell _root_.Filter.atTop (𝓝 rho) := hdistance.comp hf.tendsto_atTop
  have hzero (n : ℕ) : gamma n 0 = point (f n) := (hgamma n).1
  have hend (n : ℕ) : gamma n (ell n) = y (f n) := (hgamma n).2.1
  have hmin (n : ℕ) (s : ℝ) (hs : s ∈ _root_.Set.Icc 0 (ell n))
      (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 (ell n)) :
      riemannianEDistOf ((S (f n)).metric (time (f n))) (gamma n s) (gamma n t) =
        ENNReal.ofReal |s - t| := (hgamma n).2.2.2 s hs t ht
  have hstay (t : _root_.Set.Ico 0 rho) : ∀ᶠ n in _root_.Filter.atTop, gamma (phi n) t ∈ maps.target (phi n) := by
    filter_upwards [hphi.tendsto_atTop (hradiusconv.eventually_const_lt t.property.2),
      hphi.tendsto_atTop (hell.eventually_const_lt t.property.2)] with n hn hn'
    rw [htargets]
    change riemannianEDistOf ((S (f (phi n))).metric (time (f (phi n))))
      (point (f (phi n))) (gamma (phi n) t) < ENNReal.ofReal (radius (phi n))
    have hh := hmin (phi n) 0 ⟨le_rfl, t.property.1.trans hn'.le⟩
      t ⟨t.property.1, hn'.le⟩
    rw [hzero] at hh
    simp only [zero_sub, abs_neg, abs_of_nonneg t.property.1] at hh
    rw [hh]
    exact (ENNReal.ofReal_lt_ofReal_iff (hradius (phi n)).1).mpr hn
  let maps' := maps.compSubseq phi hphi
  have hcanonical' (n : ℕ) : (C.metrics.compSubseq phi hphi).domain n =
      CanonicalMetricCompactness.canonicalSourceData maps' n := by
    change (C.metrics.domain (phi n)).compSubseq phi hphi n = _
    rw [hcanonical (phi n)]
    rfl
  have hlimit (t : _root_.Set.Ico 0 rho) : _root_.Filter.Tendsto
      (fun n => metricScalarAt ((S (f (phi n))).metric (time (f (phi n)))) (gamma (phi n) t))
      atTop (𝓝 (metricScalarAt L.metric (g t))) :=
    pointedScalar_tendsto_of_inverse_tendsto (C.metrics.compSubseq phi hphi) hcanonical'
      (fun n => gamma (phi n) t) (hstay t)
      ((hconv {t} isCompact_singleton).tendsto_at (_root_.Set.mem_singleton t))
  have hdistend (t : _root_.Set.Ico 0 rho) : ∀ᶠ n in _root_.Filter.atTop,
      riemannianEDistOf ((S (f (phi n))).metric (time (f (phi n))))
        (gamma (phi n) t) (gamma (phi n) (ell (phi n))) ≤ ENNReal.ofReal (ell (phi n) - t) := by
    filter_upwards [hphi.tendsto_atTop (hell.eventually_const_lt t.property.2)] with n hn
    change (t : ℝ) < ell (phi n) at hn
    have hh := hmin (phi n) t ⟨t.property.1, hn.le⟩ (ell (phi n))
      ⟨t.property.1.trans hn.le, le_rfl⟩
    simpa only [abs_of_nonpos (sub_nonpos.mpr hn.le), neg_sub] using hh.le
  have hscalarblow : _root_.Filter.Tendsto (fun t => metricScalarAt L.metric (g t))
      (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 rho → ℝ) (𝓝 rho)) atTop := by
    apply standard_scalar_limit_tendsto_atTop_of_endpoint_blowup
      (fun n => S (f (phi n))) (fun n => time (f (phi n))) htau
      (Eventually.of_forall fun n => htime (f (phi n))) rho (ell ∘ phi)
      (hell.comp hphi.tendsto_atTop) (fun n => gamma (phi n)) ?_ hdistend _ hlimit
    have hh := hblowup.comp (hf.comp hphi).tendsto_atTop
    convert hh using 1
    funext n
    exact congrArg (metricScalarAt ((S (f (phi n))).metric (time (f (phi n))))) (hend (phi n))
  refine ⟨f, hf, radius, hradius, hradiusconv, L, hL, maps, C, hcanonical, htargets,
    hradial, hmetrics, hcompact, hsec, phi, (fun n => gamma (phi n)), g,
    hphi, hg, hgbase, (fun n => hgamma (phi n)), hconv, hstay, hlimit,
    hscalarblow, hescape, hmissing, ?_⟩
  have hbound (x : L.M) : _root_.EDist.edist (g ⟨0, le_rfl, hrho⟩) x < ENNReal.ofReal (rho - 0) := by
    rw [hgbase, sub_zero]
    exact hradial x
  exact hg.exists_completion_right_endpoint_not_mem_range hrho hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_standard_terminal_isometric_segment_of_scalar_escape then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_standard_terminal_isometric_segment_of_scalar_escape"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_standard_terminal_isometric_segment_of_scalar_escape ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_standard_terminal_isometric_segment_of_scalar_escape

end DifferentialGeometry.PDE.RicciFlow
