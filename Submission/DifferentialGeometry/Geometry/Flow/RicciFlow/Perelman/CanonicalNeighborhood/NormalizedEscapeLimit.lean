import Submission.DifferentialGeometry.Geometry.Curvature.DimensionThree.ScalarNonnegativeOfRicciNonnegative
import Submission.DifferentialGeometry.Geometry.Comparison.BonnetMyers.SectionalRicci
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelCurvaturePropagation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedReindexing
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedEscapeGeodesic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedLocalCompactness
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Curves
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Connected
import Submission.DifferentialGeometry.Geometry.Metric.Segment
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence

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

private theorem abs_scalar_tendsto_atTop_of_escaping_curves {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ f : ℕ → ℕ, StrictMono f → ∀ p : ∀ n, (X.term (f n)).M,
              _root_.Filter.Tendsto (fun n => (X.term (f n)).S.scalar 0 (p n)) _root_.Filter.atTop _root_.Filter.atTop →
              ∀ (rho : ℝ) (ell : ℕ → ℝ), _root_.Filter.Tendsto ell _root_.Filter.atTop (𝓝 rho) →
                ∀ (γ : ∀ n, _root_.Set.Ico 0 rho → (X.term (f n)).M),
                  (∀ t : _root_.Set.Ico 0 rho, ∀ᶠ n in _root_.Filter.atTop,
                    riemannianEDistOf ((X.term (f n)).S.base.metric 0) (γ n t) (p n) ≤
                      ENNReal.ofReal (ell n - t)) →
                ∀ (L : PointedRiemannianManifold.{u, 0, 0} (I := I3))
                  (maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f)
                  (C : MetricConvergenceData maps),
                  (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData maps n) →
                  ∀ g : _root_.Set.Ico 0 rho → L.M,
                    (∀ t : _root_.Set.Ico 0 rho, ∀ᶠ n in _root_.Filter.atTop, γ n t ∈ maps.target n) →
                    (∀ t : _root_.Set.Ico 0 rho, _root_.Filter.Tendsto
                      (fun n => (maps.partialDiffeomorph n).symm (γ n t)) _root_.Filter.atTop (𝓝 (g t))) →
                    _root_.Filter.Tendsto (fun t => |metricScalarAt L.metric (g t)|)
                      (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 rho → ℝ) (𝓝 rho)) atTop := by
  obtain ⟨epsStar, c, hepsStar, hc, hsep⟩ := eventually_edist_gt_of_scalar_tendsto_atTop hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X f hf p hp rho ell hell γ hdist L maps C hcanonical
    g hstay hconv
  apply tendsto_atTop.mpr
  intro B
  by_cases hB : B ≤ 0
  · exact Eventually.of_forall fun t => hB.trans (abs_nonneg _)
  have hBpos : 0 < B := lt_of_not_ge hB
  let d : ℝ := c / Real.sqrt (2 + B)
  have hd : 0 < d := div_pos hc (Real.sqrt_pos.mpr (by linarith))
  have hgap : _root_.Filter.Tendsto (fun t : _root_.Set.Ico 0 rho => rho - (t : ℝ))
      (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 0) := by
    simpa only [sub_self] using ((tendsto_const_nhds (x := rho)).sub
      (_root_.Filter.tendsto_comap : _root_.Filter.Tendsto (Subtype.val : _root_.Set.Ico 0 rho → ℝ) _ (𝓝 rho)))
  filter_upwards [hgap.eventually (eventually_lt_nhds hd)] with t ht
  by_contra hR
  have hRlt : |metricScalarAt L.metric (g t)| < B := lt_of_not_ge hR
  have hscalar := pointedScalar_tendsto_of_inverse_tendsto C hcanonical
    (fun n => γ n t) (hstay t) (hconv t)
  have hA : ∀ᶠ n in _root_.Filter.atTop, |(X.term (f n)).S.scalar 0 (γ n t)| ≤ B + 1 := by
    have hh := hscalar.abs.eventually (eventually_lt_nhds (hRlt.trans (lt_add_one B)))
    exact hh.mono fun _ h => h.le
  have hs : ∀ᶠ n in _root_.Filter.atTop, (0 : ℝ) ∈ _root_.Set.Icc (-((X.reindex f hf).depth n / 2)) 0 :=
    Eventually.of_forall fun n => ⟨by
      change -(X.depth (f n) / 2) ≤ 0
      linarith [X.depth_pos (f n)], le_rfl⟩
  have hseparation := hsep eps heps hle sigma hsigma Phi hPhi (X.reindex f hf)
    (fun _ => 0) (fun n => γ n t) p (B + 1) hs hA hp
  have hbound : ∀ᶠ n in _root_.Filter.atTop, ENNReal.ofReal d ≤ ENNReal.ofReal (ell n - t) := by
    filter_upwards [hseparation, hdist t] with n hn hn'
    have heq : 1 + (B + 1) = 2 + B := by ring
    rw [heq] at hn
    exact hn.le.trans hn'
  have hlimit : _root_.Filter.Tendsto (fun n => ENNReal.ofReal (ell n - t)) _root_.Filter.atTop
      (𝓝 (ENNReal.ofReal (rho - t))) := (ENNReal.continuous_ofReal.tendsto (rho - t)).comp (hell.sub_const (t : ℝ))
  have hle' := ge_of_tendsto hlimit hbound
  have hreal : d ≤ rho - t := (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr t.property.2.le)).mp hle'
  exact (not_le.mpr ht) hreal

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.abs_scalar_tendsto_atTop_of_escaping_curves
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.abs_scalar_tendsto_atTop_of_escaping_curves target :: scope.openDecls } }

theorem not_tendsto_edist_zero_of_scalar_tendsto_atTop {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ f : ℕ → ℕ, StrictMono f → ∀ p : ∀ n, (X.term (f n)).M,
              _root_.Filter.Tendsto (fun n => (X.term (f n)).S.scalar 0 (p n)) _root_.Filter.atTop _root_.Filter.atTop →
              ∀ (L : PointedRiemannianManifold.{u, 0, 0} (I := I3))
                (maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f)
                (C : MetricConvergenceData maps),
                (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData maps n) →
                ∀ x : L.M, ¬ _root_.Filter.Tendsto (fun n => riemannianEDistOf
                  ((X.term (f n)).S.base.metric 0) (p n) (maps.partialDiffeomorph n x))
                    atTop (𝓝 0) := by
  obtain ⟨epsStar, hepsStar, hbound⟩ := eventually_scalar_le_of_edist_tendsto_zero hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X f hf p hp L maps C hcanonical x hd
  have hc := KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains C hcanonical x
  let A : ℝ := |metricScalarAt L.metric x| + 1
  have hA : ∀ᶠ n in _root_.Filter.atTop, |(X.term (f n)).S.scalar 0 (maps.partialDiffeomorph n x)| ≤ A := by
    have hh := hc.abs.eventually (eventually_lt_nhds (lt_add_one |metricScalarAt L.metric x|))
    filter_upwards [hh] with n hn
    exact hn.le
  have hd' : _root_.Filter.Tendsto (fun n => riemannianEDistOf ((X.term (f n)).S.base.metric 0)
      (maps.partialDiffeomorph n x) (p n)) _root_.Filter.atTop (𝓝 0) := by
    exact hd.congr' (Eventually.of_forall fun n => riemannianEDistOf_comm _ _ _)
  have hb := hbound eps heps hle sigma hsigma Phi hPhi (X.reindex f hf)
    (fun _ => 0) (fun n => maps.partialDiffeomorph n x) p A
    (Eventually.of_forall fun n => ⟨by
      change -(X.depth (f n) / 2) ≤ 0
      linarith [X.depth_pos (f n)], le_rfl⟩) hA hd'
  obtain ⟨n, hn, hn'⟩ := (hb.and (hp.eventually (_root_.Filter.eventually_gt_atTop (4 * (1 + A))))).exists
  exact (not_le.mpr hn') hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_tendsto_edist_zero_of_scalar_tendsto_atTop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_tendsto_edist_zero_of_scalar_tendsto_atTop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_tendsto_edist_zero_of_scalar_tendsto_atTop ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.not_tendsto_edist_zero_of_scalar_tendsto_atTop

private theorem exists_geodesic_tail_curves
    {eps kappa sigma c : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (f : ℕ → ℕ) (hf : StrictMono f) (p : ∀ n, (X.term (f n)).M)
    (hp : _root_.Filter.Tendsto (fun n => (X.term (f n)).S.scalar 0 (p n)) _root_.Filter.atTop _root_.Filter.atTop)
    (hcurves : ∀ᶠ i in _root_.Filter.atTop, ∀ y : (X.term i).M, 12 < (X.term i).S.scalar 0 y →
      let L := metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y
      ∃ (γ : ℝ → (X.term i).M) (s : ℝ), s ∈ _root_.Set.Ico 0 L ∧
        γ 0 = (X.term i).basepoint ∧ γ L = y ∧ ContMDiff 𝓘(ℝ, ℝ) I3 ∞ γ ∧
        (∀ t, IsGeodesicAt ((X.term i).S.base.metric 0) γ t) ∧
        (∀ t, ((X.term i).S.base.metric 0).inner (γ t)
          (mfderiv 𝓘(ℝ, ℝ) I3 γ t 1) (mfderiv 𝓘(ℝ, ℝ) I3 γ t 1) = 1) ∧
        (∀ t ∈ _root_.Set.Icc 0 L, ∀ v ∈ _root_.Set.Icc 0 L,
          metricDistance ((X.term i).S.base.metric 0) (γ t) (γ v) = |t - v|) ∧
        (X.term i).S.scalar 0 (γ s) = 2 ∧
        (∀ t ∈ _root_.Set.Ioc s L, 2 < (X.term i).S.scalar 0 (γ t)) ∧ c < L - s) :
    ∃ N : ℕ, ∃ (γ : ∀ n, ℝ → (X.term (f (N + n))).M) (s : ℕ → ℝ), ∀ n,
      let L := metricDistance ((X.term (f (N + n))).S.base.metric 0)
        (X.term (f (N + n))).basepoint (p (N + n))
      s n ∈ _root_.Set.Ico 0 L ∧ γ n 0 = (X.term (f (N + n))).basepoint ∧
        γ n L = p (N + n) ∧ ContMDiff 𝓘(ℝ, ℝ) I3 ∞ (γ n) ∧
        (∀ t, IsGeodesicAt ((X.term (f (N + n))).S.base.metric 0) (γ n) t) ∧
        (∀ t, ((X.term (f (N + n))).S.base.metric 0).inner (γ n t)
          (mfderiv 𝓘(ℝ, ℝ) I3 (γ n) t 1) (mfderiv 𝓘(ℝ, ℝ) I3 (γ n) t 1) = 1) ∧
        (∀ t ∈ _root_.Set.Icc 0 L, ∀ v ∈ _root_.Set.Icc 0 L,
          metricDistance ((X.term (f (N + n))).S.base.metric 0) (γ n t) (γ n v) = |t - v|) ∧
        (X.term (f (N + n))).S.scalar 0 (γ n (s n)) = 2 ∧
        (∀ t ∈ _root_.Set.Ioc (s n) L, 2 < (X.term (f (N + n))).S.scalar 0 (γ n t)) ∧
        c < L - s n := by
  have hevent := (hp.eventually (_root_.Filter.eventually_gt_atTop 12)).and (hf.tendsto_atTop hcurves)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  have hchoice (n : ℕ) := (hN (N + n) (Nat.le_add_right N n)).2 (p (N + n))
    (hN (N + n) (Nat.le_add_right N n)).1
  choose γ s hs using hchoice
  exact ⟨N, γ, s, hs⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_geodesic_tail_curves
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_geodesic_tail_curves target :: scope.openDecls } }

private theorem scalar_remaining_length_lower_bound_of_escaping_curves {r : ℝ} (hr : 0 ≤ r) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, eps ≤ epsStar →
      ∀ (kappa sigma : ℝ) (Phi : ℝ → ℝ) (X : NormalizedSequence.{u} eps kappa sigma Phi)
        (f : ℕ → ℕ), StrictMono f → ∀ p : ∀ n, (X.term (f n)).M,
        _root_.Filter.Tendsto (fun n => (X.term (f n)).S.scalar 0 (p n)) _root_.Filter.atTop _root_.Filter.atTop →
        ∀ (rho : ℝ) (ell : ℕ → ℝ), _root_.Filter.Tendsto ell _root_.Filter.atTop (𝓝 rho) →
          ∀ (γ : ∀ n, _root_.Set.Ico 0 rho → (X.term (f n)).M),
            (∀ t : _root_.Set.Ico 0 rho, ∀ᶠ n in _root_.Filter.atTop,
              riemannianEDistOf ((X.term (f n)).S.base.metric 0) (γ n t) (p n) ≤
                ENNReal.ofReal (ell n - t)) →
          ∀ (L : PointedRiemannianManifold.{u, 0, 0} (I := I3))
            (maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f)
            (C : MetricConvergenceData maps),
            (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData maps n) →
            ∀ g : _root_.Set.Ico 0 rho → L.M,
              (∀ t : _root_.Set.Ico 0 rho, ∀ᶠ n in _root_.Filter.atTop, γ n t ∈ maps.target n) →
              (∀ t : _root_.Set.Ico 0 rho, _root_.Filter.Tendsto
                (fun n => (maps.partialDiffeomorph n).symm (γ n t)) _root_.Filter.atTop (𝓝 (g t))) →
              ∀ t : _root_.Set.Ico 0 rho, 2 < metricScalarAt L.metric (g t) →
                r ^ 2 ≤ metricScalarAt L.metric (g t) * (rho - t) ^ 2 := by
  obtain ⟨epsStar, hepsStar, hsep⟩ := exists_curvature_radius_lower_bound_of_scalar_tendsto_atTop.{u} hr
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps kappa sigma Phi X f hf p hp rho ell hell γ hdist L maps C hcanonical
    g hstay hconv t hR
  have hscalar := pointedScalar_tendsto_of_inverse_tendsto C hcanonical
    (fun n => γ n t) (hstay t) (hconv t)
  have hbound := hsep eps heps kappa sigma Phi (X.reindex f hf) (fun _ => 0)
    (fun n => γ n t) p (metricScalarAt L.metric (g t)) (rho - t) (fun n => ell n - t)
    (Eventually.of_forall fun n => ⟨by
      change -(X.depth (f n)) ≤ 0
      linarith [X.depth_pos (f n)], le_rfl⟩)
    hR hscalar hp (hell.sub_const (t : ℝ)) (hdist t)
  have hRpos : 0 < metricScalarAt L.metric (g t) := by linarith
  have hroot : 0 < Real.sqrt (metricScalarAt L.metric (g t)) := Real.sqrt_pos.mpr hRpos
  have hmul := (div_le_iff₀ hroot).mp hbound
  have hsq := pow_le_pow_left₀ hr hmul 2
  rw [mul_pow, Real.sq_sqrt hRpos.le] at hsq
  simpa only [mul_comm] using hsq

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_remaining_length_lower_bound_of_escaping_curves
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.scalar_remaining_length_lower_bound_of_escaping_curves target :: scope.openDecls } }


theorem exists_isometric_curve_with_missing_endpoint {kappa : ℝ} (hkappa : 0 < kappa)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ epsStar c : ℝ, 0 < epsStar ∧ 0 < c ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ f : ℕ → ℕ, StrictMono f → ∀ p : ∀ n, (X.term (f n)).M,
              _root_.Filter.Tendsto (fun n => (X.term (f n)).S.scalar 0 (p n)) _root_.Filter.atTop _root_.Filter.atTop →
              ∀ (rho : ℝ) (hrho : 0 < rho),
                _root_.Filter.Tendsto (fun n => metricDistance ((X.term (f n)).S.base.metric 0)
                  (X.term (f n)).basepoint (p n)) _root_.Filter.atTop (𝓝 rho) →
                ∀ (L : PointedRiemannianManifold.{u, 0, 0} (I := I3))
                  (maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f)
                  (C : MetricConvergenceData maps),
                  (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData maps n) →
                  ∀ r : ℕ → ℝ, (∀ n, 0 < r n) → _root_.Filter.Tendsto r _root_.Filter.atTop (𝓝 rho) →
                    (∀ n, riemannianBallOf ((X.term (f n)).S.base.metric 0)
                      (X.term (f n)).basepoint (r n) ⊆ maps.target n) →
                    (∀ eta : ℝ, 0 < eta → ∀ᶠ n in _root_.Filter.atTop,
                      ∀ x ∈ maps.source n, ∀ v : TangentSpace I3 x,
                        (1 - eta) * L.metric.inner x v v ≤
                          ((X.term (f n)).S.base.metric 0).inner (maps.partialDiffeomorph n x)
                            (mfderiv I3 I3 (maps.partialDiffeomorph n) x v)
                            (mfderiv I3 I3 (maps.partialDiffeomorph n) x v)) →
                    (∀ R : ℝ, 0 ≤ R → R < rho →
                      IsCompact (riemannianClosedBallOf L.metric L.basepoint R)) →
                    let _ : EMetricSpace L.M := L.emetricSpace
                    ∃ phi : ℕ → ℕ, ∃ (γ : ∀ n, ℝ → (X.term (f (phi n))).M)
                      (s : ℕ → ℝ) (g : C(_root_.Set.Ico 0 rho, L.M)),
                      StrictMono phi ∧ Isometry g ∧ g ⟨0, le_rfl, hrho⟩ = L.basepoint ∧
                      (∀ n,
                        let ell := metricDistance ((X.term (f (phi n))).S.base.metric 0)
                          (X.term (f (phi n))).basepoint (p (phi n))
                        s n ∈ _root_.Set.Ico 0 ell ∧ γ n 0 = (X.term (f (phi n))).basepoint ∧
                          γ n ell = p (phi n) ∧ ContMDiff 𝓘(ℝ, ℝ) I3 ∞ (γ n) ∧
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
                      (∀ A : Set (_root_.Set.Ico 0 rho), IsCompact A → TendstoUniformlyOn
                        (fun n (t : _root_.Set.Ico 0 rho) => (maps.partialDiffeomorph (phi n)).symm (γ n t))
                        g _root_.Filter.atTop A) ∧
                      (∀ x : L.M, ¬ _root_.Filter.Tendsto g
                        (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 x)) ∧
                      _root_.Filter.Tendsto (fun t => |metricScalarAt L.metric (g t)|)
                        (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 rho → ℝ) (𝓝 rho)) _root_.Filter.atTop ∧
                      ∀ t : _root_.Set.Ico 0 rho, 2 < metricScalarAt L.metric (g t) →
                        A ^ 2 ≤ metricScalarAt L.metric (g t) * (rho - t) ^ 2 := by
  obtain ⟨epsGeo, c, hepsGeo, hc, hgeo⟩ := exists_high_curvature_geodesic_tail hkappa
  obtain ⟨epsScalar, hepsScalar, hescape⟩ := abs_scalar_tendsto_atTop_of_escaping_curves hkappa
  obtain ⟨epsDistance, hepsDistance, hlength⟩ :=
    scalar_remaining_length_lower_bound_of_escaping_curves hA
  refine ⟨min epsGeo (_root_.Min.min epsScalar epsDistance), c,
    lt_min hepsGeo (lt_min hepsScalar hepsDistance), hc, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X f hf p hp rho hrho hdist L maps C hcanonical
    r hr hrconv htarget hlower hcompact
  obtain ⟨hleGeo, hleRest⟩ := le_min_iff.mp hle
  obtain ⟨hleScalar, hleDistance⟩ := le_min_iff.mp hleRest
  let : EMetricSpace L.M := L.emetricSpace
  have hupper : ∀ K : Set L.M, IsCompact K → ∀ D : ℝ, 1 < D → ∀ᶠ n in _root_.Filter.atTop,
      ∀ x ∈ K, ∀ v : TangentSpace I3 x,
        ((X.term (f n)).S.base.metric 0).inner (maps.partialDiffeomorph n x)
          (mfderiv I3 I3 (maps.partialDiffeomorph n) x v)
          (mfderiv I3 I3 (maps.partialDiffeomorph n) x v) ≤ D ^ 2 * L.metric.inner x v v := by
    intro K hK D hD
    obtain ⟨N, hN⟩ := KappaSolutions.exists_pointed_full_ambient_quadratic_control C
      (fun n => by rw [hcanonical n]; rfl) K hK (D ^ 2 - 1) (by nlinarith)
    filter_upwards [_root_.Filter.eventually_ge_atTop N] with n hn
    intro x hx v
    have hh := (abs_le.mp ((hN n hn).2 x hx v)).2
    change ((X.term (f n)).S.base.metric 0).inner (maps.partialDiffeomorph n x)
      (mfderiv I3 I3 (maps.partialDiffeomorph n) x v)
      (mfderiv I3 I3 (maps.partialDiffeomorph n) x v) - L.metric.inner x v v ≤
        (D ^ 2 - 1) * L.metric.inner x v v at hh
    nlinarith
  obtain ⟨N, γ, s, hγdata⟩ := exists_geodesic_tail_curves X f hf p hp
    (hgeo eps heps hleGeo sigma hsigma Phi hPhi X)
  let shift : ℕ → ℕ := fun n => N + n
  have hshift : StrictMono shift := fun _ _ h => Nat.add_lt_add_left h N
  let ell : ℕ → ℝ := fun n => metricDistance ((X.term (f (shift n))).S.base.metric 0)
    (X.term (f (shift n))).basepoint (p (shift n))
  let Ψ := maps.compSubseq shift hshift
  have hstart (n : ℕ) : γ n 0 = (X.term (f (shift n))).basepoint := (hγdata n).2.1
  have hsmooth (n : ℕ) : ContMDiffOn 𝓘(ℝ, ℝ) I3 1 (γ n) (_root_.Set.Icc 0 (ell n)) :=
    ((hγdata n).2.2.2.1.of_le (by simp)).contMDiffOn
  have hspeed (n : ℕ) (t : ℝ) : ((X.term (f (shift n))).S.base.metric 0).inner (γ n t)
      (mfderiv 𝓘(ℝ, ℝ) I3 (γ n) t 1) (mfderiv 𝓘(ℝ, ℝ) I3 (γ n) t 1) = 1 :=
    (hγdata n).2.2.2.2.2.1 t
  have hmin (n : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 (ell n))
      (v : ℝ) (hv : v ∈ _root_.Set.Icc 0 (ell n)) :
      edist t v ≤ riemannianEDistOf ((X.term (f (shift n))).S.base.metric 0) (γ n t) (γ n v) := by
    let : ConnectedSpace (X.term (f (shift n))).M := X.connected (f (shift n))
    rw [edist_dist, Real.dist_eq, ← (hγdata n).2.2.2.2.2.2.1 t ht v hv]
    exact (ENNReal.ofReal_toReal (riemannianEDistOf_ne_top _ _ _)).le
  obtain ⟨eta, g, heta, hg, hbase, hconv⟩ := Ψ.exists_isometric_curve_subseq_limit hrho
    (r ∘ shift) ell (fun n => hr (shift n)) (fun _ => ENNReal.toReal_nonneg)
    (hrconv.comp hshift.tendsto_atTop) (hdist.comp hshift.tendsto_atTop)
    (fun n => htarget (shift n))
    (fun e he => hshift.tendsto_atTop (hlower e he))
    (fun K hK D hD => hshift.tendsto_atTop (hupper K hK D hD)) hcompact
    γ hsmooth hstart (fun n t _ => (hspeed n t).le) hmin
  let phi := shift ∘ eta
  have hphi : StrictMono phi := hshift.comp heta
  let Θ := maps.compSubseq phi hphi
  have hstay (t : ℝ) (ht : t ∈ _root_.Set.Ico 0 rho) : ∀ᶠ n in _root_.Filter.atTop,
      γ (eta n) t ∈ (Θ.partialDiffeomorph n).target := by
    filter_upwards [hphi.tendsto_atTop (hrconv.eventually (eventually_gt_nhds ht.2)),
      heta.tendsto_atTop ((hdist.comp hshift.tendsto_atTop).eventually
        (eventually_gt_nhds ht.2))] with n hn hn'
    apply htarget (phi n)
    have hh := Geometry.riemannianEDistOf_le_of_curve_speed_bound
      ((X.term (f (shift (eta n)))).S.base.metric 0) (C := 1) ht.1
      ((hsmooth (eta n)).mono (_root_.Set.Icc_subset_Icc le_rfl hn'.le)) (by
        intro v hv
        rw [hspeed, Real.sqrt_one])
    simp only [hstart, sub_zero, ENNReal.ofReal_one, one_mul] at hh
    exact hh.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hr (phi n))).mpr hn)
  have hcanonical' (n : ℕ) : (C.compSubseq phi hphi).domain n =
      CanonicalMetricCompactness.canonicalSourceData Θ n := by
    change (C.domain (phi n)).compSubseq phi hphi n = _
    rw [hcanonical (phi n)]
    rfl
  have hdistEnd (t : _root_.Set.Ico 0 rho) : ∀ᶠ n in _root_.Filter.atTop,
      riemannianEDistOf ((X.term ((f ∘ phi) n)).S.base.metric 0)
        (γ (eta n) t) (p (phi n)) ≤ ENNReal.ofReal ((ell ∘ eta) n - t) := by
    filter_upwards [((hdist.comp hshift.tendsto_atTop).comp heta.tendsto_atTop).eventually
      (eventually_gt_nhds t.property.2)] with n hn
    have hb := Geometry.riemannianEDistOf_le_of_curve_speed_bound
      ((X.term (f (shift (eta n)))).S.base.metric 0) (C := 1) hn.le
      ((hsmooth (eta n)).mono (_root_.Set.Icc_subset_Icc t.property.1 le_rfl)) (by
        intro v hv
        rw [hspeed, Real.sqrt_one])
    simp only [ENNReal.ofReal_one, one_mul] at hb
    have hend : γ (eta n) (ell (eta n)) = p (phi n) := (hγdata (eta n)).2.2.1
    change riemannianEDistOf ((X.term (f (phi n))).S.base.metric 0)
      (γ (eta n) t) (γ (eta n) (ell (eta n))) ≤ ENNReal.ofReal (ell (eta n) - t) at hb
    rw [hend] at hb
    exact hb
  have hblow := hescape eps heps hleScalar sigma hsigma Phi hPhi X (f ∘ phi)
    (hf.comp hphi) (fun n => p (phi n)) (hp.comp hphi.tendsto_atTop) rho (ell ∘ eta)
    ((hdist.comp hshift.tendsto_atTop).comp heta.tendsto_atTop)
    (fun n t => γ (eta n) t) hdistEnd L Θ (C.compSubseq phi hphi) hcanonical' g
    (fun t => hstay t t.property) (fun t =>
      (hconv {t} isCompact_singleton).tendsto_at (_root_.Set.mem_singleton t))
  have hquant := hlength eps hleDistance kappa sigma Phi X (f ∘ phi)
    (hf.comp hphi) (fun n => p (phi n)) (hp.comp hphi.tendsto_atTop) rho (ell ∘ eta)
    ((hdist.comp hshift.tendsto_atTop).comp heta.tendsto_atTop)
    (fun n t => γ (eta n) t) hdistEnd L Θ (C.compSubseq phi hphi) hcanonical' g
    (fun t => hstay t t.property) (fun t =>
      (hconv {t} isCompact_singleton).tendsto_at (_root_.Set.mem_singleton t))
  refine ⟨phi, (fun n => γ (eta n)), (fun n => s (eta n)), g, hphi, hg, hbase,
    (fun n => hγdata (eta n)), hconv, ?_, hblow, hquant⟩
  intro x hx
  have hmap : _root_.Filter.NeBot (_root_.Filter.map (Subtype.val : _root_.Set.Ico 0 rho → ℝ)
      (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 rho → ℝ) (𝓝 rho))) := by
    rw [_root_.Filter.map_comap_setCoe_val]
    exact right_nhdsWithin_Ico_neBot hrho
  let _ := hmap.of_map
  have hscalar : _root_.Filter.Tendsto (fun t => |metricScalarAt L.metric (g t)|)
      (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 |metricScalarAt L.metric x|) :=
    ((metricScalar_smooth L.metric).continuous.abs.tendsto x).comp hx
  exact not_tendsto_nhds_of_tendsto_atTop hblow _ hscalar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_isometric_curve_with_missing_endpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_isometric_curve_with_missing_endpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_isometric_curve_with_missing_endpoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_isometric_curve_with_missing_endpoint

theorem exists_terminal_pointed_limit_with_missing_endpoint_of_not_boundedAtDistance
    {kappa : ℝ} (hkappa : 0 < kappa) {A : ℝ} (hA : 0 ≤ A) :
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
                        ∀ t : _root_.Set.Ico 0 F.radius, 2 < metricScalarAt L.metric (g t) →
                          A ^ 2 ≤ metricScalarAt L.metric (g t) *
                            dist q (g t : UniformSpace.Completion L.M) ^ 2 := by
  obtain ⟨epsLocal, hepsLocal, hlocal⟩ :=
    exists_terminal_pointed_convergence_of_not_boundedAtDistance hkappa
  obtain ⟨epsCurve, c, hepsCurve, hc, hcurve⟩ := exists_isometric_curve_with_missing_endpoint hkappa hA
  refine ⟨min epsLocal epsCurve, c, lt_min hepsLocal hepsCurve, hc, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X hnot
  obtain ⟨f, hf, F, r, hr, hrT, L, maps, C, hcanonical, htargets, hmetrics,
    hcompact, hbase, hsec⟩ := hlocal eps heps (hle.trans (min_le_left _ _))
      sigma hsigma Phi hPhi X hnot
  have hL : PathConnectedSpace L.M :=
    maps.path_connected_space_of_frequently_path_connected_targets
      (Eventually.frequently (Eventually.of_forall fun n => by
        rw [htargets n]
        exact isPathConnected_riemannianBallOf ((X.term (f n)).S.base.metric 0)
          (X.term (f n)).basepoint (hr n).1))
  let _ : PathConnectedSpace L.M := hL
  let _ : EMetricSpace L.M := L.emetricSpace
  let _ : MetricSpace L.M := EMetricSpace.toMetricSpace
    (fun x y => riemannianEDistOf_ne_top L.metric x y)
  have hlower : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in _root_.Filter.atTop,
      ∀ x ∈ maps.source n, ∀ v : TangentSpace I3 x,
        (1 - eta) * L.metric.inner x v v ≤
          ((X.term (f n)).S.base.metric 0).inner (maps.partialDiffeomorph n x)
            (mfderiv I3 I3 (maps.partialDiffeomorph n) x v)
            (mfderiv I3 I3 (maps.partialDiffeomorph n) x v) := by
    intro eta heta
    obtain ⟨N, hN⟩ := hmetrics eta heta
    filter_upwards [_root_.Filter.eventually_ge_atTop N] with n hn
    exact fun x hx v => (hN n hn x hx v).1
  obtain ⟨phi, γ, s, g, hphi, hg, hgbase, hγ, hconv, hno, hblow, hquant⟩ :=
    hcurve eps heps (hle.trans (min_le_right _ _)) sigma hsigma Phi hPhi X f hf
      F.points F.curvature_limit F.radius F.radius_pos F.distance_limit L maps C.metrics hcanonical
      r (fun n => (hr n).1) hrT (fun n => by rw [htargets n]) hlower hcompact
  have hRnonneg (x : L.M) : 0 ≤ metricScalarAt L.metric x := by
    apply metricScalarAt_nonnegative_of_ricci_nonnegative L.metric x (by simp [ThreeSpace])
    intro v
    rw [metricRicciAt_apply_eq_ricciTensor]
    exact Geometry.Riemannian.BonnetMyers.ricci_nonneg_of_sec L.metric x
      ((metricRm04At_mem_tensor04SectionalNonnegativeCone_iff L.metric x).mpr (hsec x)) v
  have hblowScalar := hblow.congr' (Eventually.of_forall fun t => abs_of_nonneg (hRnonneg (g t)))
  obtain ⟨q, hq, hdist⟩ := Geometry.exists_completion_endpoint_of_isometry F.radius_pos hg
  refine ⟨f, hf, F, r, hr, hrT, L, hL, maps, C, hcanonical, htargets, hmetrics,
    hcompact, hbase, hsec, phi, γ, s, g, hphi, hg, hgbase, hγ, hconv, hno, hblowScalar,
    q, hq, hdist, ?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact hno x ((UniformSpace.Completion.isUniformInducing_coe L.M).isInducing.tendsto_nhds_iff.mpr hq)
  · intro t ht
    rw [hdist t]
    exact hquant t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminal_pointed_limit_with_missing_endpoint_of_not_boundedAtDistance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminal_pointed_limit_with_missing_endpoint_of_not_boundedAtDistance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminal_pointed_limit_with_missing_endpoint_of_not_boundedAtDistance ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_terminal_pointed_limit_with_missing_endpoint_of_not_boundedAtDistance

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
