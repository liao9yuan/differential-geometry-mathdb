import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedSegmentNecks
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Distance
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
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_eventually_strongNeck_at_pointed_images_of_minimizing_segment_limits
    (kappa : ℝ) {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ A epsStar : ℝ, 0 < A ∧ 0 < epsStar ∧
      ∀ eps sigma : ℝ, ∀ Phi : ℝ → ℝ, ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        eps ≤ epsStar → ∀ (f : ℕ → ℕ) (γ : ∀ n, ℝ → (X.term (f n)).M)
          (ell : ℕ → ℝ) (rho tau : ℝ),
          _root_.Filter.Tendsto ell _root_.Filter.atTop (𝓝 rho) → 0 < tau → tau < rho →
          (∀ n, ∀ s ∈ _root_.Set.Icc 0 (ell n), ∀ r ∈ _root_.Set.Icc 0 (ell n),
            metricDistance ((X.term (f n)).S.base.metric 0) (γ n s) (γ n r) = |s - r|) →
          ∀ (L : PointedRiemannianManifold.{u, 0, 0} (I := I3))
            (maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f)
            (C : MetricConvergenceData maps),
            (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData maps n) →
            ∀ x : L.M, 2 < metricScalarAt L.metric x →
              (∀ᶠ n in _root_.Filter.atTop, γ n tau ∈ maps.target n) →
              _root_.Filter.Tendsto (fun n => (maps.partialDiffeomorph n).symm (γ n tau)) _root_.Filter.atTop (𝓝 x) →
              A ^ 2 < metricScalarAt L.metric x * tau ^ 2 →
              A ^ 2 < metricScalarAt L.metric x * (rho - tau) ^ 2 →
              ∀ᶠ n in _root_.Filter.atTop, Nonempty (StrongNeck (X.term (f n)).S
                (2 * alpha) (maps.partialDiffeomorph n x) 0) := by
  obtain ⟨A, epsStar, hA, hepsStar, hneck⟩ :=
    exists_eventually_strongNeck_near_minimizing_segment_limits.{u} kappa ha hsmall
  refine ⟨A, epsStar, hA, hepsStar, ?_⟩
  intro eps sigma Phi X heps f γ ell rho tau hell htau htr hsegment
    L maps C hcanonical x hR hstay hconv hleft hright
  have hreference (n : ℕ) : (C.domain n).referenceMetric = (C.domain n).limitMetric := by
    rw [hcanonical n]
    rfl
  have hupper (K : Set L.M) (hK : IsCompact K) (D : ℝ) (hD : 1 < D) :
      ∀ᶠ n in _root_.Filter.atTop, ∀ y ∈ K, ∀ v : TangentSpace I3 y,
        ((X.term (f n)).S.base.metric 0).inner (maps.partialDiffeomorph n y)
          (mfderiv I3 I3 (maps.partialDiffeomorph n) y v)
          (mfderiv I3 I3 (maps.partialDiffeomorph n) y v) ≤ D ^ 2 * L.metric.inner y v v := by
    obtain ⟨N, hN⟩ := KappaSolutions.exists_pointed_full_ambient_quadratic_control
      C hreference K hK (D ^ 2 - 1) (by nlinarith)
    filter_upwards [_root_.Filter.eventually_ge_atTop N] with n hn
    intro y hy v
    have hh := (abs_le.mp ((hN n hn).2 y hy v)).2
    change ((X.term (f n)).S.base.metric 0).inner (maps.partialDiffeomorph n y)
      (mfderiv I3 I3 (maps.partialDiffeomorph n) y v)
      (mfderiv I3 I3 (maps.partialDiffeomorph n) y v) - L.metric.inner y v v ≤
        (D ^ 2 - 1) * L.metric.inner y v v at hh
    nlinarith
  have hdist := maps.tendsto_edist_map_zero hupper hconv
  have hsource : _root_.Filter.Tendsto (fun n => riemannianEDistOf ((X.term (f n)).S.base.metric 0)
      (maps.partialDiffeomorph n x) (γ n tau)) _root_.Filter.atTop (𝓝 0) := by
    apply hdist.congr'
    filter_upwards [hstay] with n hn
    have hinv : maps.partialDiffeomorph n ((maps.partialDiffeomorph n).symm (γ n tau)) =
        γ n tau := (maps.partialDiffeomorph n).right_inv hn
    change riemannianEDistOf _ _ (maps.partialDiffeomorph n
      ((maps.partialDiffeomorph n).symm (γ n tau))) = _
    rw [hinv]
    rfl
  have hnear : _root_.Filter.Tendsto (fun n => metricDistance ((X.term (f n)).S.base.metric 0)
      (maps.partialDiffeomorph n x) (γ n tau)) _root_.Filter.atTop (𝓝 0) := by
    simpa only [metricDistance, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hsource
  have hscalar := KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains C hcanonical x
  exact hneck eps sigma Phi X heps f γ (fun n => maps.partialDiffeomorph n x)
    ell rho tau (metricScalarAt L.metric x) hell htau htr hR hsegment hscalar hnear hleft hright

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_strongNeck_at_pointed_images_of_minimizing_segment_limits then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_strongNeck_at_pointed_images_of_minimizing_segment_limits"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_strongNeck_at_pointed_images_of_minimizing_segment_limits ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_strongNeck_at_pointed_images_of_minimizing_segment_limits

theorem exists_eventually_strongNeck_at_pointed_images_near_scalar_blowup_endpoint
    (kappa : ℝ) {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ A epsStar : ℝ, 0 < A ∧ 0 < epsStar ∧
      ∀ eps sigma : ℝ, ∀ Phi : ℝ → ℝ, ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        eps ≤ epsStar → ∀ (f : ℕ → ℕ) (γ : ∀ n, ℝ → (X.term (f n)).M)
          (ell : ℕ → ℝ) (rho : ℝ), 0 < rho → _root_.Filter.Tendsto ell _root_.Filter.atTop (𝓝 rho) →
          (∀ n, ∀ s ∈ _root_.Set.Icc 0 (ell n), ∀ r ∈ _root_.Set.Icc 0 (ell n),
            metricDistance ((X.term (f n)).S.base.metric 0) (γ n s) (γ n r) = |s - r|) →
          ∀ (L : PointedRiemannianManifold.{u, 0, 0} (I := I3))
            (maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f)
            (C : MetricConvergenceData maps),
            (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData maps n) →
            ∀ g : _root_.Set.Ico 0 rho → L.M,
              (∀ tau : _root_.Set.Ico 0 rho, ∀ᶠ n in _root_.Filter.atTop, γ n tau ∈ maps.target n) →
              (∀ tau : _root_.Set.Ico 0 rho,
                _root_.Filter.Tendsto (fun n => (maps.partialDiffeomorph n).symm (γ n tau))
                  _root_.Filter.atTop (𝓝 (g tau))) →
              _root_.Filter.Tendsto (fun tau => metricScalarAt L.metric (g tau))
                (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 rho → ℝ) (𝓝 rho)) _root_.Filter.atTop →
              (∀ tau : _root_.Set.Ico 0 rho, 2 < metricScalarAt L.metric (g tau) →
                A ^ 2 ≤ metricScalarAt L.metric (g tau) * (rho - tau) ^ 2) →
              ∀ᶠ (tau : _root_.Set.Ico 0 rho) in _root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 rho → ℝ) (𝓝 rho),
                ∀ᶠ n in _root_.Filter.atTop, Nonempty (StrongNeck (X.term (f n)).S
                  (2 * alpha) (maps.partialDiffeomorph n (g tau)) 0) := by
  obtain ⟨A, epsStar, hA, hepsStar, hneck⟩ :=
    exists_eventually_strongNeck_at_pointed_images_of_minimizing_segment_limits.{u}
      kappa ha hsmall
  refine ⟨2 * A, epsStar, by positivity, hepsStar, ?_⟩
  intro eps sigma Phi X heps f γ ell rho hrho hell hsegment L maps C hcanonical
    g hstay hconv hblow hquant
  have htime : _root_.Filter.Tendsto (Subtype.val : _root_.Set.Ico 0 rho → ℝ)
      (_root_.Filter.comap (Subtype.val : _root_.Set.Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 rho) := _root_.Filter.tendsto_comap
  have hleft := hblow.atTop_mul_pos (sq_pos_of_pos hrho) (htime.pow 2)
  filter_upwards [htime.eventually (eventually_gt_nhds hrho),
    hblow.eventually (_root_.Filter.eventually_gt_atTop 2),
    hleft.eventually (_root_.Filter.eventually_gt_atTop (A ^ 2))] with tau ht hR hl
  have hr : A ^ 2 < metricScalarAt L.metric (g tau) * (rho - tau) ^ 2 := by
    have hh := hquant tau hR
    nlinarith [sq_pos_of_pos hA]
  exact hneck eps sigma Phi X heps f γ ell rho tau hell ht tau.property.2 hsegment
    L maps C hcanonical (g tau) hR (hstay tau) (hconv tau) hl hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_strongNeck_at_pointed_images_near_scalar_blowup_endpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_strongNeck_at_pointed_images_near_scalar_blowup_endpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_strongNeck_at_pointed_images_near_scalar_blowup_endpoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_eventually_strongNeck_at_pointed_images_near_scalar_blowup_endpoint

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
end
