import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckDepthInduction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.Submission.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

theorem exists_eventually_isTracedRegion_of_forall_neckAlternative_at_top
    {P₀ : ℕ → OrientedThreeStage.{u}} (H : ∀ n, RetainedCoreHistory (P₀ n))
    (t : ∀ n, _root_.Set.Icc (0 : ℝ) (H n).toHistory.horizon)
    (y : ∀ n, ((H n).toHistory.stageAt (t n)).Carrier) (R : ℕ → ℝ)
    (hRlim : _root_.Filter.Tendsto R _root_.Filter.atTop _root_.Filter.atTop)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinch : ∀ n, (H n).EventSlabsPinched phi)
    (hlast : ∀ n, (H n).toHistory.activeStage (t n) = Fin.last (H n).eventCount →
      ∃ h : (H n).time (Fin.last (H n).eventCount) < (H n).horizon,
        Perelman.PhiAlmostNonnegative ((H n).finalSlab h).flow
          (_root_.Set.Icc ((H n).time (Fin.last (H n).eventCount)) (H n).horizon) phi)
    (htop : ∀ n, (H n).time ((H n).toHistory.activeStage (t n)) < t n)
    {ε ε₁ C1 C2 : ℝ} {qcan : ℕ → ℝ} (hε₁ : ε₁ ≤ 1 / 30000)
    (hq : ∀ c : ℝ, 0 < c → ∀ᶠ n in _root_.Filter.atTop, qcan n < c * R n)
    (hclass : ∀ n,
      (H n).EventSlabsStronglyCanonical ε ε₁ C1 C2 (qcan n) (Fin.last (H n).eventCount))
    (hterm : ∀ n, (H n).toHistory.activeStage (t n) = Fin.last (H n).eventCount →
      ∃ (s : ℝ) (G : ((H n).stage ((H n).toHistory.activeStage (t n))).IncomingSlab
          ((H n).time ((H n).toHistory.activeStage (t n))) s),
        (t n : ℝ) < s ∧
        (∀ τ ∈ _root_.Set.Icc ((H n).time ((H n).toHistory.activeStage (t n))) (t n : ℝ),
          G.flow.base.metric τ =
            (H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) τ) ∧
        (H n).StronglyCanonicalBefore ((H n).toHistory.activeStage (t n)) G ε ε₁ C1 C2 (qcan n) s)
    (hball : ∀ A : ℝ, 0 < A → ∃ Qlow Qup : ℝ, 0 < Qlow ∧ ∀ᶠ n in _root_.Filter.atTop,
      ∀ x ∈ riemannianBallOf
          ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) (y n)
          (A / Real.sqrt (R n)),
        Qlow * R n ≤ metricScalarAt
            ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) x ∧
          metricScalarAt
            ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) x ≤
              Qup * R n)
    (hneck : ∀ A c : ℝ, 0 < A → 0 < c → ∀ᶠ n in _root_.Filter.atTop,
      ∀ x ∈ riemannianBallOf
          ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) (y n)
          (A / Real.sqrt (R n)),
        c * R n ≤ metricScalarAt
            ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) x →
        ∀ W : SpatialCanonicalWitness
            ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) ε C1 C2 x,
          W.capTubeHasNeckChart ε → ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk) :
    ∀ A : ℝ, 0 < A → ∃ θ K : ℝ, 0 < θ ∧ 0 ≤ K ∧ ∀ᶠ n in _root_.Filter.atTop,
      (H n).toHistory.isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (θ / R n) (K * R n) := by
  intro A hA
  obtain ⟨Qlow, Qup, hQlow, hev⟩ := hball A hA
  have hR1 : ∀ᶠ n in _root_.Filter.atTop, (1 : ℝ) ≤ R n := hRlim.eventually (_root_.Filter.eventually_ge_atTop 1)
  have hQup : 0 < Qup := by
    obtain ⟨n, hn1, hn⟩ := (hR1.and hev).exists
    have hy := hn (y n) (by
      change riemannianEDistOf _ (y n) (y n) < _
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr (by positivity))
    by_contra hneg
    have h1 : Qup * R n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) (by linarith)
    have h2 : 0 < Qlow * R n := by positivity
    linarith [hy.1, hy.2]
  have hphi1 : 0 < phi 1 := hphi.pos 1
  have hphi0 : 0 < phi 0 := hphi.pos 0
  refine ⟨(10 * Qup)⁻¹, 8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * _root_.Max.max Qup 1, by positivity,
    by positivity, ?_⟩
  filter_upwards [hev, hq Qlow hQlow, hneck A Qlow hA hQlow, hR1] with n hn hqn hneckn hRn
  have hRpos : 0 < R n := by linarith
  have key := (H n).isTracedRegion_of_forall_neckAlternative hphi (hpinch n) hε₁ (hclass n)
    (hlast n) (htop n) (ρ := A / Real.sqrt (R n)) (T := 0) (Qlow := Qlow * R n)
    (Qup := Qup * R n) (L := Qlow * R n) (by positivity) le_rfl (t n).2.1 (by positivity) hqn
    (fun x hx => (hn x hx).1) (fun x hx => (hn x hx).2) (by simp)
    (fun v hv1 hv2 _ hlastv => by
      have hvt : v = t n := Subtype.ext (le_antisymm hv2 (by simpa using hv1))
      subst hvt
      exact hterm n hlastv)
    (fun x hx v hv1 hvt _ B hL W hW => by
      have hvt' : v = t n := Subtype.ext (le_antisymm hvt (by simpa using hv1))
      subst hvt'
      have hpt : B.point ((H n).toHistory.activeStage (t n)) le_rfl
          ((H n).toHistory.activeStage_mono hvt) = x := B.endpoint_eq
      rw [hpt] at hL
      revert W
      rw [hpt]
      exact fun W hW => hneckn x hx hL W hW)
  have hdepth : (10 * Qup)⁻¹ / R n = 0 + (10 * (Qup * R n))⁻¹ := by
    rw [zero_add, div_eq_mul_inv, ← mul_inv, mul_assoc]
  rw [hdepth]
  refine key.mono_bound (by positivity) ?_
  have hmax : _root_.Max.max (Qup * R n) 1 ≤ _root_.Max.max Qup 1 * R n := by
    refine max_le ?_ ?_
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hRpos.le
    · calc (1 : ℝ) ≤ R n := hRn
        _ = 1 * R n := (one_mul _).symm
        _ ≤ _root_.Max.max Qup 1 * R n := mul_le_mul_of_nonneg_right (le_max_right _ _) hRpos.le
  calc 8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * _root_.Max.max (Qup * R n) 1
      ≤ 8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (_root_.Max.max Qup 1 * R n) :=
        mul_le_mul_of_nonneg_left hmax (by positivity)
    _ = 8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * _root_.Max.max Qup 1 * R n := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_eventually_isTracedRegion_of_forall_neckAlternative_at_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_eventually_isTracedRegion_of_forall_neckAlternative_at_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_eventually_isTracedRegion_of_forall_neckAlternative_at_top ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_eventually_isTracedRegion_of_forall_neckAlternative_at_top

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

end
