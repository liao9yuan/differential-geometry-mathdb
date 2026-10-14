import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.BufferedReference
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.CanonicalCurvatureBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.BoundedScalar
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Solution
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Soliton

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
  {D : RealTimeInterval}

theorem metric_eq_canonicalMetricFamily_of_gradientRicciSoliton
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a₀ a b sigma R : ℝ} (hbuffer : a₀ < a)
    (hcarrier : _root_.Set.Icc a₀ b ⊆ D.carrier)
    (hregular : _root_.Set.Ioo a₀ b ⊆ D.regular)
    (hcurv : ∀ t ∈ _root_.Set.Icc a₀ b, ∀ x : M,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ R)
    (hcomplete : RiemannianMetricComplete (S.base.metric a))
    (f : C^∞⟮I, M; ℝ⟯)
    (hsol : gradientRicciSoliton (S.base.metric a) f sigma)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc a b) (hscale : 0 < 1 - sigma * (t - a)) :
    S.base.metric t =
      canonicalMetricFamily (S.base.metric a) f sigma hcomplete hsol (t - a) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  rcases ht.1.eq_or_lt with hat | hat
  · subst t
    simp only [sub_self, canonicalMetricFamily_zero]
  have hta : 0 < t - a := sub_pos.mpr hat
  have ha : a ∈ _root_.Set.Icc a₀ b := ⟨hbuffer.le, ht.1.trans ht.2⟩
  have hcomplete₀ : RiemannianMetricComplete (S.base.metric a₀) :=
    complete_of_curvature_bound S hS hcarrier hregular hcurv
      ⟨le_rfl, hbuffer.le.trans ha.2⟩ ha hcomplete
  have hR : 0 ≤ _root_.Max.max R 0 := le_max_right _ _
  have hcurv' : ∀ q ∈ _root_.Set.Icc a₀ b, ∀ x : M,
      normSq0S (S.base.metric q) x 4 (S.base.rm04 q x) ≤ _root_.Max.max R 0 :=
    fun q hq x => (hcurv q hq x).trans (le_max_left _ _)
  obtain ⟨K, hK, hcanonical⟩ := canonicalMetricFamily_curvature_bound_on_Icc
    (S.base.metric a) f sigma hcomplete hsol hR hscale
    (fun x => hcurv' a ha x)
  let C := RealTimeInterval.closed 0 (t - a) hta.le
  let U := canonicalSolutionOn (S.base.metric a) f sigma hcomplete hsol C
  have hC : C.carrier ⊆ canonicalTimeDomain sigma := by
    intro q hq
    change 0 < 1 - sigma * q
    change q ∈ _root_.Set.Icc 0 (t - a) at hq
    by_cases hsigma : 0 ≤ sigma
    · have hm := mul_le_mul_of_nonneg_left hq.2 hsigma
      linarith only [hscale, hm]
    · have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hsigma) hq.1
      linarith only [hm]
  have hU : IsSolutionOn U :=
    canonicalSolutionOn_isSolutionOn (S.base.metric a) f sigma hcomplete hsol C hC
  have hshift : IsSolutionOn (S.timeShift a) := isSolutionOn_timeShift hS a
  have hshift_carrier : _root_.Set.Icc (a₀ - a) (t - a) ⊆ (D.timeShift a).carrier := by
    intro q hq
    change q + a ∈ D.carrier
    exact hcarrier ⟨by linarith only [hq.1], by linarith only [hq.2, ht.2]⟩
  have hshift_regular : _root_.Set.Ioo (a₀ - a) (t - a) ⊆ (D.timeShift a).regular := by
    intro q hq
    change q + a ∈ D.regular
    exact hregular ⟨by linarith only [hq.1], by linarith only [hq.2, ht.2]⟩
  have hshift_complete : RiemannianMetricComplete
      ((S.timeShift a).base.metric (a₀ - a)) := by
    simpa only [SolutionOn.timeShift_base_metric, sub_add_cancel] using hcomplete₀
  have hshift_curv : ∀ q ∈ _root_.Set.Icc (a₀ - a) (t - a), ∀ x : M,
      normSq0S ((S.timeShift a).base.metric q) x 4
        ((S.timeShift a).base.rm04 q x) ≤ _root_.Max.max R 0 := by
    intro q hq x
    exact hcurv' (q + a)
      ⟨by linarith only [hq.1], by linarith only [hq.2, ht.2]⟩ x
  have hinitial : U.base.metric 0 = (S.timeShift a).base.metric 0 := by
    change canonicalMetricFamily (S.base.metric a) f sigma hcomplete hsol 0 =
      S.base.metric (0 + a)
    rw [canonicalMetricFamily_zero, zero_add]
  have heq := forward_unique_on_closed_slab_of_complete_bounded_curvature_of_buffered_reference
    U (S.timeShift a) hU hshift (by linarith only [hbuffer] : a₀ - a < 0) hta
    (fun _ hq => hq) hshift_carrier (fun _ hq => hq) hshift_regular
    hshift_complete hK hR hcanonical hshift_curv hinitial
    (t - a) ⟨hta.le, le_rfl⟩
  change canonicalMetricFamily (S.base.metric a) f sigma hcomplete hsol (t - a) =
    S.base.metric (t - a + a) at heq
  simpa only [sub_add_cancel] using heq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Soliton.metric_eq_canonicalMetricFamily_of_gradientRicciSoliton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Soliton.metric_eq_canonicalMetricFamily_of_gradientRicciSoliton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Soliton.metric_eq_canonicalMetricFamily_of_gradientRicciSoliton ``Submission.DifferentialGeometry.PDE.RicciFlow.Soliton.metric_eq_canonicalMetricFamily_of_gradientRicciSoliton

theorem metricScalarAt_eq_zero_of_gradientRicciSoliton_slice
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T r rho R : ℝ} (hr : 0 < r) (hrrho : r < rho)
    (hcarrier : _root_.Set.Icc (T - rho) T ⊆ D.carrier)
    (hregular : _root_.Set.Ioo (T - rho) T ⊆ D.regular)
    (hcurv : ∀ t ∈ _root_.Set.Icc (T - rho) T, ∀ x : M,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ R)
    (hcomplete : RiemannianMetricComplete (S.base.metric T))
    (f : C^∞⟮I, M; ℝ⟯)
    (hsol : gradientRicciSoliton (S.base.metric (T - r)) f r⁻¹)
    (x : M) : metricScalarAt (S.base.metric (T - r)) x = 0 := by
  have hslice : T - r ∈ _root_.Set.Icc (T - rho) T := by
    constructor <;> linarith only [hr, hrrho]
  have hT : T ∈ _root_.Set.Icc (T - rho) T := by
    constructor <;> linarith only [hr, hrrho]
  have hcompleteSlice : RiemannianMetricComplete (S.base.metric (T - r)) :=
    complete_of_curvature_bound S hS hcarrier hregular hcurv hslice hT hcomplete
  have hcanonical : ∀ q ∈ _root_.Set.Ico 0 r,
      canonicalMetricFamily (S.base.metric (T - r)) f r⁻¹ hcompleteSlice hsol q =
        S.base.metric (q + (T - r)) := by
    intro q hq
    have hscale : 0 < 1 - r⁻¹ * q := by
      have hm : r⁻¹ * q < 1 := by
        calc
          r⁻¹ * q < r⁻¹ * r := mul_lt_mul_of_pos_left hq.2 (inv_pos.mpr hr)
          _ = 1 := inv_mul_cancel₀ hr.ne'
      linarith only [hm]
    have htime : q + (T - r) ∈ _root_.Set.Icc (T - r) T := by
      constructor <;> linarith only [hq.1, hq.2]
    have heq := metric_eq_canonicalMetricFamily_of_gradientRicciSoliton S hS
      (by linarith only [hrrho] : T - rho < T - r)
      hcarrier hregular hcurv hcompleteSlice f hsol htime
      (by simpa only [add_sub_cancel_right] using hscale)
    simpa only [add_sub_cancel_right] using heq.symm
  apply metricScalarAt_eq_zero_of_canonicalMetricFamily_scalar_bounded
    (S.base.metric (T - r)) f (inv_pos.mpr hr) hcompleteSlice hsol
    (C := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt R) ?_ x
  rw [inv_inv]
  have hpositive : ∀ᶠ q in 𝓝[<] r, 0 < q :=
    (eventually_gt_nhds hr).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpositive, self_mem_nhdsWithin] with q hq0 hqr
  intro y
  change q < r at hqr
  rw [hcanonical q ⟨hq0.le, hqr⟩]
  have htime : q + (T - r) ∈ _root_.Set.Icc (T - rho) T := by
    constructor <;> linarith only [hq0, hqr, hrrho]
  exact (scalar_abs_le_rm (S.base.metric (q + (T - r))) y).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hcurv _ htime y)) (sq_nonneg _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Soliton.metricScalarAt_eq_zero_of_gradientRicciSoliton_slice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Soliton.metricScalarAt_eq_zero_of_gradientRicciSoliton_slice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Soliton.metricScalarAt_eq_zero_of_gradientRicciSoliton_slice ``Submission.DifferentialGeometry.PDE.RicciFlow.Soliton.metricScalarAt_eq_zero_of_gradientRicciSoliton_slice

end DifferentialGeometry.PDE.RicciFlow.Soliton
