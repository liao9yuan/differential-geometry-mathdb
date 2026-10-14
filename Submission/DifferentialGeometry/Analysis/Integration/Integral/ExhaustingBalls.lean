import Submission.DifferentialGeometry.Analysis.Integration.BallBoundary
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Submission.DifferentialGeometry.Analysis.Integration.Integral.QuadraticDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory in
theorem tendsto_integral_closedBall_sdiff_of_tendsto_radius
    {X F : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : _root_.MeasureTheory.Measure X} {c : X} {R : ℝ} {rn : ℕ → ℝ} {f : X → F}
    (hf : _root_.MeasureTheory.IntegrableOn f (Metric.closedBall c R) μ)
    (hsphere : μ (Metric.sphere c R) = 0) (hr : _root_.Filter.Tendsto rn _root_.Filter.atTop (𝓝 R)) :
    _root_.Filter.Tendsto (fun n => ∫ x in Metric.closedBall c R \ Metric.closedBall c (rn n), f x ∂μ)
      atTop (𝓝 0) := by
  let ν := μ.restrict (Metric.closedBall c R)
  let S (n : ℕ) := (Metric.closedBall c (rn n))ᶜ
  have hS (n : ℕ) : MeasurableSet (S n) := measurableSet_closedBall.compl
  have hlim : ∀ᵐ x ∂ν, _root_.Filter.Tendsto (fun n => (S n).indicator f x) _root_.Filter.atTop (𝓝 (0 : F)) := by
    filter_upwards [ae_mem_ball_of_measure_sphere_eq_zero hsphere] with x hx
    have hev : ∀ᶠ n in _root_.Filter.atTop, _root_.Dist.dist x c < rn n := (tendsto_order.mp hr).1 (_root_.Dist.dist x c) hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with n hn
    exact (Set.indicator_of_notMem (show x ∉ S n from fun hx' => hx' hn.le) f).symm
  have h := _root_.MeasureTheory.tendsto_integral_of_dominated_convergence (μ := ν) (fun x => ‖f x‖)
    (fun n => hf.aestronglyMeasurable.indicator (hS n)) hf.norm
    (fun n => Eventually.of_forall fun x => by
      by_cases hx : x ∈ S n
      · simp only [Set.indicator_of_mem hx, le_refl]
      · simp only [Set.indicator_of_notMem hx, norm_zero, norm_nonneg]) hlim
  have heq (n : ℕ) : (∫ x, (S n).indicator f x ∂ν) =
      ∫ x in Metric.closedBall c R \ Metric.closedBall c (rn n), f x ∂μ := by
    rw [_root_.MeasureTheory.integral_indicator (hS n)]
    rw [Measure.restrict_restrict (hS n)]
    congr 2
    exact _root_.Set.inter_comm _ _
  simpa only [heq, _root_.MeasureTheory.integral_zero] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_integral_closedBall_sdiff_of_tendsto_radius then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_integral_closedBall_sdiff_of_tendsto_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_integral_closedBall_sdiff_of_tendsto_radius ``Submission.MeasureTheory.tendsto_integral_closedBall_sdiff_of_tendsto_radius

open _root_.MeasureTheory in
theorem integral_closedBall_sdiff_eq_integral_norm_annulus_complex
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℂ → F) (c : ℂ) (a R : ℝ) :
    (∫ z in Metric.closedBall c R \ Metric.closedBall c a, f z) =
      ∫ z in {z : ℂ | _root_.Dist.dist z c ∈ _root_.Set.Icc a R}, f z := by
  apply _root_.MeasureTheory.setIntegral_congr_set
  have hzero : ∀ᵐ z : ℂ ∂volume, z ∉ Metric.sphere c a :=
    _root_.MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere _root_.MeasureTheory.MeasureSpace.volume c a)
  filter_upwards [hzero] with z hz
  apply propext
  change (_root_.Dist.dist z c ≤ R ∧ ¬dist z c ≤ a) ↔ (a ≤ _root_.Dist.dist z c ∧ _root_.Dist.dist z c ≤ R)
  have hne : _root_.Dist.dist z c ≠ a := hz
  exact ⟨fun h => ⟨(lt_of_not_ge h.2).le, h.1⟩,
    fun h => ⟨h.2, not_le.mpr (lt_of_le_of_ne h.1 hne.symm)⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integral_closedBall_sdiff_eq_integral_norm_annulus_complex then
    throwError "Refusing to shadow existing declaration MeasureTheory.integral_closedBall_sdiff_eq_integral_norm_annulus_complex"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integral_closedBall_sdiff_eq_integral_norm_annulus_complex ``Submission.MeasureTheory.integral_closedBall_sdiff_eq_integral_norm_annulus_complex

end MeasureTheory

end

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [SecondCountableTopology F]

private theorem integrable_quadratic_fderiv_on_closedBall
    {f : ℂ → F} {L : ℝ≥0} (hf : LipschitzWith L f) {c : ℂ} {R : ℝ}
    {K : Set F} (hK : IsCompact K) (hfK : _root_.Set.MapsTo f (Metric.closedBall c R) K)
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K) :
    _root_.MeasureTheory.IntegrableOn (fun x =>
      (A (f x) (fderiv ℝ f x 1) (fderiv ℝ f x 1) +
        A (f x) (fderiv ℝ f x Complex.I) (fderiv ℝ f x Complex.I)) / 2)
      (Metric.closedBall c R) := by
  borelize F
  let μ := volume.restrict (Metric.closedBall c R)
  let _ : _root_.MeasureTheory.IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr (_root_.ProperSpace.isCompact_closedBall c R).measure_ne_top
  have hm (v : ℂ) : _root_.MeasureTheory.MemLp (fun x => fderiv ℝ f x v) 2 μ := by
    apply MemLp.of_bound (measurable_fderiv_apply_const ℝ f v).aestronglyMeasurable
      ((L : ℝ) * ‖v‖)
    exact Eventually.of_forall fun x => ((fderiv ℝ f x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg v))
  have hAc : ContinuousOn (fun x => A (f x)) (Metric.closedBall c R) :=
    hA.comp hf.continuous.continuousOn hfK
  have hAm (v w : F) : _root_.MeasureTheory.AEStronglyMeasurable (fun x => A (f x) v w) μ :=
    ((hAc.clm_apply continuousOn_const).clm_apply continuousOn_const).aestronglyMeasurable
      measurableSet_closedBall
  have hnormA : ContinuousOn (fun y => ‖A y‖) K :=
    (@continuous_norm (F →L[ℝ] F →L[ℝ] ℝ) inferInstance).comp_continuousOn hA
  obtain ⟨C, hC⟩ := hK.bddAbove_image hnormA
  have hbound : ∀ᵐ x ∂μ, ‖A (f x)‖ ≤ C := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_closedBall] with x hx
    exact hC (_root_.Set.mem_image_of_mem _ (hfK hx))
  exact ((integrable_bilinear_of_apply_aestronglyMeasurable (fun x => A (f x)) hAm hbound
    (hm 1) (hm 1)).add
      (integrable_bilinear_of_apply_aestronglyMeasurable (fun x => A (f x)) hAm hbound
        (hm Complex.I) (hm Complex.I))).div_const 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.integrable_quadratic_fderiv_on_closedBall
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.integrable_quadratic_fderiv_on_closedBall target :: scope.openDecls } }

theorem tendsto_integral_quadratic_fderiv_of_eqOn_exhausting_closedBall
    {c : ℂ} {R : ℝ} {rn : ℕ → ℝ} (hr : _root_.Filter.Tendsto rn _root_.Filter.atTop (𝓝 R))
    (hrR : ∀ᶠ n in _root_.Filter.atTop, rn n ≤ R)
    (f : ℂ → F) (fn : ℕ → ℂ → F)
    {K : Set F} (hK : IsCompact K) (A : F → F →L[ℝ] F →L[ℝ] ℝ)
    (hA : ContinuousOn A K)
    (hfn : ∀ᶠ n in _root_.Filter.atTop,
      (∃ L : ℝ≥0, LipschitzWith L (fn n)) ∧ _root_.Set.MapsTo (fn n) (Metric.closedBall c R) K)
    (hcore : ∀ᶠ n in _root_.Filter.atTop, _root_.Set.EqOn (fn n) f (Metric.closedBall c (rn n)))
    (hf : _root_.MeasureTheory.IntegrableOn (fun x =>
      (A (f x) (fderiv ℝ f x 1) (fderiv ℝ f x 1) +
        A (f x) (fderiv ℝ f x Complex.I) (fderiv ℝ f x Complex.I)) / 2)
      (Metric.closedBall c R))
    (hshell : _root_.Filter.Tendsto (fun n => ∫ x in {x : ℂ | _root_.Dist.dist x c ∈ _root_.Set.Icc (rn n) R},
      (‖fderiv ℝ (fn n) x 1‖ ^ 2 + ‖fderiv ℝ (fn n) x Complex.I‖ ^ 2) / 2)
      _root_.Filter.atTop (𝓝 0)) :
    _root_.Filter.Tendsto (fun n => ∫ x in Metric.closedBall c R,
      (A (fn n x) (fderiv ℝ (fn n) x 1) (fderiv ℝ (fn n) x 1) +
        A (fn n x) (fderiv ℝ (fn n) x Complex.I) (fderiv ℝ (fn n) x Complex.I)) / 2)
      _root_.Filter.atTop (𝓝 (∫ x in Metric.closedBall c R,
        (A (f x) (fderiv ℝ f x 1) (fderiv ℝ f x 1) +
          A (f x) (fderiv ℝ f x Complex.I) (fderiv ℝ f x Complex.I)) / 2)) := by
  let e (g : ℂ → F) (x : ℂ) :=
    (A (g x) (fderiv ℝ g x 1) (fderiv ℝ g x 1) +
      A (g x) (fderiv ℝ g x Complex.I) (fderiv ℝ g x Complex.I)) / 2
  let S (n : ℕ) := {x : ℂ | _root_.Dist.dist x c ∈ _root_.Set.Icc (rn n) R}
  have hSsub (n : ℕ) : S n ⊆ Metric.closedBall c R := fun x hx => hx.2
  have hSc (n : ℕ) : IsCompact (S n) :=
    (_root_.ProperSpace.isCompact_closedBall c R).of_isClosed_subset
      (isClosed_Icc.preimage (continuous_id.dist continuous_const)) (hSsub n)
  have hquad : _root_.Filter.Tendsto (fun n => ∫ x in S n, e (fn n) x) _root_.Filter.atTop (𝓝 0) :=
    tendsto_integral_quadratic_fderiv_of_eventually_lipschitz fn S hSc hK A hA
      (hfn.mono fun n hn => ⟨hn.1, hn.2.mono_left (hSsub n)⟩) hshell
  have hfixed : _root_.Filter.Tendsto (fun n => ∫ x in Metric.closedBall c R \ Metric.closedBall c (rn n),
      e f x) _root_.Filter.atTop (𝓝 0) :=
    tendsto_integral_closedBall_sdiff_of_tendsto_radius hf (Measure.addHaar_sphere _root_.MeasureTheory.MeasureSpace.volume c R) hr
  have hcoreEq : ∀ᶠ n in _root_.Filter.atTop,
      (∫ x in Metric.closedBall c (rn n), e (fn n) x) =
        ∫ x in Metric.closedBall c (rn n), e f x := by
    filter_upwards [hcore] with n hn
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [ae_mem_ball_of_measure_sphere_eq_zero
      (Measure.addHaar_sphere _root_.MeasureTheory.MeasureSpace.volume c (rn n))] with x hx
    have hgerm : fn n =ᶠ[𝓝 x] f := by
      filter_upwards [Metric.closedBall_mem_nhds_of_mem hx] with y hy
      exact hn hy
    simp only [e, hgerm.eq_of_nhds, hgerm.fderiv_eq]
  have hidentity : ∀ᶠ n in _root_.Filter.atTop,
      (∫ x in Metric.closedBall c R, e (fn n) x) =
        (∫ x in Metric.closedBall c R, e f x) -
          (∫ x in Metric.closedBall c R \ Metric.closedBall c (rn n), e f x) +
          ∫ x in S n, e (fn n) x := by
    filter_upwards [hfn, hrR, hcoreEq] with n hn hnR heq
    obtain ⟨L, hL⟩ := hn.1
    have hi := integrable_quadratic_fderiv_on_closedBall hL hK hn.2 A hA
    have hsub : Metric.closedBall c (rn n) ⊆ Metric.closedBall c R :=
      Metric.closedBall_subset_closedBall hnR
    have hfnSplit := _root_.MeasureTheory.setIntegral_sdiff measurableSet_closedBall hi hsub
    have hfSplit := _root_.MeasureTheory.setIntegral_sdiff measurableSet_closedBall hf hsub
    rw [integral_closedBall_sdiff_eq_integral_norm_annulus_complex] at hfnSplit
    change (∫ x in S n, e (fn n) x) =
      (∫ x in Metric.closedBall c R, e (fn n) x) -
        ∫ x in Metric.closedBall c (rn n), e (fn n) x at hfnSplit
    rw [heq] at hfnSplit
    linarith
  have hlim :=
    ((tendsto_const_nhds (x := ∫ x in Metric.closedBall c R, e f x)).sub hfixed).add hquad
  simp only [sub_zero, add_zero] at hlim
  apply hlim.congr'
  filter_upwards [hidentity] with n hn
  exact hn.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendsto_integral_quadratic_fderiv_of_eqOn_exhausting_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendsto_integral_quadratic_fderiv_of_eqOn_exhausting_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendsto_integral_quadratic_fderiv_of_eqOn_exhausting_closedBall ``Submission.DifferentialGeometry.Analysis.tendsto_integral_quadratic_fderiv_of_eqOn_exhausting_closedBall

end DifferentialGeometry.Analysis

end
