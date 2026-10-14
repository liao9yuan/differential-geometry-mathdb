import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D : RealTimeInterval}

theorem lRegularizedAction_le_add_of_metric_antitone_of_scalar_time_lipschitz
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b C R T a : ℝ} (hcarrier : D.carrier = _root_.Set.Iic b) (hC : 0 ≤ C)
    (hmetric : ∀ x : M, ∀ v : TangentSpace I x,
      AntitoneOn (fun t => (S.base.metric t).inner x v v) (_root_.Set.Iic b))
    (hscalarTime : ∀ s ≤ b, ∀ t ≤ b, ∀ x : M,
      |S.scalar s x - S.scalar t x| ≤ C * |s - t|)
    (hRT : R ≤ T) (hT : T ≤ b) (ha : 0 ≤ a)
    (alpha : ℝ → M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) :
    lRegularizedAction S T alpha 0 a ≤
      lRegularizedAction S R alpha 0 a + 2 * a ^ 3 * C * (T - R) := by
  have hcont (t : ℝ) (ht : t ≤ b) :
      ContinuousOn (lRegularizedLagrangian S t alpha) (_root_.Set.Icc 0 a) := by
    have h := lRegularizedLagrangian_continuousOn_carrier S hS alpha halpha
    have hc := h.comp (s := _root_.Set.Icc 0 a) (continuous_const.prodMk continuous_id).continuousOn
      (fun s _ => by rw [hcarrier]; exact (sub_le_self _ (sq_nonneg s)).trans ht)
    simpa only [Function.comp_def, id_eq] using hc
  have hIntT : IntervalIntegrable (lRegularizedLagrangian S T alpha) _root_.MeasureTheory.MeasureSpace.volume 0 a :=
    (hcont T hT).intervalIntegrable_of_Icc ha
  have hIntR : IntervalIntegrable (lRegularizedLagrangian S R alpha) _root_.MeasureTheory.MeasureSpace.volume 0 a :=
    (hcont R (hRT.trans hT)).intervalIntegrable_of_Icc ha
  have hpoint (s : ℝ) (hs : s ∈ _root_.Set.Icc 0 a) :
      lRegularizedLagrangian S T alpha s ≤
        lRegularizedLagrangian S R alpha s + 2 * a ^ 2 * C * (T - R) := by
    have hTs : T - s ^ 2 ≤ b := (sub_le_self _ (sq_nonneg s)).trans hT
    have hRs : R - s ^ 2 ≤ b := (sub_le_sub_right hRT _).trans hTs
    have hkin := hmetric (alpha s) (lVelocity alpha s) hRs hTs (sub_le_sub_right hRT _)
    have hscal := hscalarTime (T - s ^ 2) hTs (R - s ^ 2) hRs (alpha s)
    have hdiff : T - s ^ 2 - (R - s ^ 2) = T - R := by ring
    rw [hdiff, abs_of_nonneg (sub_nonneg.mpr hRT)] at hscal
    have hupper : S.scalar (T - s ^ 2) (alpha s) ≤
        S.scalar (R - s ^ 2) (alpha s) + C * (T - R) := by
      linarith [le_abs_self (S.scalar (T - s ^ 2) (alpha s) -
        S.scalar (R - s ^ 2) (alpha s))]
    have hsquare : s ^ 2 ≤ a ^ 2 := (sq_le_sq₀ hs.1 ha).mpr hs.2
    have hmul := mul_le_mul_of_nonneg_left hupper (by positivity : 0 ≤ 2 * s ^ 2)
    have herr := mul_le_mul_of_nonneg_right hsquare
      (mul_nonneg hC (sub_nonneg.mpr hRT))
    change (1 / 2 : ℝ) * _ + 2 * s ^ 2 * _ ≤
      (1 / 2 : ℝ) * _ + 2 * s ^ 2 * _ + _
    nlinarith
  have hint := intervalIntegral.integral_mono_on ha hIntT
    (hIntR.add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_add hIntR intervalIntegrable_const,
    intervalIntegral.integral_const] at hint
  simpa only [lRegularizedAction, sub_zero, smul_eq_mul, mul_assoc, mul_left_comm,
    mul_comm, pow_succ] using hint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_le_add_of_metric_antitone_of_scalar_time_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_le_add_of_metric_antitone_of_scalar_time_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_le_add_of_metric_antitone_of_scalar_time_lipschitz ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_le_add_of_metric_antitone_of_scalar_time_lipschitz

end DifferentialGeometry.PDE.RicciFlow.Perelman
