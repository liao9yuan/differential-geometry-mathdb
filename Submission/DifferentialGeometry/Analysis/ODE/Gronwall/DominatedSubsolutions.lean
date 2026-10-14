import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis.ODE

theorem sub_le_integral_of_dominated_subsolutions
    {a b K : ℝ} (hab : a ≤ b)
    {u u' r : ℕ → ℝ → ℝ} {v G H : ℝ → ℝ}
    (hcont : ∀ n, ContinuousOn (u n) (_root_.Set.Icc a b))
    (hderiv : ∀ n, ∀ t ∈ _root_.Set.Ioo a b, HasDerivWithinAt (u n) (u' n t) (_root_.Set.Ioi t) t)
    (hsub : ∀ n, ∀ t ∈ _root_.Set.Ioo a b, u' n t ≤ K * u n t + r n t)
    (hrmeas : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (r n) (volume.restrict (_root_.Set.Icc a b)))
    (hG : IntervalIntegrable G _root_.MeasureTheory.MeasureSpace.volume a b) (hH : IntervalIntegrable H _root_.MeasureTheory.MeasureSpace.volume a b)
    (huG : ∀ n, ∀ᵐ t ∂volume.restrict (_root_.Set.Icc a b), ‖u n t‖ ≤ G t)
    (hrH : ∀ n, ∀ᵐ t ∂volume.restrict (_root_.Set.Icc a b), ‖r n t‖ ≤ H t)
    (hu : ∀ t ∈ _root_.Set.Icc a b, _root_.Filter.Tendsto (fun n => u n t) _root_.Filter.atTop (𝓝 (v t)))
    (hr : ∀ᵐ t ∂volume.restrict (_root_.Set.Icc a b), _root_.Filter.Tendsto (fun n => r n t) _root_.Filter.atTop (𝓝 0)) :
    v b - v a ≤ K * ∫ t in a..b, v t := by
  have hGint : _root_.MeasureTheory.IntegrableOn G (_root_.Set.Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hG
  have hHint : _root_.MeasureTheory.IntegrableOn H (_root_.Set.Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hH
  have huit (n : ℕ) : _root_.MeasureTheory.IntegrableOn (u n) (_root_.Set.Icc a b) := (hcont n).integrableOn_Icc
  have hrit (n : ℕ) : _root_.MeasureTheory.IntegrableOn (r n) (_root_.Set.Icc a b) :=
    hHint.mono' (hrmeas n) (hrH n)
  have hlimit : ∀ᵐ t ∂volume.restrict (_root_.Set.Icc a b),
      Tendsto (fun n => u n t) _root_.Filter.atTop (𝓝 (v t)) := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    exact hu t ht
  have hulim := _root_.MeasureTheory.tendsto_integral_of_dominated_convergence G
    (fun n => (huit n).aestronglyMeasurable) hGint huG hlimit
  have hrlim := _root_.MeasureTheory.tendsto_integral_of_dominated_convergence H hrmeas hHint hrH hr
  have huleft : _root_.Filter.Tendsto (fun n => u n b - u n a) _root_.Filter.atTop (𝓝 (v b - v a)) :=
    (hu b ⟨hab, le_rfl⟩).sub (hu a ⟨le_rfl, hab⟩)
  have huright : _root_.Filter.Tendsto (fun n => K * (∫ t in a..b, u n t) + ∫ t in a..b, r n t)
      atTop (𝓝 (K * ∫ t in a..b, v t)) := by
    simp_rw [intervalIntegral.integral_of_le hab, ← _root_.MeasureTheory.integral_Icc_eq_integral_Ioc]
    simpa only [_root_.MeasureTheory.integral_zero, add_zero] using (hulim.const_mul K).add hrlim
  apply le_of_tendsto_of_tendsto huleft huright
  filter_upwards [] with n
  have hn := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
    hab (hcont n) (hderiv n) ((huit n).const_mul K |>.add (hrit n)) (hsub n)
  change u n b - u n a ≤ ∫ t in a..b, K * u n t + r n t at hn
  rw [intervalIntegral.integral_add
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr ((huit n).const_mul K))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (hrit n)),
    intervalIntegral.integral_const_mul] at hn
  exact hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.sub_le_integral_of_dominated_subsolutions then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.sub_le_integral_of_dominated_subsolutions"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.sub_le_integral_of_dominated_subsolutions ``Submission.DifferentialGeometry.Analysis.ODE.sub_le_integral_of_dominated_subsolutions

end DifferentialGeometry.Analysis.ODE
