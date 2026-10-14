import Submission.DifferentialGeometry.Analysis.ODE.IndexForm.Basic
import Submission.DifferentialGeometry.Analysis.Sobolev.Interval.Poincare

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.intervalIntegral _root_.MeasureTheory
open scoped _root_.RealInnerProductSpace

noncomputable section

namespace DifferentialGeometry.Analysis.ODE

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem IsJacobiFieldOn.inner_velocity_position_at_right_pos
    {R : ℝ → F →L[ℝ] F} {y v : ℝ → F} {a b κ : ℝ}
    (hsol : IsJacobiFieldOn R a b y v)
    (hab : a ≤ b) (hya : y a = 0)
    (hy_ne : ¬ _root_.Set.EqOn y (fun _ => 0) (_root_.Set.Icc a b))
    (hκ : κ * (b - a) ^ 2 < (Real.pi / 2) ^ 2)
    (hupper : ∀ t ∈ _root_.Set.Ioo a b, ⟪R t (y t), y t⟫ ≤ κ * ‖y t‖ ^ 2) :
    0 < ⟪v b, y b⟫ := by
  have hablt : a < b := by
    rcases hab.lt_or_eq with hab | rfl
    · exact hab
    · exact False.elim (hy_ne fun t ht => by
        simpa only [le_antisymm ht.2 ht.1] using hya)
  have hyint : IntervalIntegrable (fun t => (⟪y t, y t⟫ : ℝ)) _root_.MeasureTheory.MeasureSpace.volume a b :=
    (hsol.contOn_fst.inner hsol.contOn_fst).intervalIntegrable_of_Icc hab
  have hvint : IntervalIntegrable (fun t => (⟪v t, v t⟫ : ℝ)) _root_.MeasureTheory.MeasureSpace.volume a b :=
    (hsol.contOn_snd.inner hsol.contOn_snd).intervalIntegrable_of_Icc hab
  have hlower : ContinuousOn (fun t => (⟪v t, v t⟫ : ℝ) - κ * ⟪y t, y t⟫)
      (_root_.Set.Icc a b) :=
    (hsol.contOn_snd.inner hsol.contOn_snd).sub
      ((hsol.contOn_fst.inner hsol.contOn_fst).const_mul κ)
  have hmono : (∫ t in a..b, (⟪v t, v t⟫ : ℝ) - κ * ⟪y t, y t⟫) ≤
      ⟪v b, y b⟫ - ⟪v a, y a⟫ := by
    apply intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab
      (hsol.contOn_snd.inner hsol.contOn_fst)
      (fun t ht => (hsol.hasDerivAt_inner hsol.deriv_fst ht).hasDerivWithinAt)
      hlower.integrableOn_Icc
    intro t ht
    unfold indexIntegrand
    simp only [real_inner_self_eq_norm_sq]
    exact sub_le_sub_left (hupper t ht) _
  rw [hya, inner_zero_right, sub_zero,
    intervalIntegral.integral_sub hvint (hyint.const_mul κ),
    intervalIntegral.integral_const_mul] at hmono
  have hp := DifferentialGeometry.Analysis.poincare_interval_lt_of_eq_zero_left hablt hsol.deriv_fst
    hsol.contOn_snd hya hy_ne hκ
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.inner_velocity_position_at_right_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.inner_velocity_position_at_right_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.inner_velocity_position_at_right_pos ``Submission.DifferentialGeometry.Analysis.ODE.IsJacobiFieldOn.inner_velocity_position_at_right_pos

end DifferentialGeometry.Analysis.ODE
