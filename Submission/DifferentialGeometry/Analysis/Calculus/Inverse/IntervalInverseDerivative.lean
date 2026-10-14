import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.Order.IntermediateValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set

namespace DifferentialGeometry.Analysis

theorem derivWithin_pos_of_left_inverse_Icc
    {f g : ℝ → ℝ} {a b : ℝ} {T : Set ℝ} (hab : a < b)
    (hf : DifferentiableOn ℝ f (_root_.Set.Icc a b)) (hg : DifferentiableOn ℝ g T)
    (hmap : _root_.Set.MapsTo f (_root_.Set.Icc a b) T) (hinv : _root_.Set.LeftInvOn g f (_root_.Set.Icc a b))
    (hfab : f a ≤ f b) {x : ℝ} (hx : x ∈ _root_.Set.Icc a b) :
    0 < derivWithin f (_root_.Set.Icc a b) x := by
  have hmono : StrictMonoOn f (_root_.Set.Icc a b) :=
    hf.continuousOn.strictMonoOn_of_injOn_Icc hab.le hfab hinv.injOn
  have hnonneg : 0 ≤ derivWithin f (_root_.Set.Icc a b) x := hmono.monotoneOn.derivWithin_nonneg
  have hcomp := (hg _ (hmap hx)).hasDerivWithinAt.comp x (hf x hx).hasDerivWithinAt hmap
  have hid : HasDerivWithinAt (fun y : ℝ ↦ y)
      (derivWithin g T (f x) * derivWithin f (_root_.Set.Icc a b) x) (_root_.Set.Icc a b) x :=
    hcomp.congr (fun y hy ↦ (hinv hy).symm) (hinv hx).symm
  have he : derivWithin g T (f x) * derivWithin f (_root_.Set.Icc a b) x = 1 :=
    (hid.derivWithin (uniqueDiffOn_Icc hab x hx)).symm.trans
      ((hasDerivWithinAt_id x (_root_.Set.Icc a b)).derivWithin (uniqueDiffOn_Icc hab x hx))
  have hne : derivWithin f (_root_.Set.Icc a b) x ≠ 0 := by
    intro hz
    rw [hz, _root_.MulZeroClass.mul_zero] at he
    exact zero_ne_one he
  exact lt_of_le_of_ne hnonneg hne.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.derivWithin_pos_of_left_inverse_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.derivWithin_pos_of_left_inverse_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.derivWithin_pos_of_left_inverse_Icc ``Submission.DifferentialGeometry.Analysis.derivWithin_pos_of_left_inverse_Icc

theorem deriv_pos_of_monotone_left_inverse
    {f g : ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hinv : Function.LeftInverse g f) (hmono : Monotone f) (x : ℝ) :
    0 < deriv f x := by
  have hcomp := (hg (f x)).hasDerivAt.comp x (hf x).hasDerivAt
  have hid : HasDerivAt (fun y : ℝ ↦ y) (deriv g (f x) * deriv f x) x :=
    hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ (hinv y).symm)
  have he : deriv g (f x) * deriv f x = 1 := hid.unique (hasDerivAt_id x)
  have hne : deriv f x ≠ 0 := by
    intro hz
    rw [hz, _root_.MulZeroClass.mul_zero] at he
    exact zero_ne_one he
  exact lt_of_le_of_ne hmono.deriv_nonneg hne.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.deriv_pos_of_monotone_left_inverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.deriv_pos_of_monotone_left_inverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.deriv_pos_of_monotone_left_inverse ``Submission.DifferentialGeometry.Analysis.deriv_pos_of_monotone_left_inverse

end DifferentialGeometry.Analysis
