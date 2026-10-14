import Mathlib.Topology.Covering.AddCircle
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Calculus.Deriv.Comp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

theorem deriv_eq_of_addCircle_coe_eventuallyEq {period : ℝ} {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (heq : (fun y => (f y : AddCircle period)) =ᶠ[𝓝 x]
      (fun y => (g y : AddCircle period))) :
    deriv f x = deriv g x := by
  obtain ⟨U, hU, hxU, hinj⟩ :=
    (AddCircle.isLocalHomeomorph_coe period).isLocallyInjective (f x - g x)
  have hpoint : (f x : AddCircle period) = (g x : AddCircle period) := heq.self_of_nhds
  have hzero : ((f x - g x : ℝ) : AddCircle period) = 0 := by
    rw [AddCircle.coe_sub, hpoint, sub_self]
  have hfun : f =ᶠ[𝓝 x] (fun y => g y + (f x - g x)) := by
    filter_upwards [(hf.sub hg).eventually (hU.mem_nhds hxU), heq] with y hy heqy
    have hyzero : ((f y - g y : ℝ) : AddCircle period) = 0 := by
      rw [AddCircle.coe_sub, heqy, sub_self]
    have hconst : f y - g y = f x - g x := hinj hy hxU (hyzero.trans hzero.symm)
    exact (sub_eq_iff_eq_add.mp hconst).trans (add_comm _ _)
  rw [hfun.deriv_eq, deriv_add_const]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.deriv_eq_of_addCircle_coe_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.deriv_eq_of_addCircle_coe_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.deriv_eq_of_addCircle_coe_eventuallyEq ``Submission.DifferentialGeometry.Topology.deriv_eq_of_addCircle_coe_eventuallyEq

end DifferentialGeometry.Topology

end

section

open scoped _root_.Topology

namespace DifferentialGeometry.Analysis

theorem deriv_eq_im_div_circleExp {y : ℝ → ℝ} {x : ℝ}
    (hy : DifferentiableAt ℝ y x) :
    deriv y x =
      (deriv (fun z => Complex.exp ((2 * Real.pi * y z : ℝ) * Complex.I)) x /
        Complex.exp ((2 * Real.pi * y x : ℝ) * Complex.I)).im / (2 * Real.pi) := by
  have harg := ((hy.hasDerivAt.const_mul (2 * Real.pi)).ofReal_comp).mul_const Complex.I
  have hder := harg.cexp.deriv
  have hquot : deriv (fun z => Complex.exp ((2 * Real.pi * y z : ℝ) * Complex.I)) x /
        Complex.exp ((2 * Real.pi * y x : ℝ) * Complex.I) =
      (2 * Real.pi * deriv y x : ℝ) * Complex.I := by
    rw [hder]
    exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)
  rw [hquot, Complex.mul_I_im, Complex.ofReal_re]
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.deriv_eq_im_div_circleExp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.deriv_eq_im_div_circleExp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.deriv_eq_im_div_circleExp ``Submission.DifferentialGeometry.Analysis.deriv_eq_im_div_circleExp

end DifferentialGeometry.Analysis

end
