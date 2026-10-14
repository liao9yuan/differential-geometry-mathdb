import Mathlib.Analysis.Calculus.ContDiff.Deriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Analysis.ODE

open _root_.Set
open scoped _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_infty_of_hasDerivAt
    {v : ℝ → E → E} {z : ℝ → E} {J : Set ℝ}
    (hJ : IsOpen J)
    (hv : ∀ t ∈ J, ContDiffAt ℝ ∞ (Function.uncurry v) (t, z t))
    (hz : ∀ t ∈ J, HasDerivAt z (v t (z t)) t) :
    ContDiffOn ℝ ∞ z J := by
  have hdiff : DifferentiableOn ℝ z J := fun t ht =>
    (hz t ht).differentiableAt.differentiableWithinAt
  apply contDiffOn_infty.mpr
  intro n
  induction n with
  | zero => exact contDiffOn_zero.mpr hdiff.continuousOn
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one]
    apply (contDiffOn_succ_iff_deriv_of_isOpen hJ).mpr
    refine ⟨hdiff, by simp, ?_⟩
    have hrhs : ContDiffOn ℝ n (fun t => v t (z t)) J := by
      intro t ht
      exact (contDiffAt_infty.mp (hv t ht) n).comp t
        (contDiffAt_id.prodMk (ih.contDiffAt (hJ.mem_nhds ht)))
        |>.contDiffWithinAt
    exact hrhs.congr (fun t ht => (hz t ht).deriv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.contDiffOn_infty_of_hasDerivAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.contDiffOn_infty_of_hasDerivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.contDiffOn_infty_of_hasDerivAt ``Submission.DifferentialGeometry.Analysis.ODE.contDiffOn_infty_of_hasDerivAt

end DifferentialGeometry.Analysis.ODE
