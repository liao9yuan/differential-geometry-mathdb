import Mathlib.Analysis.Calculus.ContDiff.Deriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry

open _root_.Set
open scoped _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_ode2
    {F : E × E → E} {y : ℝ → E} {J : Set ℝ} {V : Set (E × E)}
    (hJ : IsOpen J) (hF : ContDiffOn ℝ ∞ F V)
    (hmem : ∀ t ∈ J, (y t, deriv y t) ∈ V)
    (hy₁ : ∀ t ∈ J, HasDerivAt y (deriv y t) t)
    (hy₂ : ∀ t ∈ J, HasDerivAt (deriv y) (F (y t, deriv y t)) t)
    (n : ℕ) :
    ContDiffOn ℝ n y J ∧ ContDiffOn ℝ n (deriv y) J := by
  have hdy : DifferentiableOn ℝ y J := fun t ht =>
    (hy₁ t ht).differentiableAt.differentiableWithinAt
  have hddy : DifferentiableOn ℝ (deriv y) J := fun t ht =>
    (hy₂ t ht).differentiableAt.differentiableWithinAt
  have hdd : ∀ t ∈ J, deriv (deriv y) t = F (y t, deriv y t) :=
    fun t ht => (hy₂ t ht).deriv
  induction n with
  | zero =>
    exact ⟨contDiffOn_zero.mpr hdy.continuousOn,
      contDiffOn_zero.mpr hddy.continuousOn⟩
  | succ n ih =>
    obtain ⟨ihy, ihdy⟩ := ih
    have hFn : ContDiffOn ℝ n F V := contDiffOn_infty.mp hF n
    have hpair : ContDiffOn ℝ n (fun t => (y t, deriv y t)) J := ihy.prodMk ihdy
    have hrhs : ContDiffOn ℝ n (fun t => F (y t, deriv y t)) J :=
      hFn.comp hpair fun t ht => hmem t ht
    have hddn : ContDiffOn ℝ n (deriv (deriv y)) J := hrhs.congr hdd
    exact ⟨(contDiffOn_succ_iff_deriv_of_isOpen hJ).mpr ⟨hdy, by simp, ihdy⟩,
      (contDiffOn_succ_iff_deriv_of_isOpen hJ).mpr ⟨hddy, by simp, hddn⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.contDiffOn_ode2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.contDiffOn_ode2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.contDiffOn_ode2 ``Submission.DifferentialGeometry.contDiffOn_ode2

theorem contDiffOn_infty_of_secondOrderODE
    {F : E × E → E} {y : ℝ → E} {J : Set ℝ} {V : Set (E × E)}
    (hJ : IsOpen J) (hF : ContDiffOn ℝ ∞ F V)
    (hmem : ∀ t ∈ J, (y t, deriv y t) ∈ V)
    (hy₁ : ∀ t ∈ J, HasDerivAt y (deriv y t) t)
    (hy₂ : ∀ t ∈ J, HasDerivAt (deriv y) (F (y t, deriv y t)) t) :
    ContDiffOn ℝ ∞ y J ∧ ContDiffOn ℝ ∞ (deriv y) J :=
  ⟨contDiffOn_infty.mpr fun n => (contDiffOn_ode2 hJ hF hmem hy₁ hy₂ n).1,
    contDiffOn_infty.mpr fun n => (contDiffOn_ode2 hJ hF hmem hy₁ hy₂ n).2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.contDiffOn_infty_of_secondOrderODE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.contDiffOn_infty_of_secondOrderODE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.contDiffOn_infty_of_secondOrderODE ``Submission.DifferentialGeometry.contDiffOn_infty_of_secondOrderODE

end DifferentialGeometry
