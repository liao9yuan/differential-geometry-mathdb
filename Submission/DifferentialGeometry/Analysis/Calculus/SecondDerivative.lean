import Batteries.Tactic.Alias
import Mathlib.Analysis.Calculus.DerivativeTest

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Filter _root_.Set _root_.SignType _root_.Topology

namespace DifferentialGeometry

theorem second_derivative_nonneg_of_isLocalMin
    {f : ℝ → ℝ} {x : ℝ} (hmin : IsLocalMin f x)
    (hdiff : Differentiable ℝ f) :
    0 ≤ deriv (deriv f) x := by
  by_contra hnonneg
  have hsecondNeg : deriv (deriv f) x < 0 := lt_of_not_ge hnonneg
  have hfirst : deriv f x = 0 := hmin.deriv_eq_zero
  have hsign :
      ∀ᶠ y in 𝓝 x, _root_.SignType.sign (deriv f y) = _root_.SignType.sign (x - y) :=
    eventually_nhdsWithin_sign_eq_of_deriv_neg hsecondNeg hfirst
  have hderivNeg : ∀ᶠ y in 𝓝[>] x, deriv f y < 0 :=
    deriv_neg_right_of_sign_deriv (nhdsWithin_le_nhds hsign)
  have hminRight : ∀ᶠ y in 𝓝[>] x, f x ≤ f y :=
    nhdsWithin_le_nhds hmin
  have hboth : {y : ℝ | deriv f y < 0 ∧ f x ≤ f y} ∈ 𝓝[>] x :=
    hderivNeg.and hminRight
  obtain ⟨u, hxu, hu⟩ :=
    (mem_nhdsGT_iff_exists_Ioc_subset.mp hboth)
  have hanti : StrictAntiOn f (Set.Icc x u) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc x u)
      hdiff.continuous.continuousOn
    intro y hy
    rw [interior_Icc] at hy
    exact (hu ⟨hy.1, hy.2.le⟩).1
  have hdrop : f u < f x :=
    hanti (left_mem_Icc.mpr hxu.le) (right_mem_Icc.mpr hxu.le) hxu
  exact (not_le_of_gt hdrop) (hu ⟨hxu, le_rfl⟩).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.second_derivative_nonneg_of_isLocalMin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.second_derivative_nonneg_of_isLocalMin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.second_derivative_nonneg_of_isLocalMin ``Submission.DifferentialGeometry.second_derivative_nonneg_of_isLocalMin

end DifferentialGeometry

namespace DifferentialGeometry.Analysis

alias second_derivative_nonneg_of_isLocalMin := DifferentialGeometry.second_derivative_nonneg_of_isLocalMin

end DifferentialGeometry.Analysis
