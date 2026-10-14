import Submission.DifferentialGeometry.Topology.Homeomorph.AffinePeriodicCompression
import Submission.DifferentialGeometry.Topology.LoopSpace.RadialHomeomorphism.Plane
import Submission.DifferentialGeometry.Topology.LoopSpace.AffineLift
import Submission.DifferentialGeometry.Topology.LoopSpace.RadialHomeomorphism

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open _root_.Set
open scoped _root_.NNReal

namespace DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Analysis

theorem exists_radial_homeomorph_compresses_circle_arc
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ e : ℂ ≃ₜ ℂ, e 0 = 0 ∧ (∀ z, ‖e z‖ = ‖z‖) ∧
      ∀ t ∈ _root_.Set.Icc (0 : ℝ) (3 / 4), ∀ r : ℝ, 0 < r →
        e (r • (AddCircle.toCircle (t : loopCircle) : ℂ)) =
          r • (AddCircle.toCircle ((q * t : ℝ) : loopCircle) : ℂ) := by
  obtain ⟨F, L, hFp, hF, hFi, hFt⟩ := exists_affinePeriodic_homeomorph_eq_mul_on_Icc hq hq1
  let κ := affineCircleHomeomorph F hFp
  obtain ⟨hκ, hκi⟩ := affineCircleHomeomorph_lipschitz F hFp hF hFi
  obtain ⟨K, hK⟩ := geometricCircleHomeomorph_lipschitz κ hκ
  obtain ⟨L', hL'⟩ := geometricCircleHomeomorph_lipschitz κ.symm hκi
  rw [← geometricCircleHomeomorph_symm] at hL'
  let e := radialHomeomorph (geometricCircleHomeomorph κ) hK hL'
  refine ⟨e, radialExtension_zero _, radialHomeomorph_norm _ _ _, ?_⟩
  intro t ht r hr
  change radialExtension (geometricCircleHomeomorph κ)
    (r • (AddCircle.toCircle (t : loopCircle) : ℂ)) = _
  rw [radialExtension, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hr.le,
    radialDirection_pos_smul hr, geometricCircleHomeomorph_boundary]
  change r • (AddCircle.toCircle (affineCircleHomeomorph F hFp (t : loopCircle)) : ℂ) = _
  rw [show affineCircleHomeomorph F hFp (t : loopCircle) = (F t : loopCircle) from rfl,
    hFt t ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_radial_homeomorph_compresses_circle_arc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_radial_homeomorph_compresses_circle_arc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_radial_homeomorph_compresses_circle_arc ``Submission.DifferentialGeometry.Topology.exists_radial_homeomorph_compresses_circle_arc

end DifferentialGeometry.Topology

end

end

section

noncomputable section
open _root_.Set

namespace DifferentialGeometry.Topology

private theorem coe_toCircle_zero : (AddCircle.toCircle (0 : loopCircle) : ℂ) = 1 := by simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.coe_toCircle_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.coe_toCircle_zero target :: scope.openDecls } }

private theorem coe_toCircle_quarter :
    (AddCircle.toCircle ((1 / 4 : ℝ) : loopCircle) : ℂ) = Complex.I := by
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  norm_num
  have he : (2 * (Real.pi : ℂ) * (1 / 4)) * Complex.I =
      (Real.pi / 2 : ℂ) * Complex.I := by ring
  rw [he, Complex.exp_pi_div_two_mul_I]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.coe_toCircle_quarter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.coe_toCircle_quarter target :: scope.openDecls } }

private theorem coe_toCircle_half :
    (AddCircle.toCircle ((1 / 2 : ℝ) : loopCircle) : ℂ) = -1 := by
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  norm_num
  have he : (2 * (Real.pi : ℂ) * (1 / 2)) * Complex.I =
      Real.pi * Complex.I := by ring
  rw [he, Complex.exp_pi_mul_I]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.coe_toCircle_half
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.coe_toCircle_half target :: scope.openDecls } }

private theorem coe_toCircle_three_quarters :
    (AddCircle.toCircle ((3 / 4 : ℝ) : loopCircle) : ℂ) = -Complex.I := by
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  norm_num
  have he : (2 * (Real.pi : ℂ) * (3 / 4)) * Complex.I =
      Real.pi * Complex.I + (Real.pi / 2 : ℂ) * Complex.I := by ring
  rw [he, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_pi_div_two_mul_I, neg_one_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.coe_toCircle_three_quarters
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.coe_toCircle_three_quarters target :: scope.openDecls } }

private theorem pow_coe_toCircle_scaled
    {m : ℕ} (hm : m ≠ 0) (t : ℝ) :
    (AddCircle.toCircle (((2 / (m : ℝ)) * t : ℝ) : loopCircle) : ℂ) ^ m =
      Complex.exp ((4 * Real.pi * t : ℝ) * Complex.I) := by
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp, ← Complex.exp_nat_mul]
  congr 1
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  push_cast
  field_simp
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.pow_coe_toCircle_scaled
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.pow_coe_toCircle_scaled target :: scope.openDecls } }

private theorem scaled_angle_half :
    Complex.exp ((4 * Real.pi * (1 / 2) : ℝ) * Complex.I) = 1 := by
  have he : ((4 * Real.pi * (1 / 2) : ℝ) : ℂ) * Complex.I =
      2 * Real.pi * Complex.I := by push_cast; ring
  rw [he, Complex.exp_two_pi_mul_I]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.scaled_angle_half
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.scaled_angle_half target :: scope.openDecls } }

private theorem scaled_angle_quarter :
    Complex.exp ((4 * Real.pi * (1 / 4) : ℝ) * Complex.I) = -1 := by
  have he : ((4 * Real.pi * (1 / 4) : ℝ) : ℂ) * Complex.I =
      Real.pi * Complex.I := by push_cast; ring
  rw [he, Complex.exp_pi_mul_I]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.scaled_angle_quarter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.scaled_angle_quarter target :: scope.openDecls } }

private theorem scaled_angle_three_quarters :
    Complex.exp ((4 * Real.pi * (3 / 4) : ℝ) * Complex.I) = -1 := by
  have he : ((4 * Real.pi * (3 / 4) : ℝ) : ℂ) * Complex.I =
      2 * Real.pi * Complex.I + Real.pi * Complex.I := by push_cast; ring
  rw [he, Complex.exp_add, Complex.exp_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.scaled_angle_three_quarters
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.scaled_angle_three_quarters target :: scope.openDecls } }

theorem exists_homeomorph_with_alternating_power_rays {m : ℕ} (hm : 2 ≤ m) :
    ∃ e : (ℝ × ℝ) ≃ₜ ℂ, e 0 = 0 ∧
      (∀ t : ℝ, t ≠ 0 → 0 < (e (t, 0) ^ m).re) ∧
      ∀ t : ℝ, t ≠ 0 → (e (0, t) ^ m).re < 0 := by
  have hm0 : m ≠ 0 := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  obtain ⟨e, he0, _, he⟩ := exists_radial_homeomorph_compresses_circle_arc
    (div_pos (by norm_num : (0 : ℝ) < 2) hmR)
    ((div_le_one hmR).mpr (by exact_mod_cast hm))
  let E := Complex.equivRealProdCLM.symm.toHomeomorph.trans e
  have hE (x y : ℝ) : E (x, y) = e ((x : ℂ) + (y : ℂ) * Complex.I) := by
    change e (Complex.equivRealProdCLM.symm (x, y)) = _
    rw [Complex.equivRealProdCLM_symm_apply]
  refine ⟨E, ?_, ?_, ?_⟩
  · change E (0, 0) = 0
    simpa only [hE, Complex.ofReal_zero, _root_.MulZeroClass.zero_mul, add_zero] using he0
  · intro t ht
    rcases lt_or_gt_of_ne ht with ht | ht
    · have hh := he (1 / 2) (by constructor <;> norm_num) (-t) (by linarith)
      rw [coe_toCircle_half] at hh
      have he' : E (t, 0) = e ((-t) • (-1 : ℂ)) := by rw [hE]; simp [Complex.real_smul]
      rw [he', hh, Complex.real_smul, mul_pow, pow_coe_toCircle_scaled hm0]
      rw [scaled_angle_half, mul_one, ← Complex.ofReal_pow, Complex.ofReal_re]
      exact pow_pos (by linarith : 0 < -t) m
    · have hh := he 0 (by constructor <;> norm_num) t ht
      simp only [QuotientAddGroup.mk_zero, coe_toCircle_zero, _root_.MulZeroClass.mul_zero] at hh
      have he' : E (t, 0) = e (t • (1 : ℂ)) := by rw [hE]; simp
      rw [he', hh, Complex.real_smul, mul_one, ← Complex.ofReal_pow, Complex.ofReal_re]
      exact pow_pos ht m
  · intro t ht
    rcases lt_or_gt_of_ne ht with ht | ht
    · have hh := he (3 / 4) (by constructor <;> norm_num) (-t) (by linarith)
      rw [coe_toCircle_three_quarters] at hh
      have he' : E (0, t) = e ((-t) • (-Complex.I)) := by rw [hE]; simp [Complex.real_smul]
      rw [he', hh, Complex.real_smul, mul_pow, pow_coe_toCircle_scaled hm0]
      rw [scaled_angle_three_quarters, mul_neg_one, Complex.neg_re,
        ← Complex.ofReal_pow, Complex.ofReal_re]
      exact neg_neg_of_pos (pow_pos (by linarith : 0 < -t) m)
    · have hh := he (1 / 4) (by constructor <;> norm_num) t ht
      rw [coe_toCircle_quarter] at hh
      have he' : E (0, t) = e (t • Complex.I) := by rw [hE]; simp [Complex.real_smul]
      rw [he', hh, Complex.real_smul, mul_pow, pow_coe_toCircle_scaled hm0]
      rw [scaled_angle_quarter, mul_neg_one, Complex.neg_re,
        ← Complex.ofReal_pow, Complex.ofReal_re]
      exact neg_neg_of_pos (pow_pos ht m)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_homeomorph_with_alternating_power_rays then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_homeomorph_with_alternating_power_rays"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_homeomorph_with_alternating_power_rays ``Submission.DifferentialGeometry.Topology.exists_homeomorph_with_alternating_power_rays

end DifferentialGeometry.Topology

end

end
