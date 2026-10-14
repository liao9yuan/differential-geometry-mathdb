import Submission.DifferentialGeometry.Topology.Diffeomorph.Translation
import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.Coordinates.JacobianSign
import Mathlib.Analysis.Calculus.Deriv.MeanValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace Diffeomorph
open _root_.Diffeomorph

open _root_.Diffeomorph in
private def translateReal (c : ℝ) : ℝ ≃ₘ[ℝ] ℝ where
  toFun x := x + c
  invFun x := x - c
  left_inv x := add_sub_cancel_right x c
  right_inv x := sub_add_cancel x c
  contMDiff_toFun := contMDiff_id.add contMDiff_const
  contMDiff_invFun := contMDiff_id.sub contMDiff_const

run_cmd do
  let target := ``Submission.Diffeomorph.translateReal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Diffeomorph.translateReal target :: scope.openDecls } }

open _root_.Diffeomorph in
theorem exists_interval_diffeomorph_eq_translation_near_endpoints
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    ∃ F : ℝ ≃ₘ[ℝ] ℝ,
      F a = c ∧ F b = d ∧ (∀ r, 0 < deriv F r) ∧
      F '' _root_.Set.Icc a b = _root_.Set.Icc c d ∧
      ∃ ε₀ ε₁ : ℝ, 0 < ε₀ ∧ 0 < ε₁ ∧
        (∀ r, |r - a| ≤ ε₀ → F r = r - a + c) ∧
        ∀ r, b - ε₁ ≤ r → F r = r - b + d := by
  let x := a - b + d
  let u := (_root_.Max.max x c + d) / 2
  have hxd : x < d := by dsimp [x]; linarith
  have hu : _root_.Max.max x c < u ∧ u < d := by dsimp [u]; constructor <;> linarith [max_lt hxd hcd]
  have hxu : x < u := (le_max_left x c).trans_lt hu.1
  have hcu : c < u := (le_max_right x c).trans_lt hu.1
  let δ := (u - _root_.Max.max x c) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith [hu.1]
  have hxδ : x + δ < u := by dsimp [δ]; linarith [le_max_left x c, hu.1]
  have hcδ : c + δ < u := by dsimp [δ]; linarith [le_max_right x c, hu.1]
  obtain ⟨H, _, _, _, hmove, _, K, hK, hKu, hfix⟩ :=
    exists_isotopy_translation_in_open (_root_.ProperSpace.isCompact_closedBall x δ) isOpen_Iio (c - x) (by
      intro t ht y hy
      have hy' : |y - x| ≤ δ := by simpa only [Metric.mem_closedBall, Real.dist_eq] using hy
      change y + t * (c - x) < u
      have hyu : y < u := by linarith [(abs_le.mp hy').2]
      have hycu : y + (c - x) < u := by linarith [(abs_le.mp hy').2]
      have hm := (convex_Iio u) hyu hycu (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
      change (1 - t) * y + t * (y + (c - x)) < u at hm
      nlinarith)
  let F := (translateReal (d - b)).trans (H 1)
  have hF (r : ℝ) : F r = H 1 (r - b + d) := by change H 1 (r + (d - b)) = _; congr 1; ring
  have ha : F a = c := by
    rw [hF]
    exact (hmove 1 ⟨zero_le_one, le_rfl⟩ x (Metric.mem_closedBall_self hδ.le)).trans (by simp)
  have heq (r : ℝ) (hr : b - (d - u) ≤ r) : F r = r - b + d := by
    rw [hF]
    exact (hfix 1).1 (fun hk => (not_lt_of_ge (by linarith : u ≤ r - b + d)) (hKu hk))
  have hb : F b = d := (heq b (by linarith [hu.2])).trans (by ring)
  have hp (r : ℝ) : 0 < deriv F r := by
    have hpos := (H 1).det_fderiv_pos_of_eqOn_compl_isCompact hK (hfix 1).1 (r - b + d)
    have hder : deriv F r = deriv (H 1) (r - b + d) := by
      have h := ((H 1).contDiff.differentiable (by simp) (r - b + d)).hasDerivAt.comp r
        (((hasDerivAt_id r).sub_const b).add_const d)
      have he : (F : ℝ → ℝ) = (fun y => H 1 (y - b + d)) := funext hF
      rw [he]
      simpa only [one_mul, mul_one, Function.comp_def, id_eq] using h.deriv
    rw [hder]
    simpa only [LinearMap.det_ring, ContinuousLinearMap.coe_coe, fderiv_eq_smul_deriv, one_smul] using hpos
  refine ⟨F, ha, hb, hp, ?_, δ, d - u, hδ, sub_pos.mpr hu.2, ?_, heq⟩
  · rw [F.continuous.image_Icc_of_strictMono (strictMono_of_deriv_pos hp), ha, hb]
  · intro r hr
    rw [hF]
    have hmem : r - b + d ∈ Metric.closedBall x δ := by
      rw [Metric.mem_closedBall, Real.dist_eq]
      have he : r - b + d - x = r - a := by dsimp [x]; ring
      rwa [he]
    have h := hmove 1 ⟨zero_le_one, le_rfl⟩ (r - b + d) hmem
    exact h.trans (by change r - b + d + 1 * (c - (a - b + d)) = r - a + c; ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.exists_interval_diffeomorph_eq_translation_near_endpoints then
    throwError "Refusing to shadow existing declaration Diffeomorph.exists_interval_diffeomorph_eq_translation_near_endpoints"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.exists_interval_diffeomorph_eq_translation_near_endpoints ``Submission.Diffeomorph.exists_interval_diffeomorph_eq_translation_near_endpoints

end Diffeomorph
