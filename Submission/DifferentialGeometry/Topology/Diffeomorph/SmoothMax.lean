import Submission.DifferentialGeometry.Analysis.Calculus.SmoothMax
import Mathlib.Geometry.Manifold.Diffeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Manifold

namespace Diffeomorph
open _root_.Diffeomorph

open _root_.Diffeomorph in
noncomputable def smoothMax (ε : ℝ) : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) where
  toFun p := (p.1 - p.2, Real.smoothMax ε p.1 p.2)
  invFun p := (p.2 + (p.1 - Real.smoothAbs ε p.1) / 2,
    p.2 - (p.1 + Real.smoothAbs ε p.1) / 2)
  left_inv p := by
    apply Prod.ext <;> dsimp [Real.smoothMax] <;> ring
  right_inv p := by
    have h : p.2 + (p.1 - Real.smoothAbs ε p.1) / 2 -
        (p.2 - (p.1 + Real.smoothAbs ε p.1) / 2) = p.1 := by ring
    apply Prod.ext
    · exact h
    · dsimp [Real.smoothMax]
      rw [h]
      ring
  contMDiff_toFun := ((contDiff_fst.sub contDiff_snd).prodMk
    (Real.smoothMax.contDiff ε)).contMDiff
  contMDiff_invFun := by
    have h := (Real.smoothAbs.contDiff ε).comp
      (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : ℝ × ℝ → ℝ))
    exact ((contDiff_snd.add ((contDiff_fst.sub h).div_const 2)).prodMk
      (contDiff_snd.sub ((contDiff_fst.add h).div_const 2))).contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.smoothMax then
    throwError "Refusing to shadow existing declaration Diffeomorph.smoothMax"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.smoothMax ``Submission.Diffeomorph.smoothMax

open _root_.Diffeomorph in
@[simp] theorem smoothMax_apply (ε : ℝ) (p : ℝ × ℝ) :
    smoothMax ε p = (p.1 - p.2, Real.smoothMax ε p.1 p.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.smoothMax_apply then
    throwError "Refusing to shadow existing declaration Diffeomorph.smoothMax_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.smoothMax_apply ``Submission.Diffeomorph.smoothMax_apply

open _root_.Diffeomorph in
theorem smoothMax_symm_apply (ε : ℝ) (p : ℝ × ℝ) :
    (smoothMax ε).symm p = (p.2 + (p.1 - Real.smoothAbs ε p.1) / 2,
      p.2 - (p.1 + Real.smoothAbs ε p.1) / 2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.smoothMax_symm_apply then
    throwError "Refusing to shadow existing declaration Diffeomorph.smoothMax_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.smoothMax_symm_apply ``Submission.Diffeomorph.smoothMax_symm_apply

end Diffeomorph
