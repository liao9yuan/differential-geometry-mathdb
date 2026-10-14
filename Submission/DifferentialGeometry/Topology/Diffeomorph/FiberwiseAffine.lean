import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.ContDiff

namespace Diffeomorph
open _root_.Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

open _root_.Diffeomorph in
def fiberwiseAffine (shift scale : M → ℝ)
    (hshift : ContMDiff I 𝓘(ℝ) n shift) (hscale : ContMDiff I 𝓘(ℝ) n scale)
    (hne : ∀ p, scale p ≠ 0) :
    Diffeomorph (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (M × ℝ) (M × ℝ) n where
  toFun p := (p.1, shift p.1 + scale p.1 * p.2)
  invFun p := (p.1, (p.2 - shift p.1) / scale p.1)
  left_inv p := by
    refine Prod.ext (by rfl) ?_
    change (shift p.1 + scale p.1 * p.2 - shift p.1) / scale p.1 = p.2
    field_simp [hne p.1]
    ring
  right_inv p := by
    refine Prod.ext (by rfl) ?_
    change shift p.1 + scale p.1 * ((p.2 - shift p.1) / scale p.1) = p.2
    field_simp [hne p.1]
    ring
  contMDiff_toFun := contMDiff_fst.prodMk
    ((hshift.comp contMDiff_fst).add ((hscale.comp contMDiff_fst).mul contMDiff_snd))
  contMDiff_invFun := contMDiff_fst.prodMk
    ((contMDiff_snd.sub (hshift.comp contMDiff_fst)).div₀
      (hscale.comp contMDiff_fst) (fun p => hne p.1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.fiberwiseAffine then
    throwError "Refusing to shadow existing declaration Diffeomorph.fiberwiseAffine"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.fiberwiseAffine ``Submission.Diffeomorph.fiberwiseAffine

open _root_.Diffeomorph in
@[simp] theorem fiberwiseAffine_apply (shift scale : M → ℝ)
    (hshift : ContMDiff I 𝓘(ℝ) n shift) (hscale : ContMDiff I 𝓘(ℝ) n scale)
    (hne : ∀ p, scale p ≠ 0) (p : M × ℝ) :
    fiberwiseAffine shift scale hshift hscale hne p =
      (p.1, shift p.1 + scale p.1 * p.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.fiberwiseAffine_apply then
    throwError "Refusing to shadow existing declaration Diffeomorph.fiberwiseAffine_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.fiberwiseAffine_apply ``Submission.Diffeomorph.fiberwiseAffine_apply

open _root_.Diffeomorph in
@[simp] theorem fiberwiseAffine_symm_apply (shift scale : M → ℝ)
    (hshift : ContMDiff I 𝓘(ℝ) n shift) (hscale : ContMDiff I 𝓘(ℝ) n scale)
    (hne : ∀ p, scale p ≠ 0) (p : M × ℝ) :
    (fiberwiseAffine shift scale hshift hscale hne).symm p =
      (p.1, (p.2 - shift p.1) / scale p.1) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.fiberwiseAffine_symm_apply then
    throwError "Refusing to shadow existing declaration Diffeomorph.fiberwiseAffine_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.fiberwiseAffine_symm_apply ``Submission.Diffeomorph.fiberwiseAffine_symm_apply

end Diffeomorph

end
