import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.ContDiff

namespace Diffeomorph
open _root_.Diffeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω} {f g h : E → F}

open _root_.Diffeomorph in
def graphShear (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    Diffeomorph 𝓘(ℝ, E × F) 𝓘(ℝ, E × F) (E × F) (E × F) n where
  toEquiv := (Equiv.refl E).prodShear (fun x => Equiv.addRight (g x - f x))
  contMDiff_toFun :=
    (contDiff_fst.prodMk
      (contDiff_snd.add ((hg.sub hf).comp contDiff_fst))).contMDiff
  contMDiff_invFun :=
    (contDiff_fst.prodMk
      (contDiff_snd.add (((hg.sub hf).comp contDiff_fst).neg))).contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.graphShear then
    throwError "Refusing to shadow existing declaration Diffeomorph.graphShear"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.graphShear ``Submission.Diffeomorph.graphShear

open _root_.Diffeomorph in
@[simp] theorem graphShear_apply (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (p : E × F) : graphShear hf hg p = (p.1, p.2 + g p.1 - f p.1) := by
  apply Prod.ext
  · rfl
  · change p.2 + (g p.1 - f p.1) = p.2 + g p.1 - f p.1
    abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.graphShear_apply then
    throwError "Refusing to shadow existing declaration Diffeomorph.graphShear_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.graphShear_apply ``Submission.Diffeomorph.graphShear_apply

open _root_.Diffeomorph in
theorem graphShear_symm_apply (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (p : E × F) : (graphShear hf hg).symm p = (p.1, p.2 + f p.1 - g p.1) := by
  apply Prod.ext
  · rfl
  · change p.2 + -(g p.1 - f p.1) = p.2 + f p.1 - g p.1
    abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.graphShear_symm_apply then
    throwError "Refusing to shadow existing declaration Diffeomorph.graphShear_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.graphShear_symm_apply ``Submission.Diffeomorph.graphShear_symm_apply

open _root_.Diffeomorph in
@[simp] theorem graphShear_symm (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    (graphShear hf hg).symm = graphShear hg hf := by
  apply Diffeomorph.ext
  intro p
  rw [graphShear_symm_apply, graphShear_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.graphShear_symm then
    throwError "Refusing to shadow existing declaration Diffeomorph.graphShear_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.graphShear_symm ``Submission.Diffeomorph.graphShear_symm

open _root_.Diffeomorph in
@[simp] theorem graphShear_refl (hf : ContDiff ℝ n f) :
    graphShear hf hf = Diffeomorph.refl 𝓘(ℝ, E × F) (E × F) n := by
  apply Diffeomorph.ext
  intro p
  rw [graphShear_apply]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.graphShear_refl then
    throwError "Refusing to shadow existing declaration Diffeomorph.graphShear_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.graphShear_refl ``Submission.Diffeomorph.graphShear_refl

open _root_.Diffeomorph in
@[simp] theorem graphShear_trans (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (hh : ContDiff ℝ n h) :
    (graphShear hf hg).trans (graphShear hg hh) = graphShear hf hh := by
  apply Diffeomorph.ext
  intro p
  change graphShear hg hh (graphShear hf hg p) = graphShear hf hh p
  simp only [graphShear_apply]
  apply Prod.ext
  · rfl
  · dsimp
    abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.graphShear_trans then
    throwError "Refusing to shadow existing declaration Diffeomorph.graphShear_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.graphShear_trans ``Submission.Diffeomorph.graphShear_trans

open _root_.Diffeomorph in
theorem graphShear_apply_eq_self_iff (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (p : E × F) : graphShear hf hg p = p ↔ f p.1 = g p.1 := by
  constructor
  · intro hp
    have hs := congrArg Prod.snd hp
    rw [graphShear_apply] at hs
    change p.2 + g p.1 - f p.1 = p.2 at hs
    have heq : p.2 + g p.1 = p.2 + f p.1 := by
      simpa only [sub_add_cancel] using congrArg (fun y : F => y + f p.1) hs
    exact (add_left_cancel heq).symm
  · intro hp
    rw [graphShear_apply]
    apply Prod.ext
    · rfl
    · change p.2 + g p.1 - f p.1 = p.2
      rw [hp]
      simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.graphShear_apply_eq_self_iff then
    throwError "Refusing to shadow existing declaration Diffeomorph.graphShear_apply_eq_self_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.graphShear_apply_eq_self_iff ``Submission.Diffeomorph.graphShear_apply_eq_self_iff

open _root_.Diffeomorph in
theorem graphShear_image_graphOn (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (s : Set E) : graphShear hf hg '' Set.graphOn f s = Set.graphOn g s := by
  simp only [Set.graphOn, Set.image_image]
  congr 1
  funext x
  simp only [graphShear_apply]
  apply Prod.ext
  · rfl
  · dsimp
    abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.graphShear_image_graphOn then
    throwError "Refusing to shadow existing declaration Diffeomorph.graphShear_image_graphOn"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.graphShear_image_graphOn ``Submission.Diffeomorph.graphShear_image_graphOn

section Epigraph

variable {f g : E → ℝ}

open _root_.Diffeomorph in
theorem graphShear_image_epigraph (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (s : Set E) :
    graphShear hf hg '' {p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2} =
      {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [graphShear_apply]
    exact ⟨hq.1, by dsimp; linarith [hq.2]⟩
  · intro hp
    refine ⟨(p.1, p.2 + f p.1 - g p.1), ⟨hp.1, ?_⟩, ?_⟩
    · dsimp
      linarith [hp.2]
    · rw [graphShear_apply]
      apply Prod.ext
      · rfl
      · dsimp
        abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.graphShear_image_epigraph then
    throwError "Refusing to shadow existing declaration Diffeomorph.graphShear_image_epigraph"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.graphShear_image_epigraph ``Submission.Diffeomorph.graphShear_image_epigraph

open _root_.Diffeomorph in
theorem graphShear_image_strict_epigraph (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (s : Set E) :
    graphShear hf hg '' {p : E × ℝ | p.1 ∈ s ∧ f p.1 < p.2} =
      {p : E × ℝ | p.1 ∈ s ∧ g p.1 < p.2} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [graphShear_apply]
    exact ⟨hq.1, by dsimp; linarith [hq.2]⟩
  · intro hp
    refine ⟨(p.1, p.2 + f p.1 - g p.1), ⟨hp.1, ?_⟩, ?_⟩
    · dsimp
      linarith [hp.2]
    · rw [graphShear_apply]
      apply Prod.ext
      · rfl
      · dsimp
        abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Diffeomorph.graphShear_image_strict_epigraph then
    throwError "Refusing to shadow existing declaration Diffeomorph.graphShear_image_strict_epigraph"
  Lean.modifyEnv fun env => Lean.addAlias env `Diffeomorph.graphShear_image_strict_epigraph ``Submission.Diffeomorph.graphShear_image_strict_epigraph

end Epigraph

end Diffeomorph
