/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Homeomorph.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology
open scoped _root_.ContDiff

namespace DifferentialGeometry.Manifold

def cornerSquaring (p : ℝ × ℝ) : ℝ × ℝ :=
  (2 * p.1 * p.2, p.1 ^ 2 - p.2 ^ 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.cornerSquaring then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.cornerSquaring"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.cornerSquaring ``Submission.DifferentialGeometry.Manifold.cornerSquaring

noncomputable def cornerRoot (p : ℝ × ℝ) : ℝ × ℝ :=
  (Real.sqrt ((Real.sqrt (p.1 ^ 2 + p.2 ^ 2) + p.2) / 2),
    Real.sqrt ((Real.sqrt (p.1 ^ 2 + p.2 ^ 2) - p.2) / 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.cornerRoot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.cornerRoot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.cornerRoot ``Submission.DifferentialGeometry.Manifold.cornerRoot

theorem contDiff_cornerSquaring : ContDiff ℝ ∞ cornerSquaring := by
  exact ((contDiff_const.mul contDiff_fst).mul contDiff_snd).prodMk
    ((contDiff_fst.pow 2).sub (contDiff_snd.pow 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.contDiff_cornerSquaring then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.contDiff_cornerSquaring"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.contDiff_cornerSquaring ``Submission.DifferentialGeometry.Manifold.contDiff_cornerSquaring

theorem continuous_cornerRoot : Continuous cornerRoot := by
  unfold cornerRoot
  fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.continuous_cornerRoot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.continuous_cornerRoot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.continuous_cornerRoot ``Submission.DifferentialGeometry.Manifold.continuous_cornerRoot

theorem cornerRoot_nonneg (p : ℝ × ℝ) :
    0 ≤ (cornerRoot p).1 ∧ 0 ≤ (cornerRoot p).2 :=
  ⟨Real.sqrt_nonneg _, Real.sqrt_nonneg _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.cornerRoot_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.cornerRoot_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.cornerRoot_nonneg ``Submission.DifferentialGeometry.Manifold.cornerRoot_nonneg

theorem cornerRoot_cornerSquaring {p : ℝ × ℝ} (hp : 0 ≤ p.1 ∧ 0 ≤ p.2) :
    cornerRoot (cornerSquaring p) = p := by
  have hs : Real.sqrt ((2 * p.1 * p.2) ^ 2 + (p.1 ^ 2 - p.2 ^ 2) ^ 2) =
      p.1 ^ 2 + p.2 ^ 2 := by
    rw [show (2 * p.1 * p.2) ^ 2 + (p.1 ^ 2 - p.2 ^ 2) ^ 2 =
      (p.1 ^ 2 + p.2 ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  apply Prod.ext
  · change Real.sqrt ((Real.sqrt _ + (p.1 ^ 2 - p.2 ^ 2)) / 2) = p.1
    dsimp only [cornerSquaring]
    rw [hs, show (p.1 ^ 2 + p.2 ^ 2 + (p.1 ^ 2 - p.2 ^ 2)) / 2 = p.1 ^ 2 by ring]
    exact Real.sqrt_sq hp.1
  · change Real.sqrt ((Real.sqrt _ - (p.1 ^ 2 - p.2 ^ 2)) / 2) = p.2
    dsimp only [cornerSquaring]
    rw [hs, show (p.1 ^ 2 + p.2 ^ 2 - (p.1 ^ 2 - p.2 ^ 2)) / 2 = p.2 ^ 2 by ring]
    exact Real.sqrt_sq hp.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.cornerRoot_cornerSquaring then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.cornerRoot_cornerSquaring"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.cornerRoot_cornerSquaring ``Submission.DifferentialGeometry.Manifold.cornerRoot_cornerSquaring

theorem cornerSquaring_cornerRoot {p : ℝ × ℝ} (hp : 0 ≤ p.1) :
    cornerSquaring (cornerRoot p) = p := by
  let r := Real.sqrt (p.1 ^ 2 + p.2 ^ 2)
  have hr : r ^ 2 = p.1 ^ 2 + p.2 ^ 2 := Real.sq_sqrt (by positivity)
  have habs : |p.2| ≤ r := Real.abs_le_sqrt (by nlinarith [sq_nonneg p.1])
  have hplus : 0 ≤ (r + p.2) / 2 := by have h := (abs_le.mp habs).1; linarith
  have hminus : 0 ≤ (r - p.2) / 2 := by have h := (abs_le.mp habs).2; linarith
  have hx : (cornerRoot p).1 ^ 2 = (r + p.2) / 2 := Real.sq_sqrt hplus
  have hy : (cornerRoot p).2 ^ 2 = (r - p.2) / 2 := Real.sq_sqrt hminus
  have hsq : (2 * (cornerRoot p).1 * (cornerRoot p).2) ^ 2 = p.1 ^ 2 := by
    calc
      _ = 4 * (cornerRoot p).1 ^ 2 * (cornerRoot p).2 ^ 2 := by ring
      _ = (r + p.2) * (r - p.2) := by rw [hx, hy]; ring
      _ = p.1 ^ 2 := by nlinarith [hr]
  apply Prod.ext
  · have hn := cornerRoot_nonneg p
    exact (sq_eq_sq₀ (mul_nonneg (mul_nonneg (by norm_num) hn.1) hn.2) hp).mp hsq
  · change (cornerRoot p).1 ^ 2 - (cornerRoot p).2 ^ 2 = p.2
    rw [hx, hy]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.cornerSquaring_cornerRoot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.cornerSquaring_cornerRoot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.cornerSquaring_cornerRoot ``Submission.DifferentialGeometry.Manifold.cornerSquaring_cornerRoot

noncomputable def quadrantHalfPlaneHomeomorph :
    {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} ≃ₜ {p : ℝ × ℝ | 0 ≤ p.1} where
  toFun p := ⟨cornerSquaring p.val, by
    change 0 ≤ 2 * p.val.1 * p.val.2
    exact mul_nonneg (mul_nonneg (by norm_num) p.property.1) p.property.2⟩
  invFun p := ⟨cornerRoot p.val, cornerRoot_nonneg p.val⟩
  left_inv p := Subtype.ext (cornerRoot_cornerSquaring p.property)
  right_inv p := Subtype.ext (cornerSquaring_cornerRoot p.property)
  continuous_toFun := by
    apply (contDiff_cornerSquaring.continuous.comp continuous_subtype_val).subtype_mk
  continuous_invFun := (continuous_cornerRoot.comp continuous_subtype_val).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.quadrantHalfPlaneHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.quadrantHalfPlaneHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.quadrantHalfPlaneHomeomorph ``Submission.DifferentialGeometry.Manifold.quadrantHalfPlaneHomeomorph

theorem cornerSquaring_fst_eq_zero_iff (p : ℝ × ℝ) :
    (cornerSquaring p).1 = 0 ↔ p.1 = 0 ∨ p.2 = 0 := by
  simp [cornerSquaring, mul_eq_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.cornerSquaring_fst_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.cornerSquaring_fst_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.cornerSquaring_fst_eq_zero_iff ``Submission.DifferentialGeometry.Manifold.cornerSquaring_fst_eq_zero_iff

theorem cornerSquaring_first_face_iff {p : ℝ × ℝ} (hp : 0 ≤ p.1 ∧ 0 ≤ p.2) :
    (cornerSquaring p).1 = 0 ∧ (cornerSquaring p).2 ≤ 0 ↔ p.1 = 0 := by
  constructor
  · rintro ⟨hz, hn⟩
    rcases (cornerSquaring_fst_eq_zero_iff p).mp hz with h | h
    · exact h
    · change p.1 ^ 2 - p.2 ^ 2 ≤ 0 at hn
      rw [h] at hn
      nlinarith [hp.1]
  · intro h
    simp [cornerSquaring, h, sq_nonneg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.cornerSquaring_first_face_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.cornerSquaring_first_face_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.cornerSquaring_first_face_iff ``Submission.DifferentialGeometry.Manifold.cornerSquaring_first_face_iff

theorem cornerSquaring_second_face_iff {p : ℝ × ℝ} (hp : 0 ≤ p.1 ∧ 0 ≤ p.2) :
    (cornerSquaring p).1 = 0 ∧ 0 ≤ (cornerSquaring p).2 ↔ p.2 = 0 := by
  constructor
  · rintro ⟨hz, hn⟩
    rcases (cornerSquaring_fst_eq_zero_iff p).mp hz with h | h
    · change 0 ≤ p.1 ^ 2 - p.2 ^ 2 at hn
      rw [h] at hn
      nlinarith [hp.2]
    · exact h
  · intro h
    simp [cornerSquaring, h, sq_nonneg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.cornerSquaring_second_face_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.cornerSquaring_second_face_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.cornerSquaring_second_face_iff ``Submission.DifferentialGeometry.Manifold.cornerSquaring_second_face_iff

private theorem norm_sq_pos_of_ne_zero {p : ℝ × ℝ} (hp : p ≠ 0) :
    0 < p.1 ^ 2 + p.2 ^ 2 := by
  by_contra hn
  apply hp
  apply Prod.ext
  · change p.1 = 0
    nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  · change p.2 = 0
    nlinarith [sq_nonneg p.1, sq_nonneg p.2]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Manifold.norm_sq_pos_of_ne_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Manifold.norm_sq_pos_of_ne_zero target :: scope.openDecls } }

private theorem cornerRoot_eq_first {p : ℝ × ℝ} (hp : 0 ≤ p.1)
    (ha : 0 < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) + p.2) :
    cornerRoot p = ((cornerRoot p).1, p.1 / (2 * (cornerRoot p).1)) := by
  have hx : 0 < (cornerRoot p).1 := Real.sqrt_pos.2 (by linarith)
  have h := congrArg Prod.fst (cornerSquaring_cornerRoot hp)
  refine Prod.ext rfl ?_
  apply (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hx))).mpr
  change 2 * (cornerRoot p).1 * (cornerRoot p).2 = p.1 at h
  nlinarith [h]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Manifold.cornerRoot_eq_first
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Manifold.cornerRoot_eq_first target :: scope.openDecls } }

private theorem cornerRoot_eq_second {p : ℝ × ℝ} (hp : 0 ≤ p.1)
    (ha : 0 < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) - p.2) :
    cornerRoot p = (p.1 / (2 * (cornerRoot p).2), (cornerRoot p).2) := by
  have hy : 0 < (cornerRoot p).2 := Real.sqrt_pos.2 (by linarith)
  have h := congrArg Prod.fst (cornerSquaring_cornerRoot hp)
  refine Prod.ext ?_ rfl
  apply (eq_div_iff (mul_ne_zero (by norm_num) (ne_of_gt hy))).mpr
  change 2 * (cornerRoot p).1 * (cornerRoot p).2 = p.1 at h
  nlinarith [h]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Manifold.cornerRoot_eq_second
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Manifold.cornerRoot_eq_second target :: scope.openDecls } }

theorem contDiffWithinAt_cornerRoot {p : ℝ × ℝ} (hp : 0 ≤ p.1) (hne : p ≠ 0) :
    ContDiffWithinAt ℝ ∞ cornerRoot {z : ℝ × ℝ | 0 ≤ z.1} p := by
  have hq := norm_sq_pos_of_ne_zero hne
  have hr : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) p :=
    ((contDiff_fst.pow 2).add (contDiff_snd.pow 2)).contDiffAt.sqrt (ne_of_gt hq)
  have hrpos : 0 < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := Real.sqrt_pos.2 hq
  by_cases ha : 0 < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) + p.2
  · have hx : 0 < (cornerRoot p).1 := Real.sqrt_pos.2 (by linarith)
    have hf : ContDiffAt ℝ ∞ (fun z => (cornerRoot z).1) p :=
      ((hr.add contDiff_snd.contDiffAt).div_const 2).sqrt (by linarith)
    have hg := hf.prodMk (contDiff_fst.contDiffAt.div
      (contDiff_const.contDiffAt.mul hf) (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hx)))
    refine hg.contDiffWithinAt.congr_of_eventuallyEq ?_ (cornerRoot_eq_first hp ha)
    have hu : {z : ℝ × ℝ | 0 < Real.sqrt (z.1 ^ 2 + z.2 ^ 2) + z.2} ∈ 𝓝 p :=
      (isOpen_lt continuous_const
        (((continuous_fst.pow 2).add (continuous_snd.pow 2)).sqrt.add continuous_snd)).mem_nhds ha
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hu] with z hz hza
    exact cornerRoot_eq_first hz hza
  · have hb : 0 < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) - p.2 := by linarith
    have hy : 0 < (cornerRoot p).2 := Real.sqrt_pos.2 (by linarith)
    have hf : ContDiffAt ℝ ∞ (fun z => (cornerRoot z).2) p :=
      ((hr.sub contDiff_snd.contDiffAt).div_const 2).sqrt (by linarith)
    have hg := (contDiff_fst.contDiffAt.div
      (contDiff_const.contDiffAt.mul hf)
      (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hy))).prodMk hf
    refine hg.contDiffWithinAt.congr_of_eventuallyEq ?_ (cornerRoot_eq_second hp hb)
    have hu : {z : ℝ × ℝ | 0 < Real.sqrt (z.1 ^ 2 + z.2 ^ 2) - z.2} ∈ 𝓝 p :=
      (isOpen_lt continuous_const
        (((continuous_fst.pow 2).add (continuous_snd.pow 2)).sqrt.sub continuous_snd)).mem_nhds hb
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hu] with z hz hzb
    exact cornerRoot_eq_second hz hzb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.contDiffWithinAt_cornerRoot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.contDiffWithinAt_cornerRoot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.contDiffWithinAt_cornerRoot ``Submission.DifferentialGeometry.Manifold.contDiffWithinAt_cornerRoot

theorem contDiffOn_cornerRoot :
    ContDiffOn ℝ ∞ cornerRoot {p : ℝ × ℝ | 0 ≤ p.1 ∧ p ≠ 0} := by
  intro p hp
  exact (contDiffWithinAt_cornerRoot hp.1 hp.2).mono (fun _ h => h.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.contDiffOn_cornerRoot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.contDiffOn_cornerRoot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.contDiffOn_cornerRoot ``Submission.DifferentialGeometry.Manifold.contDiffOn_cornerRoot

end DifferentialGeometry.Manifold
