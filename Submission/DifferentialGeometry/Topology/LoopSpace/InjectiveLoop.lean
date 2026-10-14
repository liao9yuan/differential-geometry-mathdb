/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.BasedCircle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology

open _root_.Set

variable {X : Type*} [TopologicalSpace X]

theorem injective_trans {a b c : X} {p : Path a b} {q : Path b c}
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hpq : Set.range p ∩ Set.range q ⊆ {b}) : Function.Injective (p.trans q) := by
  intro s t hst
  simp only [Path.trans_apply] at hst
  split_ifs at hst with hs ht ht
  · have h := congrArg Subtype.val (hp hst)
    simp only at h
    exact Subtype.ext (by linarith)
  · have hmem : p _ ∈ Set.range p ∩ Set.range q := ⟨⟨_, rfl⟩, ⟨_, hst.symm⟩⟩
    have hb : p _ = b := hpq hmem
    have hs1 := congrArg Subtype.val (hp (hb.trans p.target.symm))
    have ht0 := congrArg Subtype.val (hq ((hst.symm.trans hb).trans q.source.symm))
    simp only [Set.Icc.coe_one, Set.Icc.coe_zero] at hs1 ht0
    exact absurd (by linarith : (t : ℝ) ≤ 1 / 2) ht
  · have hmem : p _ ∈ Set.range p ∩ Set.range q := ⟨⟨_, rfl⟩, ⟨_, hst⟩⟩
    have hb : p _ = b := hpq hmem
    have hs1 := congrArg Subtype.val (hp (hb.trans p.target.symm))
    have ht0 := congrArg Subtype.val (hq ((hst.trans hb).trans q.source.symm))
    simp only [Set.Icc.coe_one, Set.Icc.coe_zero] at hs1 ht0
    exact absurd (by linarith : (s : ℝ) ≤ 1 / 2) hs
  · have h := congrArg Subtype.val (hq hst)
    simp only at h
    exact Subtype.ext (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.injective_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.injective_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.injective_trans ``Submission.DifferentialGeometry.Topology.injective_trans

theorem pathToCircle_trans_injective {a b : X} {p : Path a b} {q : Path b a}
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hpq : Set.range p ∩ Set.range q ⊆ {a, b}) :
    Function.Injective (pathToCircle (p.trans q)) := by
  intro θ₁ θ₂ hθ
  obtain ⟨s, rfl⟩ := unitInterval_to_loopCircle_surjective θ₁
  obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ₂
  rw [pathToCircle_coe, pathToCircle_coe] at hθ
  have hcoe : ∀ r₁ r₂ : unitInterval, (r₁ : ℝ) = (r₂ : ℝ) →
      ((r₁ : ℝ) : loopCircle) = ((r₂ : ℝ) : loopCircle) := fun _ _ h => by rw [h]
  have hends : ((0 : ℝ) : loopCircle) = ((1 : ℝ) : loopCircle) :=
    (AddCircle.coe_period (1 : ℝ)).symm
  simp only [Path.trans_apply] at hθ
  split_ifs at hθ with hs ht ht
  · exact hcoe s t (by linarith [congrArg Subtype.val (hp hθ)])
  · have hmem : p _ ∈ Set.range p ∩ Set.range q := ⟨⟨_, rfl⟩, ⟨_, hθ.symm⟩⟩
    rcases hpq hmem with hval | hval
    · have hs0 := congrArg Subtype.val (hp (hval.trans p.source.symm))
      have ht1 := congrArg Subtype.val (hq ((hθ.symm.trans hval).trans q.target.symm))
      simp only [Set.Icc.coe_one, Set.Icc.coe_zero] at hs0 ht1
      have hs' : (s : ℝ) = 0 := by linarith
      have ht' : (t : ℝ) = 1 := by linarith
      change ((s : ℝ) : loopCircle) = ((t : ℝ) : loopCircle)
      rw [hs', ht']
      exact hends
    · rw [_root_.Set.mem_singleton_iff] at hval
      have hs1 := congrArg Subtype.val (hp (hval.trans p.target.symm))
      have ht0 := congrArg Subtype.val (hq ((hθ.symm.trans hval).trans q.source.symm))
      simp only [Set.Icc.coe_one, Set.Icc.coe_zero] at hs1 ht0
      exact absurd (by linarith : (t : ℝ) ≤ 1 / 2) ht
  · have hmem : p _ ∈ Set.range p ∩ Set.range q := ⟨⟨_, rfl⟩, ⟨_, hθ⟩⟩
    rcases hpq hmem with hval | hval
    · have ht0 := congrArg Subtype.val (hp (hval.trans p.source.symm))
      have hs1 := congrArg Subtype.val (hq ((hθ.trans hval).trans q.target.symm))
      simp only [Set.Icc.coe_one, Set.Icc.coe_zero] at hs1 ht0
      have hs' : (s : ℝ) = 1 := by linarith
      have ht' : (t : ℝ) = 0 := by linarith
      change ((s : ℝ) : loopCircle) = ((t : ℝ) : loopCircle)
      rw [hs', ht']
      exact hends.symm
    · rw [_root_.Set.mem_singleton_iff] at hval
      have ht1 := congrArg Subtype.val (hp (hval.trans p.target.symm))
      have hs0 := congrArg Subtype.val (hq ((hθ.trans hval).trans q.source.symm))
      simp only [Set.Icc.coe_one, Set.Icc.coe_zero] at ht1 hs0
      exact absurd (by linarith : (s : ℝ) ≤ 1 / 2) hs
  · exact hcoe s t (by linarith [congrArg Subtype.val (hq hθ)])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathToCircle_trans_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathToCircle_trans_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathToCircle_trans_injective ``Submission.DifferentialGeometry.Topology.pathToCircle_trans_injective

theorem pathToCircle_surjective {x : X} (ℓ : Path x x) (hrange : Set.range ℓ = Set.univ) :
    Function.Surjective (pathToCircle ℓ) := by
  intro y
  obtain ⟨t, ht⟩ : y ∈ Set.range ℓ := hrange ▸ Set.mem_univ y
  exact ⟨((t : ℝ) : loopCircle), (pathToCircle_coe ℓ t).trans ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.pathToCircle_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.pathToCircle_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.pathToCircle_surjective ``Submission.DifferentialGeometry.Topology.pathToCircle_surjective

end DifferentialGeometry.Topology
