/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Covering.SectionSplit
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Data.Set.Card

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.unitInterval

namespace DifferentialGeometry.Topology.Covering

variable {B C : Type*} [TopologicalSpace B] [TopologicalSpace C]

theorem injective_of_continuous_section [PreconnectedSpace C] [T2Space C]
    {p : C → B} (hp : IsLocalHomeomorph p) (s : C(B, C))
    (hs : Function.RightInverse s p) : Function.Injective p := by
  have heq : _root_.Set.range s = {x | s (p x) = x} := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      change s (p (s b)) = s b
      rw [hs]
    · exact fun hx => ⟨p x, hx⟩
  have hclosed : IsClosed (_root_.Set.range s) := by
    rw [heq]
    exact isClosed_eq (s.continuous.comp hp.continuous) continuous_id
  have hclopen : IsClopen (_root_.Set.range s) :=
    ⟨hclosed, (isOpenEmbedding_section hp s hs).isOpen_range⟩
  intro x y hxy
  have hrange : _root_.Set.range s = univ := hclopen.eq_univ ⟨s (p x), _root_.Set.mem_range_self _⟩
  obtain ⟨a, rfl⟩ := hrange.symm ▸ _root_.Set.mem_univ x
  obtain ⟨b, rfl⟩ := hrange.symm ▸ _root_.Set.mem_univ y
  exact congrArg s ((hs a).symm.trans (hxy.trans (hs b)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Covering.injective_of_continuous_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Covering.injective_of_continuous_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Covering.injective_of_continuous_section ``Submission.DifferentialGeometry.Topology.Covering.injective_of_continuous_section

theorem exists_continuous_section_of_homotopic_lift
    {p : C → B} (hp : IsCoveringMap p) {f : C(B, B)}
    (H : ContinuousMap.Homotopy f (ContinuousMap.id B)) (s : C(B, C))
    (hs : ∀ x, p (s x) = f x) : ∃ t : C(B, C), Function.RightInverse t p := by
  have hzero : ∀ x, H (0, x) = p (s x) := fun x => (H.apply_zero x).trans (hs x).symm
  let L := hp.liftHomotopy H.toContinuousMap s hzero
  refine ⟨⟨fun x => L (1, x), L.continuous.comp (continuous_const.prodMk continuous_id)⟩, ?_⟩
  intro x
  exact (congrFun (hp.liftHomotopy_lifts H.toContinuousMap s hzero) (1, x)).trans (H.apply_one x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Covering.exists_continuous_section_of_homotopic_lift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Covering.exists_continuous_section_of_homotopic_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Covering.exists_continuous_section_of_homotopic_lift ``Submission.DifferentialGeometry.Topology.Covering.exists_continuous_section_of_homotopic_lift

theorem not_exists_continuous_section_of_fiber_card_two
    [PreconnectedSpace C] [T2Space C] [Nonempty B]
    {p : C → B} (hp : IsCoveringMap p) (hcard : ∀ x, (p ⁻¹' {x}).encard = 2) :
    ¬∃ s : C(B, C), Function.RightInverse s p := by
  rintro ⟨s, hs⟩
  have hinj := injective_of_continuous_section hp.isLocalHomeomorph s hs
  let x : B := Classical.choice inferInstance
  have hle : (p ⁻¹' {x}).encard ≤ 1 := Set.encard_le_one_iff_subsingleton.mpr
    (fun a ha b hb => hinj (ha.trans hb.symm))
  rw [hcard] at hle
  norm_num at hle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Covering.not_exists_continuous_section_of_fiber_card_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Covering.not_exists_continuous_section_of_fiber_card_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Covering.not_exists_continuous_section_of_fiber_card_two ``Submission.DifferentialGeometry.Topology.Covering.not_exists_continuous_section_of_fiber_card_two

end DifferentialGeometry.Topology.Covering
