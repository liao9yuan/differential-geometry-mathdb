/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
/-
Modified for this project; see MODIFICATIONS.md for the local changes.
-/
import Submission.DifferentialGeometry.External.Schoenflies.Subarc
import Submission.DifferentialGeometry.External.Schoenflies.Concatenate

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Two points cut a Jordan curve into two arcs

Two distinct points of a Jordan curve cut it into two arcs between them, which cover the
curve and meet in exactly those two points. This is the converse of
`IsJordanCurve.of_two_arcs`, and the harder direction.

The whole argument is carried by the loop's **parameters**; the circle never appears. Pull the
two points back to parameters `s` and `t` short of the finish — `parameter_before_finish`,
which replaces a parameter at the finish by the start, the only use the closing condition gets
— and order them, say `s < t`. Then the two pieces are what the loop makes of the parameters
*between* `s` and `t` and of the parameters *outside* them:

* the middle piece `f '' Icc s t` is a subarc, produced by `Subarc.lean`'s
  `isArcBetween_subarc`, whose injectivity hypothesis is confined to the traversed interval
  and so survives a loop;
* the outside piece `f '' Icc 0 s ∪ f '' Icc t 1` is two end intervals glued where the loop
  closes up, produced by `Concatenate.lean`'s `IsArcBetween.concatenate`.

That asymmetry — one subarc and one concatenation — is inherent to a parameter interval with
a seam in it, and is not worth fighting. It costs one case split, at `s = 0`, where the front
interval degenerates to a point that the back piece already carries at its far end.

Both halves of the conclusion are then facts about intervals of reals. Covering is the
three-way split of `[0,1]` around two parameters, which is the linearity of the order and
nothing else. Meeting is injectivity off the finish, applied on each of the three pieces; the
one case that needs the loop rather than an arc is an outside parameter *at* the finish, which
carries the same point as the start and so lands back on `s`.

## Blueprint

* `lem:jordan-circle` — "any two distinct points of `C` divide it into two simple arcs having
  exactly those points in common". `IsJordanCurve.two_arcs` is that clause, proved directly
  from the parametrisation instead of through the model curve, so it does not wait on the
  loop-to-circle bridge.
* `IsLoop.two_arcs_at_parameters` — the parameter-level form the clause is assembled from.
-/

open _root_.Set _root_.unitInterval

namespace Schoenflies

namespace IsLoop

variable {f : ℝ → Plane} {s t : ℝ}

/-! ### Parameters short of the finish

A loop is injective on `[0, 1)` only, so every statement below has to keep its parameters
away from `1`. These two lemmas are the interface to that: one says injectivity holds as soon
as neither parameter is the finish, the other says the finish can always be avoided. -/

/-- Two parameters short of the finish carrying the same point are equal. This is `IsLoop.injOn`
with the half-open interval spelled as "in `[0,1]` and not `1`", which is the form every use
below produces. -/
theorem injective_before_finish (hf : IsLoop f) {u v : ℝ} (hu : u ∈ I) (hv : v ∈ I)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (h : f u = f v) : u = v :=
  hf.injOn ⟨hu.1, hu.2.lt_of_ne hu1⟩ ⟨hv.1, hv.2.lt_of_ne hv1⟩ h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.injective_before_finish then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.injective_before_finish"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.injective_before_finish ``Submission.Schoenflies.IsLoop.injective_before_finish

/-- **Every point of the curve has a parameter short of the finish.** A parameter at the finish
is replaced by the start, which carries the same point. This is the only use the closing
condition gets. -/
theorem parameter_before_finish (hf : IsLoop f) {p : Plane} (hp : p ∈ f '' I) :
    ∃ u ∈ I, u ≠ 1 ∧ f u = p := by
  obtain ⟨u, hu, rfl⟩ := hp
  rcases eq_or_ne u 1 with rfl | hu1
  · exact ⟨0, zero_mem_I, one_ne_zero.symm, hf.closes⟩
  · exact ⟨u, hu, hu1, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.parameter_before_finish then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.parameter_before_finish"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.parameter_before_finish ``Submission.Schoenflies.IsLoop.parameter_before_finish

/-- The start and the finish are the same point of the curve; recorded in the direction the
proofs below read it. -/
theorem finish_eq_start (hf : IsLoop f) : f 1 = f 0 := hf.closes.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.finish_eq_start then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.finish_eq_start"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.finish_eq_start ``Submission.Schoenflies.IsLoop.finish_eq_start

/-! ### The three pieces of parameters

Two parameters `s < t` cut `[0, 1]` into the middle interval `[s, t]` and the two end
intervals `[0, s]` and `[t, 1]`. Each piece needs the loop to be injective on its own
parameters. On the middle and the front that is injectivity off the finish, since neither
contains it; the back piece *does* contain the finish, and there the extra argument is that
the only other parameter carrying `f 1` is the start, which lies strictly before `t`. -/

theorem front_subset_I (hs : s ∈ I) : _root_.Set.Icc 0 s ⊆ I := _root_.Set.Icc_subset_Icc le_rfl hs.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.front_subset_I then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.front_subset_I"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.front_subset_I ``Submission.Schoenflies.IsLoop.front_subset_I

theorem middle_subset_I (hs : s ∈ I) (ht : t ∈ I) : _root_.Set.Icc s t ⊆ I := _root_.Set.Icc_subset_Icc hs.1 ht.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.middle_subset_I then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.middle_subset_I"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.middle_subset_I ``Submission.Schoenflies.IsLoop.middle_subset_I

theorem back_subset_I (ht : t ∈ I) : _root_.Set.Icc t 1 ⊆ I := _root_.Set.Icc_subset_Icc ht.1 le_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.back_subset_I then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.back_subset_I"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.back_subset_I ``Submission.Schoenflies.IsLoop.back_subset_I

/-- Injectivity on the front piece: no parameter of `[0, s]` is the finish, because `s` is
not. -/
theorem injective_on_front (hf : IsLoop f) (hs : s ∈ I) (hs1 : s ≠ 1) : _root_.Set.InjOn f (_root_.Set.Icc 0 s) := by
  have hs' : s < 1 := hs.2.lt_of_ne hs1
  intro u hu v hv h
  exact hf.injective_before_finish (front_subset_I hs hu) (front_subset_I hs hv)
    (ne_of_lt (lt_of_le_of_lt hu.2 hs')) (ne_of_lt (lt_of_le_of_lt hv.2 hs')) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.injective_on_front then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.injective_on_front"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.injective_on_front ``Submission.Schoenflies.IsLoop.injective_on_front

/-- Injectivity on the middle piece: no parameter of `[s, t]` is the finish, because `t` is
not. -/
theorem injective_on_middle (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (ht1 : t ≠ 1) :
    InjOn f (_root_.Set.Icc s t) := by
  have ht' : t < 1 := ht.2.lt_of_ne ht1
  intro u hu v hv h
  exact hf.injective_before_finish (middle_subset_I hs ht hu) (middle_subset_I hs ht hv)
    (ne_of_lt (lt_of_le_of_lt hu.2 ht')) (ne_of_lt (lt_of_le_of_lt hv.2 ht')) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.injective_on_middle then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.injective_on_middle"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.injective_on_middle ``Submission.Schoenflies.IsLoop.injective_on_middle

/-- On the back piece the finish is the *only* parameter carrying `f 1`. A second one would be
the start, by injectivity off the finish and the closing condition — but the start lies
strictly before `t`. -/
theorem back_at_finish (hf : IsLoop f) (ht : t ∈ I) (ht0 : 0 < t) {w : ℝ} (hw : w ∈ _root_.Set.Icc t 1)
    (h : f w = f 1) : w = 1 := by
  by_contra hw1
  have : w = 0 :=
    hf.injective_before_finish (back_subset_I ht hw) zero_mem_I hw1 one_ne_zero.symm
      (h.trans hf.finish_eq_start)
  exact absurd (this ▸ hw.1) (not_le.mpr ht0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.back_at_finish then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.back_at_finish"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.back_at_finish ``Submission.Schoenflies.IsLoop.back_at_finish

/-- Injectivity on the back piece. Unlike the other two this piece contains the finish, so
injectivity off the finish is not enough on its own; `back_at_finish` supplies the rest. -/
theorem injective_on_back (hf : IsLoop f) (ht : t ∈ I) (ht0 : 0 < t) : _root_.Set.InjOn f (_root_.Set.Icc t 1) := by
  intro u hu v hv h
  rcases eq_or_ne u 1 with rfl | hu1
  · exact (hf.back_at_finish ht ht0 hv h.symm).symm
  · rcases eq_or_ne v 1 with rfl | hv1
    · exact hf.back_at_finish ht ht0 hu h
    · exact hf.injective_before_finish (back_subset_I ht hu) (back_subset_I ht hv) hu1 hv1 h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.injective_on_back then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.injective_on_back"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.injective_on_back ``Submission.Schoenflies.IsLoop.injective_on_back

/-! ### The three pieces are arcs -/

/-- The middle piece is an arc between the two cut points. -/
theorem middle_IsArcBetween (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (ht1 : t ≠ 1)
    (hst : s < t) : IsArcBetween (f '' _root_.Set.Icc s t) (f s) (f t) := by
  rw [← _root_.Set.uIcc_of_le hst.le]
  refine isArcBetween_subarc hf.continuousOn ?_ hs ht (ne_of_lt hst)
  rw [_root_.Set.uIcc_of_le hst.le]
  exact hf.injective_on_middle hs ht ht1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.middle_IsArcBetween then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.middle_IsArcBetween"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.middle_IsArcBetween ``Submission.Schoenflies.IsLoop.middle_IsArcBetween

/-- The front piece is an arc from the start to the first cut point. -/
theorem front_IsArcBetween (hf : IsLoop f) (hs : s ∈ I) (hs1 : s ≠ 1) (hs0 : 0 < s) :
    IsArcBetween (f '' _root_.Set.Icc 0 s) (f 0) (f s) := by
  rw [← _root_.Set.uIcc_of_le hs0.le]
  refine isArcBetween_subarc hf.continuousOn ?_ zero_mem_I hs (ne_of_lt hs0)
  rw [_root_.Set.uIcc_of_le hs0.le]
  exact hf.injective_on_front hs hs1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.front_IsArcBetween then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.front_IsArcBetween"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.front_IsArcBetween ``Submission.Schoenflies.IsLoop.front_IsArcBetween

/-- The back piece is an arc from the second cut point to the finish. -/
theorem back_IsArcBetween (hf : IsLoop f) (ht : t ∈ I) (ht1 : t ≠ 1) (ht0 : 0 < t) :
    IsArcBetween (f '' _root_.Set.Icc t 1) (f t) (f 1) := by
  rw [← _root_.Set.uIcc_of_le ht.2]
  refine isArcBetween_subarc hf.continuousOn ?_ ht one_mem_I ht1
  rw [_root_.Set.uIcc_of_le ht.2]
  exact hf.injective_on_back ht ht0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.back_IsArcBetween then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.back_IsArcBetween"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.back_IsArcBetween ``Submission.Schoenflies.IsLoop.back_IsArcBetween

/-! ### The outside piece

The parameters outside `[s, t]` are two intervals, glued at the point where the loop closes
up: walk from `t` to the finish, then from the start to `s`. When `s` *is* the start the front
interval degenerates to a single parameter, and the outside is the back piece alone — its far
end already carries the point the front piece would have contributed. -/

/-- The back and front pieces meet only where the loop closes up. A point on both comes from a
parameter at or past `t` and from one at or before `s`; two distinct parameters short of the
finish cannot carry the same point, and `t ≤ s` is false, so the back parameter is the
finish. -/
theorem back_meet_front (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1) (hst : s < t)
    {z : Plane} (hzb : z ∈ f '' _root_.Set.Icc t 1) (hzf : z ∈ f '' _root_.Set.Icc 0 s) : z = f 1 := by
  obtain ⟨b, hb, rfl⟩ := hzb
  obtain ⟨a, ha, hab⟩ := hzf
  have ha1 : a ≠ 1 := ne_of_lt (lt_of_le_of_lt ha.2 (hs.2.lt_of_ne hs1))
  rcases eq_or_ne b 1 with rfl | hb1
  · rfl
  · -- Otherwise both parameters are short of the finish, so they coincide — impossible,
    -- since one is at least `t` and the other at most `s < t`.
    have : b = a :=
      hf.injective_before_finish (back_subset_I ht hb) (front_subset_I hs ha) hb1 ha1 hab.symm
    exact absurd (this ▸ hb.1) (not_le.mpr (lt_of_le_of_lt ha.2 hst))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.back_meet_front then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.back_meet_front"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.back_meet_front ``Submission.Schoenflies.IsLoop.back_meet_front

/-- **The outside piece is an arc between the two cut points.** -/
theorem outside_IsArcBetween (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) (hst : s < t) :
    IsArcBetween (f '' _root_.Set.Icc 0 s ∪ f '' _root_.Set.Icc t 1) (f t) (f s) := by
  have ht0 : 0 < t := lt_of_le_of_lt hs.1 hst
  have hback : IsArcBetween (f '' _root_.Set.Icc t 1) (f t) (f 1) := hf.back_IsArcBetween ht ht1 ht0
  rcases eq_or_lt_of_le hs.1 with hs0 | hs0
  · -- `s` is the start: the front interval is the single parameter `0`, whose point the back
    -- piece already carries at its far end, so the outside is the back piece alone.
    have hfront : f '' _root_.Set.Icc 0 s = {f 1} := by
      rw [← hs0, _root_.Set.Icc_self, _root_.Set.image_singleton, hf.finish_eq_start]
    have hone : f 1 ∈ f '' _root_.Set.Icc t 1 := ⟨1, ⟨ht.2, le_rfl⟩, rfl⟩
    rw [hfront, _root_.Set.singleton_union, insert_eq_self.mpr hone, ← hs0, ← hf.finish_eq_start]
    exact hback
  · -- Otherwise the two end intervals are genuine arcs, glued where the loop closes up.
    have hfront : IsArcBetween (f '' _root_.Set.Icc 0 s) (f 1) (f s) := by
      rw [hf.finish_eq_start]
      exact hf.front_IsArcBetween hs hs1 hs0
    have := hback.concatenate hfront (fun z hzb hzf => hf.back_meet_front hs ht hs1 hst hzb hzf)
    rwa [_root_.Set.union_comm] at this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.outside_IsArcBetween then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.outside_IsArcBetween"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.outside_IsArcBetween ``Submission.Schoenflies.IsLoop.outside_IsArcBetween

/-! ### Covering, and where the pieces meet -/

/-- The parameter interval splits three ways around any two of its points. Linearity of the
order, and nothing else — the split does not even need the two points ordered, since when they
are not the middle interval is empty and the two end intervals already overlap. -/
theorem parameters_split (hs : s ∈ I) (ht : t ∈ I) :
    I = _root_.Set.Icc s t ∪ (_root_.Set.Icc 0 s ∪ _root_.Set.Icc t 1) := by
  ext x
  constructor
  · rintro ⟨h0, h1⟩
    rcases le_total x s with h | h
    · exact Or.inr (Or.inl ⟨h0, h⟩)
    · rcases le_total x t with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr (Or.inr ⟨h', h1⟩)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨hs.1.trans h1, h2.trans ht.2⟩
    · exact ⟨h1, h2.trans hs.2⟩
    · exact ⟨ht.1.trans h1, h2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.parameters_split then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.parameters_split"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.parameters_split ``Submission.Schoenflies.IsLoop.parameters_split

/-- The loop's images of the middle and of the outside cover the curve. -/
theorem pieces_cover (hs : s ∈ I) (ht : t ∈ I) :
    f '' _root_.Set.Icc s t ∪ (f '' _root_.Set.Icc 0 s ∪ f '' _root_.Set.Icc t 1) = f '' I := by
  rw [parameters_split hs ht, _root_.Set.image_union, _root_.Set.image_union]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.pieces_cover then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.pieces_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.pieces_cover ``Submission.Schoenflies.IsLoop.pieces_cover

/-- **The two pieces meet in exactly the two cut points.**

Three cases, one for each way an outside parameter can be placed. The one that matters is the
outside parameter being the finish: it carries the same point as the start, so the middle
parameter is the start, which forces `s` to be it. That case is why the argument needs a loop
rather than an arc. -/
theorem pieces_meet_at_ends (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) (hst : s < t) :
    f '' _root_.Set.Icc s t ∩ (f '' _root_.Set.Icc 0 s ∪ f '' _root_.Set.Icc t 1) = {f s, f t} := by
  have ht' : t < 1 := ht.2.lt_of_ne ht1
  apply Subset.antisymm
  · rintro z ⟨⟨m, hm, rfl⟩, hzout⟩
    have hmI : m ∈ I := middle_subset_I hs ht hm
    have hm1 : m ≠ 1 := ne_of_lt (lt_of_le_of_lt hm.2 ht')
    rcases hzout with ⟨a, ha, hazm⟩ | ⟨b, hb, hbzm⟩
    · -- A front parameter: it is at most `s`, and the middle parameter is at least `s`.
      have ha1 : a ≠ 1 := ne_of_lt (lt_of_le_of_lt ha.2 (hs.2.lt_of_ne hs1))
      have : m = a :=
        hf.injective_before_finish hmI (front_subset_I hs ha) hm1 ha1 hazm.symm
      rw [le_antisymm (this ▸ ha.2) hm.1]
      exact _root_.Set.mem_insert _ _
    · rcases eq_or_ne b 1 with rfl | hb1
      · -- The far end carries the same point as the start, and the start is short of the
        -- finish, so the middle parameter is the start — which forces `s` to be it.
        have : m = 0 :=
          hf.injective_before_finish hmI zero_mem_I hm1 one_ne_zero.symm
            (hbzm.symm.trans hf.finish_eq_start)
        have hs0 : s = 0 := le_antisymm (this ▸ hm.1) hs.1
        rw [hs0, ← this]
        exact _root_.Set.mem_insert _ _
      · -- Otherwise the outside parameter is at least `t`, and the middle one is at most `t`.
        have : m = b :=
          hf.injective_before_finish hmI (back_subset_I ht hb) hm1 hb1 hbzm.symm
        rw [le_antisymm hm.2 (this ▸ hb.1)]
        exact _root_.Set.mem_insert_of_mem _ rfl
  · rintro z (rfl | rfl)
    · exact ⟨⟨s, ⟨le_rfl, hst.le⟩, rfl⟩, Or.inl ⟨s, ⟨hs.1, le_rfl⟩, rfl⟩⟩
    · exact ⟨⟨t, ⟨hst.le, le_rfl⟩, rfl⟩, Or.inr ⟨t, ⟨le_rfl, ht.2⟩, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.pieces_meet_at_ends then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.pieces_meet_at_ends"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.pieces_meet_at_ends ``Submission.Schoenflies.IsLoop.pieces_meet_at_ends

/-! ### The two arcs, at chosen parameters -/

/-- **Two parameters short of the finish cut the loop's image into two arcs between the points
they carry, which cover it and meet in exactly those two points.**

The pieces are named by the parameters, not chosen: the first is the middle interval's image,
the second the outside's. -/
theorem two_arcs_at_parameters (hf : IsLoop f) (hs : s ∈ I) (ht : t ∈ I) (hs1 : s ≠ 1)
    (ht1 : t ≠ 1) (hst : s < t) :
    ∃ A B, IsArcBetween A (f s) (f t) ∧ IsArcBetween B (f t) (f s) ∧
      A ∪ B = f '' I ∧ A ∩ B = {f s, f t} :=
  ⟨f '' _root_.Set.Icc s t, f '' _root_.Set.Icc 0 s ∪ f '' _root_.Set.Icc t 1,
    hf.middle_IsArcBetween hs ht ht1 hst,
    hf.outside_IsArcBetween hs ht hs1 ht1 hst,
    pieces_cover hs ht,
    hf.pieces_meet_at_ends hs ht hs1 ht1 hst⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.two_arcs_at_parameters then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.two_arcs_at_parameters"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.two_arcs_at_parameters ``Submission.Schoenflies.IsLoop.two_arcs_at_parameters

end IsLoop

/-! ### The theorem -/

/-- **Two distinct points of a Jordan curve cut it into two arcs between them, which cover the
curve and meet in exactly those two points.**

The parameters carrying the two points come in one order or the other, and the conclusion is
symmetric in the two pieces, so the second case is the first with the roles exchanged: the
union and the intersection commute, and the unordered pair does too.

This is the exact converse of `IsJordanCurve.of_two_arcs`: that theorem's hypotheses are two
arcs between the same two points meeting only there, which is what the two pieces produced
here are — see `IsJordanCurve.two_arcs_of_two_arcs`. -/
theorem IsJordanCurve.two_arcs {C : Set Plane} (hC : IsJordanCurve C) {p q : Plane}
    (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q) :
    ∃ A B, IsArcBetween A p q ∧ IsArcBetween B p q ∧ A ∪ B = C ∧ A ∩ B = {p, q} := by
  obtain ⟨f, hf, rfl⟩ := hC
  obtain ⟨s, hs, hs1, rfl⟩ := hf.parameter_before_finish hp
  obtain ⟨t, ht, ht1, rfl⟩ := hf.parameter_before_finish hq
  -- Distinct points, so distinct parameters, so one of the two orders holds.
  rcases lt_or_gt_of_ne (fun h : s = t => hpq (by rw [h])) with hst | hts
  · obtain ⟨A, B, hA, hB, hcov, hmeet⟩ := hf.two_arcs_at_parameters hs ht hs1 ht1 hst
    exact ⟨A, B, hA, hB.reverse, hcov, hmeet⟩
  · -- The middle piece now runs from `f t` to `f s`, so it is the *second* piece here.
    obtain ⟨A, B, hA, hB, hcov, hmeet⟩ := hf.two_arcs_at_parameters ht hs ht1 hs1 hts
    refine ⟨B, A, hB, hA.reverse, ?_, ?_⟩
    · rw [_root_.Set.union_comm]; exact hcov
    · rw [_root_.Set.inter_comm, hmeet, _root_.Set.pair_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsJordanCurve.two_arcs then
    throwError "Refusing to shadow existing declaration Schoenflies.IsJordanCurve.two_arcs"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsJordanCurve.two_arcs ``Submission.Schoenflies.IsJordanCurve.two_arcs

/-- The composition check: the two arcs `IsJordanCurve.two_arcs` produces are exactly what
`IsJordanCurve.of_two_arcs` consumes, and glue back to the curve one started from. -/
theorem IsJordanCurve.two_arcs_of_two_arcs {A B : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q) (hmeet : A ∩ B = {p, q}) :
    IsJordanCurve (A ∪ B) :=
  IsJordanCurve.of_two_arcs hA hB.reverse fun z hzA hzB => by
    have : z ∈ ({p, q} : Set Plane) := hmeet ▸ ⟨hzA, hzB⟩
    exact this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsJordanCurve.two_arcs_of_two_arcs then
    throwError "Refusing to shadow existing declaration Schoenflies.IsJordanCurve.two_arcs_of_two_arcs"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsJordanCurve.two_arcs_of_two_arcs ``Submission.Schoenflies.IsJordanCurve.two_arcs_of_two_arcs

end Schoenflies
