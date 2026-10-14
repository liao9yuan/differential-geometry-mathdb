/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
/-
Modified for this project; see MODIFICATIONS.md for the local changes.
-/
import Submission.DifferentialGeometry.External.Schoenflies.CellulationInvariants
import Submission.DifferentialGeometry.External.Schoenflies.Subarc

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Realizing an edge subdivision

`Schoenflies/GeneratedStructure.lean` performs the *abstract* edge subdivision
(`CellStructure.subdivideEdge`) and states what it means for a realization of the subdivided
structure to refine a realization of the old one (`SubdivData.IsRefinement`);
`Schoenflies/CellulationInvariants.lean` propagates assertions (i), (iv) and (vii) across such a
refinement. Nothing built such a realization. This module does.

The construction is the blueprint's own sentence — "the corresponding point is inserted into the
corresponding edge using the edge parametrization" — made into data: pick a parameter
`t ∈ (0,1)`, put the new 0-cell at `R.drawing d.edge t`, and draw the two new 1-cells with the
two halves of the old parametrization, each rescaled to `[0,1]`.

## The orientation of the drawn edge

`IsDrawing.edge_param` is deliberately orientation-free: it says
`G.IsLink e (drawing e 0) (drawing e 1)`, so `drawing d.edge 0` may be *either* `pos d.left` or
`pos d.right`. But `d.newEdge₁` runs from `d.left` to `d.newVertex` by definition of
`subdivideEdge`, so which half of the parametrization draws it is not fixed in advance.

Assuming `drawing d.edge 0 = pos d.left` would be a false hypothesis for half of all inputs, and
the caller cannot repair it (swapping `d.left` with `d.right` in the `SubdivData` also swaps the
two new edge *names*, producing a different abstract structure). So the orientation is read off
instead: `SubdivData.leftParam` is the endpoint parameter, `0` or `1`, at which the drawn edge
sits at `d.left`. Every statement below is orientation-free; only the two lemmas
`SubdivData.drawing_leftParam` and `SubdivData.drawing_rightParam` look inside.

Because of that, the construction is phrased with `Schoenflies.subarc` — the general affine
reparametrization already on `main` — rather than with `firstHalf` / `secondHalf`, which are the
two halves in the standard orientation and are recorded here as the named special case.

## No side conditions

`SubdivData.realize` takes no geometric hypothesis beyond `t ∈ Ioo 0 1`. Everything else it
needs — that `d.edge` is drawn, injectively and continuously, between the positions of `d.left`
and `d.right`, and that an interior point of a drawn edge is not a vertex — is already carried by
`CellStructure.Realization`, and is extracted here rather than assumed.

## The transported skeleton homeomorphism is not here, but it exists

**Closed, in `Schoenflies/RealizeSubdivHomeo.lean`** (`SubdivData.realizeHomeo`), on top of
`Schoenflies/ArcMonotone.lean`, which supplies the missing fact named at the end of this
section. What follows is the record of why it could not be done here.

`SkeletonHomeo.realize` is absent from *this* module. Six of its eight fields are immediate —
`skeletonSet_realize` below says the realized 1-skeleton is *literally the same set* after a
subdivision, so the map, its inverse, both continuity clauses and both inverse clauses transport
verbatim, and
`pos_apply` at the new 0-cell is the statement `g.toFun (R₁.drawing d.edge t₁) =
R₂.drawing d.edge t₂` that a caller choosing corresponding parameters supplies anyway.

What is missing is `edgeArc_image` at the two new edges: that `g` carries the *half* arc from
`R₁.pos d.left` to the new source point onto the half arc from `R₂.pos d.left` to the new target
point. This is true but is not implied by the `SkeletonHomeo` data pointwise: it needs the fact
that a homeomorphism between two arcs matching their endpoints is monotone, hence carries
initial subarcs to initial subarcs. That fact was not on `main` when this module was written,
and assuming the two clauses would have been assuming the conclusion, so nothing was stated
here. `Schoenflies/ArcMonotone.lean`
now proves it — `ArcMatch`, `transferParam`, `image_image_uIcc` — and
`Schoenflies/RealizeSubdivHomeo.lean` builds the transported homeomorphism from it, orientation
of the two realizations handled rather than assumed.

## Blueprint

* `def:generated-structure`, operation 1 (edge subdivision) — the geometric half of the
  operation, whose abstract half is `CellStructure.subdivideEdge`.
* `lem:cellulation-invariants` (i) and (iv), the paragraph "Suppose first that an open edge `e`
  is subdivided at a new vertex `v`": `SubdivData.isRefinement_realize` produces exactly the
  hypotheses that `SubdivData.IsRefinement.isCellDecomposition_and_isFaceJordan` consumes.

Declarations:

* `Schoenflies.uIcc_union_uIcc`, `Schoenflies.uIcc_inter_uIcc` — a parameter interval cut at an
  interior point.
* `Schoenflies.subarc_image_union`, `Schoenflies.subarc_image_inter` — the two subarcs of a cut
  cover the arc and meet exactly at the cut point.
* `Schoenflies.firstHalf`, `Schoenflies.secondHalf` — the two halves of a drawn edge in the
  standard orientation, with their endpoint values, continuity, injectivity, images, meet and
  union.
* `Schoenflies.CellStructure.SubdivData.leftParam` / `rightParam` — the orientation of the drawn
  edge.
* `Schoenflies.CellStructure.SubdivData.realize` — the realization of the subdivided structure.
* `Schoenflies.CellStructure.SubdivData.isRefinement_realize` — it refines the given one.
* `Schoenflies.CellStructure.SubdivData.realize_isCellDecomposition_and_isFaceJordan` — the
  induction step of `lem:cellulation-invariants` over the first constructor, now constructed
  with all necessary data constructed here.
* `Schoenflies.CellStructure.SubdivData.skeletonSet_realize` — a subdivision does not move the
  realized 1-skeleton.
-/

open _root_.Set _root_.unitInterval
open scoped _root_.Graph _root_.Submission.Graph

namespace Schoenflies

open _root_.Graph _root_.Submission.Graph

/-! ### Cutting a parameter interval at an interior point -/

variable {a b t : ℝ}

/-- The two halves of a parameter interval cut at a point of it cover it. -/
theorem uIcc_union_uIcc (h : t ∈ _root_.Set.uIcc a b) : _root_.Set.uIcc a t ∪ _root_.Set.uIcc t b = _root_.Set.uIcc a b := by
  rcases le_total a b with hab | hab
  · rw [_root_.Set.uIcc_of_le hab] at h ⊢
    rw [_root_.Set.uIcc_of_le h.1, _root_.Set.uIcc_of_le h.2, _root_.Set.Icc_union_Icc_eq_Icc h.1 h.2]
  · rw [_root_.Set.uIcc_of_ge hab] at h ⊢
    rw [_root_.Set.uIcc_of_ge h.2, _root_.Set.uIcc_of_ge h.1, _root_.Set.union_comm, _root_.Set.Icc_union_Icc_eq_Icc h.1 h.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.uIcc_union_uIcc then
    throwError "Refusing to shadow existing declaration Schoenflies.uIcc_union_uIcc"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.uIcc_union_uIcc ``Submission.Schoenflies.uIcc_union_uIcc

/-- …and meet exactly at the cut point. -/
theorem uIcc_inter_uIcc (h : t ∈ _root_.Set.uIcc a b) : _root_.Set.uIcc a t ∩ _root_.Set.uIcc t b = {t} := by
  rcases le_total a b with hab | hab
  · rw [_root_.Set.uIcc_of_le hab] at h
    rw [_root_.Set.uIcc_of_le h.1, _root_.Set.uIcc_of_le h.2, _root_.Set.Icc_inter_Icc_eq_singleton h.1 h.2]
  · rw [_root_.Set.uIcc_of_ge hab] at h
    rw [_root_.Set.uIcc_of_ge h.2, _root_.Set.uIcc_of_ge h.1, _root_.Set.inter_comm, _root_.Set.Icc_inter_Icc_eq_singleton h.1 h.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.uIcc_inter_uIcc then
    throwError "Refusing to shadow existing declaration Schoenflies.uIcc_inter_uIcc"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.uIcc_inter_uIcc ``Submission.Schoenflies.uIcc_inter_uIcc

/-- The far endpoint is not in the near half. -/
theorem right_notMem_uIcc_left (h : t ∈ _root_.Set.uIcc a b) (hb : b ≠ t) : b ∉ _root_.Set.uIcc a t := fun hmem =>
  hb (by
    have : b ∈ _root_.Set.uIcc a t ∩ _root_.Set.uIcc t b := ⟨hmem, right_mem_uIcc⟩
    rwa [uIcc_inter_uIcc h, _root_.Set.mem_singleton_iff] at this)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.right_notMem_uIcc_left then
    throwError "Refusing to shadow existing declaration Schoenflies.right_notMem_uIcc_left"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.right_notMem_uIcc_left ``Submission.Schoenflies.right_notMem_uIcc_left

/-- …and symmetrically. -/
theorem left_notMem_uIcc_right (h : t ∈ _root_.Set.uIcc a b) (ha : a ≠ t) : a ∉ _root_.Set.uIcc t b := fun hmem =>
  ha (by
    have : a ∈ _root_.Set.uIcc a t ∩ _root_.Set.uIcc t b := ⟨left_mem_uIcc, hmem⟩
    rwa [uIcc_inter_uIcc h, _root_.Set.mem_singleton_iff] at this)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.left_notMem_uIcc_right then
    throwError "Refusing to shadow existing declaration Schoenflies.left_notMem_uIcc_right"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.left_notMem_uIcc_right ``Submission.Schoenflies.left_notMem_uIcc_right

theorem uIcc_left_subset (h : t ∈ _root_.Set.uIcc a b) : _root_.Set.uIcc a t ⊆ _root_.Set.uIcc a b :=
  _root_.Set.uIcc_subset_uIcc _root_.Set.left_mem_uIcc h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.uIcc_left_subset then
    throwError "Refusing to shadow existing declaration Schoenflies.uIcc_left_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.uIcc_left_subset ``Submission.Schoenflies.uIcc_left_subset

theorem uIcc_right_subset (h : t ∈ _root_.Set.uIcc a b) : _root_.Set.uIcc t b ⊆ _root_.Set.uIcc a b :=
  _root_.Set.uIcc_subset_uIcc h _root_.Set.right_mem_uIcc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.uIcc_right_subset then
    throwError "Refusing to shadow existing declaration Schoenflies.uIcc_right_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.uIcc_right_subset ``Submission.Schoenflies.uIcc_right_subset

/-! ### The two subarcs of a cut -/

variable {f : ℝ → Plane}

/-- **The two subarcs of a cut cover the arc.** -/
theorem subarc_image_union (h : t ∈ _root_.Set.uIcc a b) :
    subarc f a t '' I ∪ subarc f t b '' I = f '' _root_.Set.uIcc a b := by
  rw [subarc_image, subarc_image, ← _root_.Set.image_union, uIcc_union_uIcc h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.subarc_image_union then
    throwError "Refusing to shadow existing declaration Schoenflies.subarc_image_union"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.subarc_image_union ``Submission.Schoenflies.subarc_image_union

/-- **The two subarcs of a cut meet exactly at the cut point.** -/
theorem subarc_image_inter (hi : _root_.Set.InjOn f (_root_.Set.uIcc a b)) (h : t ∈ _root_.Set.uIcc a b) :
    subarc f a t '' I ∩ subarc f t b '' I = {f t} := by
  rw [subarc_image, subarc_image, ← hi.image_inter (uIcc_left_subset h) (uIcc_right_subset h),
    uIcc_inter_uIcc h, _root_.Set.image_singleton]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.subarc_image_inter then
    throwError "Refusing to shadow existing declaration Schoenflies.subarc_image_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.subarc_image_inter ``Submission.Schoenflies.subarc_image_inter

/-- **The closure of an open arc is the closed arc.** General; `Schoenflies/Subarc.lean` has the
two endpoint halves (`IsArcBetween.left_mem_closure_diff` and `…right_mem_closure_diff`) but not
this consequence, and every "closure of a new open edge" computation is this lemma. It belongs
next to those two if a second consumer appears. -/
theorem IsArcBetween.closure_diff_eq {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    closure (A \ {p, q}) = A := by
  refine subset_antisymm (h.isArc.isClosed.closure_subset_iff.2 _root_.Set.sdiff_subset) fun z hz => ?_
  by_cases hzp : z = p
  · exact hzp ▸ h.left_mem_closure_diff
  · by_cases hzq : z = q
    · exact hzq ▸ h.right_mem_closure_diff
    · exact subset_closure ⟨hz, by simp [hzp, hzq]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsArcBetween.closure_diff_eq then
    throwError "Refusing to shadow existing declaration Schoenflies.IsArcBetween.closure_diff_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsArcBetween.closure_diff_eq ``Submission.Schoenflies.IsArcBetween.closure_diff_eq

/-- The three pieces an open arc is cut into put the arc back together. -/
theorem diff_pair_union_union {A : Set Plane} {p q : Plane} (hp : p ∈ A) (hq : q ∈ A) :
    A \ {p, q} ∪ {q} ∪ {p} = A := by
  ext z
  simp only [_root_.Set.mem_union, _root_.Set.mem_sdiff, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, not_or]
  constructor
  · rintro ((⟨h, -, -⟩ | rfl) | rfl)
    exacts [h, hq, hp]
  · intro h
    by_cases h₁ : z = p
    · exact Or.inr h₁
    · by_cases h₂ : z = q
      · exact Or.inl (Or.inr h₂)
      · exact Or.inl (Or.inl ⟨h, h₁, h₂⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.diff_pair_union_union then
    throwError "Refusing to shadow existing declaration Schoenflies.diff_pair_union_union"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.diff_pair_union_union ``Submission.Schoenflies.diff_pair_union_union

/-! ### The two halves of a drawn edge

The special case `a = 0`, `b = 1` of the previous section, in the notation a consumer holding a
`Graph.IsDrawing` writes. -/

variable {β : Type*} {drawing : β → ℝ → Plane} {e : β}

theorem uIcc_zero_one : _root_.Set.uIcc (0 : ℝ) 1 = I := _root_.Set.uIcc_of_le zero_le_one

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.uIcc_zero_one then
    throwError "Refusing to shadow existing declaration Schoenflies.uIcc_zero_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.uIcc_zero_one ``Submission.Schoenflies.uIcc_zero_one

/-- The first half of a drawn edge, rescaled to `[0, 1]`. -/
def firstHalf (drawing : β → ℝ → Plane) (e : β) (t : ℝ) : ℝ → Plane := subarc (drawing e) 0 t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.firstHalf then
    throwError "Refusing to shadow existing declaration Schoenflies.firstHalf"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.firstHalf ``Submission.Schoenflies.firstHalf

/-- The second half of a drawn edge, rescaled to `[0, 1]`. -/
def secondHalf (drawing : β → ℝ → Plane) (e : β) (t : ℝ) : ℝ → Plane := subarc (drawing e) t 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.secondHalf then
    throwError "Refusing to shadow existing declaration Schoenflies.secondHalf"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.secondHalf ``Submission.Schoenflies.secondHalf

theorem firstHalf_apply (s : ℝ) : firstHalf drawing e t s = drawing e (t * s) := by
  simp only [firstHalf, subarc, reparam]
  congr 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.firstHalf_apply then
    throwError "Refusing to shadow existing declaration Schoenflies.firstHalf_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.firstHalf_apply ``Submission.Schoenflies.firstHalf_apply

theorem secondHalf_apply (s : ℝ) : secondHalf drawing e t s = drawing e (t + (1 - t) * s) := by
  simp only [secondHalf, subarc, reparam]
  congr 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.secondHalf_apply then
    throwError "Refusing to shadow existing declaration Schoenflies.secondHalf_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.secondHalf_apply ``Submission.Schoenflies.secondHalf_apply

@[simp] theorem firstHalf_zero : firstHalf drawing e t 0 = drawing e 0 := subarc_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.firstHalf_zero then
    throwError "Refusing to shadow existing declaration Schoenflies.firstHalf_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.firstHalf_zero ``Submission.Schoenflies.firstHalf_zero

@[simp] theorem firstHalf_one : firstHalf drawing e t 1 = drawing e t := subarc_one

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.firstHalf_one then
    throwError "Refusing to shadow existing declaration Schoenflies.firstHalf_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.firstHalf_one ``Submission.Schoenflies.firstHalf_one

@[simp] theorem secondHalf_zero : secondHalf drawing e t 0 = drawing e t := subarc_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.secondHalf_zero then
    throwError "Refusing to shadow existing declaration Schoenflies.secondHalf_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.secondHalf_zero ``Submission.Schoenflies.secondHalf_zero

@[simp] theorem secondHalf_one : secondHalf drawing e t 1 = drawing e 1 := subarc_one

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.secondHalf_one then
    throwError "Refusing to shadow existing declaration Schoenflies.secondHalf_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.secondHalf_one ``Submission.Schoenflies.secondHalf_one

theorem continuousOn_firstHalf (hc : ContinuousOn (drawing e) I) (ht : t ∈ I) :
    ContinuousOn (firstHalf drawing e t) I := continuousOn_subarc hc zero_mem_I ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.continuousOn_firstHalf then
    throwError "Refusing to shadow existing declaration Schoenflies.continuousOn_firstHalf"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.continuousOn_firstHalf ``Submission.Schoenflies.continuousOn_firstHalf

theorem continuousOn_secondHalf (hc : ContinuousOn (drawing e) I) (ht : t ∈ I) :
    ContinuousOn (secondHalf drawing e t) I := continuousOn_subarc hc ht one_mem_I

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.continuousOn_secondHalf then
    throwError "Refusing to shadow existing declaration Schoenflies.continuousOn_secondHalf"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.continuousOn_secondHalf ``Submission.Schoenflies.continuousOn_secondHalf

theorem injOn_firstHalf (hi : _root_.Set.InjOn (drawing e) I) (ht : t ∈ I) (h0 : t ≠ 0) :
    InjOn (firstHalf drawing e t) I :=
  injOn_subarc (hi.mono (uIcc_subset_I zero_mem_I ht)) (Ne.symm h0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.injOn_firstHalf then
    throwError "Refusing to shadow existing declaration Schoenflies.injOn_firstHalf"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.injOn_firstHalf ``Submission.Schoenflies.injOn_firstHalf

theorem injOn_secondHalf (hi : _root_.Set.InjOn (drawing e) I) (ht : t ∈ I) (h1 : t ≠ 1) :
    InjOn (secondHalf drawing e t) I :=
  injOn_subarc (hi.mono (uIcc_subset_I ht one_mem_I)) h1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.injOn_secondHalf then
    throwError "Refusing to shadow existing declaration Schoenflies.injOn_secondHalf"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.injOn_secondHalf ``Submission.Schoenflies.injOn_secondHalf

theorem image_firstHalf (ht : t ∈ I) :
    firstHalf drawing e t '' I = drawing e '' _root_.Set.Icc 0 t := by
  rw [firstHalf, subarc_image, _root_.Set.uIcc_of_le ht.1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.image_firstHalf then
    throwError "Refusing to shadow existing declaration Schoenflies.image_firstHalf"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.image_firstHalf ``Submission.Schoenflies.image_firstHalf

theorem image_secondHalf (ht : t ∈ I) :
    secondHalf drawing e t '' I = drawing e '' _root_.Set.Icc t 1 := by
  rw [secondHalf, subarc_image, _root_.Set.uIcc_of_le ht.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.image_secondHalf then
    throwError "Refusing to shadow existing declaration Schoenflies.image_secondHalf"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.image_secondHalf ``Submission.Schoenflies.image_secondHalf

/-- **The two halves cover the drawn edge.** -/
theorem firstHalf_union_secondHalf (ht : t ∈ I) :
    firstHalf drawing e t '' I ∪ secondHalf drawing e t '' I = edgeArc drawing e := by
  rw [firstHalf, secondHalf, subarc_image_union (by rwa [uIcc_zero_one]), uIcc_zero_one, edgeArc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.firstHalf_union_secondHalf then
    throwError "Refusing to shadow existing declaration Schoenflies.firstHalf_union_secondHalf"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.firstHalf_union_secondHalf ``Submission.Schoenflies.firstHalf_union_secondHalf

/-- **The two halves meet exactly at the cut point.** -/
theorem firstHalf_inter_secondHalf (hi : _root_.Set.InjOn (drawing e) I) (ht : t ∈ I) :
    firstHalf drawing e t '' I ∩ secondHalf drawing e t '' I = {drawing e t} := by
  rw [firstHalf, secondHalf,
    subarc_image_inter (by rwa [uIcc_zero_one]) (by rwa [uIcc_zero_one])]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.firstHalf_inter_secondHalf then
    throwError "Refusing to shadow existing declaration Schoenflies.firstHalf_inter_secondHalf"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.firstHalf_inter_secondHalf ``Submission.Schoenflies.firstHalf_inter_secondHalf

/-- Each half is an arc between the corresponding endpoint and the cut point. -/
theorem isArcBetween_firstHalf (hc : ContinuousOn (drawing e) I) (hi : _root_.Set.InjOn (drawing e) I)
    (ht : t ∈ I) (h0 : t ≠ 0) :
    IsArcBetween (firstHalf drawing e t '' I) (drawing e 0) (drawing e t) :=
  ⟨firstHalf drawing e t, continuousOn_firstHalf hc ht, injOn_firstHalf hi ht h0, rfl,
    firstHalf_zero, firstHalf_one⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.isArcBetween_firstHalf then
    throwError "Refusing to shadow existing declaration Schoenflies.isArcBetween_firstHalf"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.isArcBetween_firstHalf ``Submission.Schoenflies.isArcBetween_firstHalf

theorem isArcBetween_secondHalf (hc : ContinuousOn (drawing e) I) (hi : _root_.Set.InjOn (drawing e) I)
    (ht : t ∈ I) (h1 : t ≠ 1) :
    IsArcBetween (secondHalf drawing e t '' I) (drawing e t) (drawing e 1) :=
  ⟨secondHalf drawing e t, continuousOn_secondHalf hc ht, injOn_secondHalf hi ht h1, rfl,
    secondHalf_zero, secondHalf_one⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.isArcBetween_secondHalf then
    throwError "Refusing to shadow existing declaration Schoenflies.isArcBetween_secondHalf"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.isArcBetween_secondHalf ``Submission.Schoenflies.isArcBetween_secondHalf

/-! ### The orientation of the drawn subdivided edge -/

namespace CellStructure

namespace SubdivData

variable {γ : Type*} {S : CellStructure γ} (d : S.SubdivData) (R : S.Realization)

/-- What the realization already knows about the subdivided edge: it is an edge of the drawn
skeleton. -/
theorem edge_mem_edgeSet_graph : d.edge ∈ E(R.graph) := by
  rw [Realization.edgeSet_graph]; exact d.edge_mem_edgeSet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.edge_mem_edgeSet_graph then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.edge_mem_edgeSet_graph"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.edge_mem_edgeSet_graph ``Submission.Schoenflies.CellStructure.SubdivData.edge_mem_edgeSet_graph

theorem continuousOn_drawing_edge : ContinuousOn (R.drawing d.edge) I :=
  (R.isDrawing.edge_param (d.edge_mem_edgeSet_graph R)).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.continuousOn_drawing_edge then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.continuousOn_drawing_edge"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.continuousOn_drawing_edge ``Submission.Schoenflies.CellStructure.SubdivData.continuousOn_drawing_edge

theorem injOn_drawing_edge : _root_.Set.InjOn (R.drawing d.edge) I :=
  (R.isDrawing.edge_param (d.edge_mem_edgeSet_graph R)).2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.injOn_drawing_edge then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.injOn_drawing_edge"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.injOn_drawing_edge ``Submission.Schoenflies.CellStructure.SubdivData.injOn_drawing_edge

theorem isLink_drawn_edge : R.graph.IsLink d.edge (R.pos d.left) (R.pos d.right) :=
  d.isLink.map R.pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.isLink_drawn_edge then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.isLink_drawn_edge"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.isLink_drawn_edge ``Submission.Schoenflies.CellStructure.SubdivData.isLink_drawn_edge

open scoped _root_.Classical in
/-- **The orientation of the drawn subdivided edge**: the endpoint parameter, `0` or `1`, at
which `R.drawing d.edge` sits at `R.pos d.left`.

`IsDrawing.edge_param` fixes only the unordered pair of endpoint values, so this cannot be read
off the structure; it is decided by a case distinction, once, here. -/
noncomputable def leftParam : ℝ := if R.drawing d.edge 0 = R.pos d.left then 0 else 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.leftParam then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.leftParam"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.leftParam ``Submission.Schoenflies.CellStructure.SubdivData.leftParam

/-- The endpoint parameter at which the drawn subdivided edge sits at `R.pos d.right`. -/
noncomputable def rightParam : ℝ := 1 - d.leftParam R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.rightParam then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.rightParam"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.rightParam ``Submission.Schoenflies.CellStructure.SubdivData.rightParam

theorem leftParam_eq_zero_or_one : d.leftParam R = 0 ∨ d.leftParam R = 1 := by
  unfold leftParam
  split_ifs
  exacts [Or.inl rfl, Or.inr rfl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.leftParam_eq_zero_or_one then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.leftParam_eq_zero_or_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.leftParam_eq_zero_or_one ``Submission.Schoenflies.CellStructure.SubdivData.leftParam_eq_zero_or_one

/-- **The two endpoint parameters land on the two endpoints.** The only lemma that looks inside
`leftParam`; everything downstream is orientation-free. -/
theorem drawing_params :
    R.drawing d.edge (d.leftParam R) = R.pos d.left ∧
      R.drawing d.edge (d.rightParam R) = R.pos d.right := by
  have hd := R.isDrawing.edge_param (d.edge_mem_edgeSet_graph R)
  rcases (d.isLink_drawn_edge R).eq_and_eq_or_eq_and_eq hd.2.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hL : d.leftParam R = 0 := if_pos h0.symm
    refine ⟨by rw [hL]; exact h0.symm, ?_⟩
    have hR : d.rightParam R = 1 := by rw [rightParam, hL]; ring
    rw [hR]; exact h1.symm
  · -- Here `R.pos d.left = R.drawing d.edge 1`; the other reading would collapse the two
    -- endpoint values, which injectivity forbids.
    have hne : ¬ (R.drawing d.edge 0 = R.pos d.left) := fun hcon =>
      zero_ne_one (hd.2.1 zero_mem_I one_mem_I (by rw [hcon, h0]))
    have hL : d.leftParam R = 1 := if_neg hne
    refine ⟨by rw [hL]; exact h0.symm, ?_⟩
    have hR : d.rightParam R = 0 := by rw [rightParam, hL]; ring
    rw [hR]; exact h1.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.drawing_params then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.drawing_params"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.drawing_params ``Submission.Schoenflies.CellStructure.SubdivData.drawing_params

theorem drawing_leftParam : R.drawing d.edge (d.leftParam R) = R.pos d.left :=
  (d.drawing_params R).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.drawing_leftParam then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.drawing_leftParam"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.drawing_leftParam ``Submission.Schoenflies.CellStructure.SubdivData.drawing_leftParam

theorem drawing_rightParam : R.drawing d.edge (d.rightParam R) = R.pos d.right :=
  (d.drawing_params R).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.drawing_rightParam then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.drawing_rightParam"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.drawing_rightParam ``Submission.Schoenflies.CellStructure.SubdivData.drawing_rightParam

theorem leftParam_mem_I : d.leftParam R ∈ I := by
  rcases d.leftParam_eq_zero_or_one R with h | h <;> rw [h]
  exacts [zero_mem_I, one_mem_I]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.leftParam_mem_I then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.leftParam_mem_I"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.leftParam_mem_I ``Submission.Schoenflies.CellStructure.SubdivData.leftParam_mem_I

theorem rightParam_mem_I : d.rightParam R ∈ I := by
  rcases d.leftParam_eq_zero_or_one R with h | h
  · rw [rightParam, h, sub_zero]; exact one_mem_I
  · rw [rightParam, h, sub_self]; exact zero_mem_I

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.rightParam_mem_I then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.rightParam_mem_I"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.rightParam_mem_I ``Submission.Schoenflies.CellStructure.SubdivData.rightParam_mem_I

/-- The two endpoint parameters span the whole parameter interval, in whichever order. -/
theorem uIcc_params : _root_.Set.uIcc (d.leftParam R) (d.rightParam R) = I := by
  rcases d.leftParam_eq_zero_or_one R with h | h
  · rw [rightParam, h, sub_zero]; exact uIcc_zero_one
  · rw [rightParam, h, sub_self, _root_.Set.uIcc_comm]; exact uIcc_zero_one

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.uIcc_params then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.uIcc_params"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.uIcc_params ``Submission.Schoenflies.CellStructure.SubdivData.uIcc_params

theorem leftParam_ne (ht : t ∈ _root_.Set.Ioo (0 : ℝ) 1) : d.leftParam R ≠ t := by
  rcases d.leftParam_eq_zero_or_one R with h | h <;> rw [h]
  exacts [ht.1.ne, ht.2.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.leftParam_ne then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.leftParam_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.leftParam_ne ``Submission.Schoenflies.CellStructure.SubdivData.leftParam_ne

theorem rightParam_ne (ht : t ∈ _root_.Set.Ioo (0 : ℝ) 1) : d.rightParam R ≠ t := by
  rcases d.leftParam_eq_zero_or_one R with h | h
  · rw [rightParam, h, sub_zero]; exact ht.2.ne'
  · rw [rightParam, h, sub_self]; exact ht.1.ne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.rightParam_ne then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.rightParam_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.rightParam_ne ``Submission.Schoenflies.CellStructure.SubdivData.rightParam_ne

theorem mem_uIcc_params (ht : t ∈ _root_.Set.Ioo (0 : ℝ) 1) : t ∈ _root_.Set.uIcc (d.leftParam R) (d.rightParam R) := by
  rw [d.uIcc_params R]; exact _root_.Set.Ioo_subset_Icc_self ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.mem_uIcc_params then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.mem_uIcc_params"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.mem_uIcc_params ``Submission.Schoenflies.CellStructure.SubdivData.mem_uIcc_params

/-- **An interior point of a drawn edge is not a vertex.** The one geometric fact the
construction needs that is not simply read off a field, and the reason `SubdivData.realize`
needs no side condition. -/
theorem newPos_notMem_vertexSet (ht : t ∈ _root_.Set.Ioo (0 : ℝ) 1) :
    R.drawing d.edge t ∉ V(R.graph) := by
  intro hmem
  have harc : R.drawing d.edge t ∈ edgeArc R.drawing d.edge :=
    ⟨t, _root_.Set.Ioo_subset_Icc_self ht, rfl⟩
  have hinj := d.injOn_drawing_edge R
  rcases R.isDrawing.vertex_mem_edgeArc (d.isLink_drawn_edge R) hmem harc with h | h
  · exact d.leftParam_ne R ht
      (hinj (d.leftParam_mem_I R) (_root_.Set.Ioo_subset_Icc_self ht) ((d.drawing_leftParam R).trans h.symm))
  · exact d.rightParam_ne R ht
      (hinj (d.rightParam_mem_I R) (_root_.Set.Ioo_subset_Icc_self ht)
        ((d.drawing_rightParam R).trans h.symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.newPos_notMem_vertexSet then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.newPos_notMem_vertexSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.newPos_notMem_vertexSet ``Submission.Schoenflies.CellStructure.SubdivData.newPos_notMem_vertexSet

theorem newPos_ne_pos (ht : t ∈ _root_.Set.Ioo (0 : ℝ) 1) {v : γ} (hv : v ∈ V(S.skel)) :
    R.drawing d.edge t ≠ R.pos v := fun h =>
  d.newPos_notMem_vertexSet R ht (by rw [h, Realization.vertexSet_graph]; exact ⟨v, hv, rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.newPos_ne_pos then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.newPos_ne_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.newPos_ne_pos ``Submission.Schoenflies.CellStructure.SubdivData.newPos_ne_pos

/-! ### Freshness of the three new names, in the forms used below -/

theorem newVertex_notMem_vertexSet : d.newVertex ∉ V(S.skel) := fun h =>
  d.newVertex_notMem (S.mem_cells_of_mem_vertexSet h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.newVertex_notMem_vertexSet then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.newVertex_notMem_vertexSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.newVertex_notMem_vertexSet ``Submission.Schoenflies.CellStructure.SubdivData.newVertex_notMem_vertexSet

theorem ne_newVertex_of_mem_cells {z : γ} (hz : z ∈ S.cells) : z ≠ d.newVertex := fun h =>
  d.newVertex_notMem (h ▸ hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.ne_newVertex_of_mem_cells then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.ne_newVertex_of_mem_cells"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.ne_newVertex_of_mem_cells ``Submission.Schoenflies.CellStructure.SubdivData.ne_newVertex_of_mem_cells

theorem ne_newEdge₁_of_mem_cells {z : γ} (hz : z ∈ S.cells) : z ≠ d.newEdge₁ := fun h =>
  d.newEdge₁_notMem (h ▸ hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.ne_newEdge₁_of_mem_cells then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.ne_newEdge₁_of_mem_cells"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.ne_newEdge₁_of_mem_cells ``Submission.Schoenflies.CellStructure.SubdivData.ne_newEdge₁_of_mem_cells

theorem ne_newEdge₂_of_mem_cells {z : γ} (hz : z ∈ S.cells) : z ≠ d.newEdge₂ := fun h =>
  d.newEdge₂_notMem (h ▸ hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.ne_newEdge₂_of_mem_cells then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.ne_newEdge₂_of_mem_cells"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.ne_newEdge₂_of_mem_cells ``Submission.Schoenflies.CellStructure.SubdivData.ne_newEdge₂_of_mem_cells

theorem newEdge₁_ne_edge : d.newEdge₁ ≠ d.edge := fun h =>
  d.newEdge₁_notMem (h ▸ d.edge_mem_cells)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.newEdge₁_ne_edge then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.newEdge₁_ne_edge"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.newEdge₁_ne_edge ``Submission.Schoenflies.CellStructure.SubdivData.newEdge₁_ne_edge

theorem newEdge₂_ne_edge : d.newEdge₂ ≠ d.edge := fun h =>
  d.newEdge₂_notMem (h ▸ d.edge_mem_cells)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.newEdge₂_ne_edge then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.newEdge₂_ne_edge"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.newEdge₂_ne_edge ``Submission.Schoenflies.CellStructure.SubdivData.newEdge₂_ne_edge

/-! ### The links of the subdivided skeleton -/

theorem isLink_newEdge₁ : d.skeleton.IsLink d.newEdge₁ d.left d.newVertex :=
  d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.isLink_newEdge₁ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.isLink_newEdge₁"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.isLink_newEdge₁ ``Submission.Schoenflies.CellStructure.SubdivData.isLink_newEdge₁

theorem isLink_newEdge₂ : d.skeleton.IsLink d.newEdge₂ d.newVertex d.right :=
  d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, rfl⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.isLink_newEdge₂ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.isLink_newEdge₂"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.isLink_newEdge₂ ``Submission.Schoenflies.CellStructure.SubdivData.isLink_newEdge₂

/-- An old edge other than the subdivided one keeps its ends. -/
theorem skeleton_isLink_of_old {f x y : γ} (hfe : f ≠ d.edge) (h : S.skel.IsLink f x y) :
    d.skeleton.IsLink f x y :=
  d.skeleton_isLink.2 (Or.inl ⟨h, hfe,
    fun hc => d.newEdge₁_notMem_edgeSet (hc ▸ h.edge_mem),
    fun hc => d.newEdge₂_notMem_edgeSet (hc ▸ h.edge_mem)⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.skeleton_isLink_of_old then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.skeleton_isLink_of_old"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.skeleton_isLink_of_old ``Submission.Schoenflies.CellStructure.SubdivData.skeleton_isLink_of_old

/-- …and gains none: for an old edge the two skeleta have the same links. -/
theorem skeleton_isLink_old_iff {f x y : γ} (hf : f ∈ E(S.skel)) (hfe : f ≠ d.edge) :
    d.skeleton.IsLink f x y ↔ S.skel.IsLink f x y := by
  refine ⟨fun h => ?_, d.skeleton_isLink_of_old hfe⟩
  rcases d.skeleton_isLink.1 h with ⟨h, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact h
  · exact absurd hf d.newEdge₁_notMem_edgeSet
  · exact absurd hf d.newEdge₂_notMem_edgeSet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.skeleton_isLink_old_iff then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.skeleton_isLink_old_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.skeleton_isLink_old_iff ``Submission.Schoenflies.CellStructure.SubdivData.skeleton_isLink_old_iff

/-! ### The realization of the subdivided structure -/

open scoped _root_.Classical in
/-- The positions after the subdivision: the new 0-cell goes to the point of the drawn edge at
parameter `t`, and every old 0-cell stays where it was. -/
noncomputable def realizePos (d : S.SubdivData) (R : S.Realization) (t : ℝ) : γ → Plane :=
  fun z => if z = d.newVertex then R.drawing d.edge t else R.pos z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizePos then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizePos"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizePos ``Submission.Schoenflies.CellStructure.SubdivData.realizePos

open scoped _root_.Classical in
/-- The parametrizations after the subdivision: the two new 1-cells are drawn by the two halves
of the old parametrization, cut at `t` and rescaled to `[0, 1]`; every old 1-cell keeps its own.

`d.newEdge₁` runs from `d.left`, so the half that draws it starts at `d.leftParam R`, which is
`0` or `1` according to the orientation of the old parametrization. -/
noncomputable def realizeDrawing (d : S.SubdivData) (R : S.Realization) (t : ℝ) : γ → ℝ → Plane :=
  fun f =>
    if f = d.newEdge₁ then subarc (R.drawing d.edge) (d.leftParam R) t
    else if f = d.newEdge₂ then subarc (R.drawing d.edge) t (d.rightParam R)
    else R.drawing f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizeDrawing then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizeDrawing"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizeDrawing ``Submission.Schoenflies.CellStructure.SubdivData.realizeDrawing

open scoped _root_.Classical in
/-- The open cells after the subdivision: the new 0-cell is the new point, each new open 1-cell
is its half arc without its two endpoints, and every surviving cell is unchanged. -/
noncomputable def realizeCell (d : S.SubdivData) (R : S.Realization) (t : ℝ) : γ → Set Plane :=
  fun c =>
    if c = d.newVertex then {R.drawing d.edge t}
    else if c = d.newEdge₁ then
      R.drawing d.edge '' _root_.Set.uIcc (d.leftParam R) t \ {R.pos d.left, R.drawing d.edge t}
    else if c = d.newEdge₂ then
      R.drawing d.edge '' _root_.Set.uIcc t (d.rightParam R) \ {R.drawing d.edge t, R.pos d.right}
    else R.cell c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizeCell then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizeCell"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizeCell ``Submission.Schoenflies.CellStructure.SubdivData.realizeCell

/-- The drawn skeleton after the subdivision. -/
noncomputable def realizeGraph (d : S.SubdivData) (R : S.Realization) (t : ℝ) : Graph Plane γ :=
  d.skeleton.map (d.realizePos R t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizeGraph then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizeGraph"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizeGraph ``Submission.Schoenflies.CellStructure.SubdivData.realizeGraph

variable {d R}

@[simp] theorem realizePos_newVertex : d.realizePos R t d.newVertex = R.drawing d.edge t :=
  if_pos rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizePos_newVertex then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizePos_newVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizePos_newVertex ``Submission.Schoenflies.CellStructure.SubdivData.realizePos_newVertex

theorem realizePos_of_ne {z : γ} (h : z ≠ d.newVertex) : d.realizePos R t z = R.pos z := if_neg h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizePos_of_ne then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizePos_of_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizePos_of_ne ``Submission.Schoenflies.CellStructure.SubdivData.realizePos_of_ne

theorem realizePos_of_mem_cells {z : γ} (h : z ∈ S.cells) : d.realizePos R t z = R.pos z :=
  realizePos_of_ne (d.ne_newVertex_of_mem_cells h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizePos_of_mem_cells then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizePos_of_mem_cells"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizePos_of_mem_cells ``Submission.Schoenflies.CellStructure.SubdivData.realizePos_of_mem_cells

theorem realizePos_of_mem_vertexSet {z : γ} (h : z ∈ V(S.skel)) : d.realizePos R t z = R.pos z :=
  realizePos_of_mem_cells (S.mem_cells_of_mem_vertexSet h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizePos_of_mem_vertexSet then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizePos_of_mem_vertexSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizePos_of_mem_vertexSet ``Submission.Schoenflies.CellStructure.SubdivData.realizePos_of_mem_vertexSet

@[simp] theorem realizeDrawing_newEdge₁ :
    d.realizeDrawing R t d.newEdge₁ = subarc (R.drawing d.edge) (d.leftParam R) t := if_pos rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁ ``Submission.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₁

@[simp] theorem realizeDrawing_newEdge₂ :
    d.realizeDrawing R t d.newEdge₂ = subarc (R.drawing d.edge) t (d.rightParam R) := by
  rw [realizeDrawing, if_neg d.newEdge_ne.symm, if_pos rfl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂ ``Submission.Schoenflies.CellStructure.SubdivData.realizeDrawing_newEdge₂

theorem realizeDrawing_of_ne {f : γ} (h₁ : f ≠ d.newEdge₁) (h₂ : f ≠ d.newEdge₂) :
    d.realizeDrawing R t f = R.drawing f := by rw [realizeDrawing, if_neg h₁, if_neg h₂]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizeDrawing_of_ne then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizeDrawing_of_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizeDrawing_of_ne ``Submission.Schoenflies.CellStructure.SubdivData.realizeDrawing_of_ne

theorem realizeDrawing_of_mem_cells {f : γ} (h : f ∈ S.cells) :
    d.realizeDrawing R t f = R.drawing f :=
  realizeDrawing_of_ne (d.ne_newEdge₁_of_mem_cells h) (d.ne_newEdge₂_of_mem_cells h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizeDrawing_of_mem_cells then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizeDrawing_of_mem_cells"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizeDrawing_of_mem_cells ``Submission.Schoenflies.CellStructure.SubdivData.realizeDrawing_of_mem_cells

@[simp] theorem realizeCell_newVertex : d.realizeCell R t d.newVertex = {R.drawing d.edge t} :=
  if_pos rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizeCell_newVertex then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizeCell_newVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizeCell_newVertex ``Submission.Schoenflies.CellStructure.SubdivData.realizeCell_newVertex

@[simp] theorem realizeCell_newEdge₁ : d.realizeCell R t d.newEdge₁ =
    R.drawing d.edge '' _root_.Set.uIcc (d.leftParam R) t \ {R.pos d.left, R.drawing d.edge t} := by
  rw [realizeCell, if_neg d.newVertex_ne₁.symm, if_pos rfl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁ ``Submission.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₁

@[simp] theorem realizeCell_newEdge₂ : d.realizeCell R t d.newEdge₂ =
    R.drawing d.edge '' _root_.Set.uIcc t (d.rightParam R) \ {R.drawing d.edge t, R.pos d.right} := by
  rw [realizeCell, if_neg d.newVertex_ne₂.symm, if_neg d.newEdge_ne.symm, if_pos rfl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂ ``Submission.Schoenflies.CellStructure.SubdivData.realizeCell_newEdge₂

theorem realizeCell_of_mem_cells {c : γ} (h : c ∈ S.cells) : d.realizeCell R t c = R.cell c := by
  rw [realizeCell, if_neg (d.ne_newVertex_of_mem_cells h), if_neg (d.ne_newEdge₁_of_mem_cells h),
    if_neg (d.ne_newEdge₂_of_mem_cells h)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizeCell_of_mem_cells then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizeCell_of_mem_cells"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizeCell_of_mem_cells ``Submission.Schoenflies.CellStructure.SubdivData.realizeCell_of_mem_cells

/-! ### The two half arcs -/

theorem edgeArc_newEdge₁ : edgeArc (d.realizeDrawing R t) d.newEdge₁ =
    R.drawing d.edge '' _root_.Set.uIcc (d.leftParam R) t := by
  rw [edgeArc, realizeDrawing_newEdge₁, subarc_image]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.edgeArc_newEdge₁ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.edgeArc_newEdge₁"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.edgeArc_newEdge₁ ``Submission.Schoenflies.CellStructure.SubdivData.edgeArc_newEdge₁

theorem edgeArc_newEdge₂ : edgeArc (d.realizeDrawing R t) d.newEdge₂ =
    R.drawing d.edge '' _root_.Set.uIcc t (d.rightParam R) := by
  rw [edgeArc, realizeDrawing_newEdge₂, subarc_image]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.edgeArc_newEdge₂ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.edgeArc_newEdge₂"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.edgeArc_newEdge₂ ``Submission.Schoenflies.CellStructure.SubdivData.edgeArc_newEdge₂

theorem edgeArc_of_ne {f : γ} (h₁ : f ≠ d.newEdge₁) (h₂ : f ≠ d.newEdge₂) :
    edgeArc (d.realizeDrawing R t) f = edgeArc R.drawing f := by
  rw [edgeArc, edgeArc, realizeDrawing_of_ne h₁ h₂]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.edgeArc_of_ne then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.edgeArc_of_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.edgeArc_of_ne ``Submission.Schoenflies.CellStructure.SubdivData.edgeArc_of_ne

/-! ### The two cell-shape fields of a realization -/

/-- Every 0-cell of the subdivided structure is realized by its point. -/
theorem cell_vertex_realize ⦃v : γ⦄ (hv : v ∈ V(d.skeleton)) :
    d.realizeCell R t v = {d.realizePos R t v} := by
  rw [d.skeleton_vertexSet, _root_.Set.mem_insert_iff] at hv
  rcases hv with rfl | hv
  · rw [realizeCell_newVertex, realizePos_newVertex]
  · rw [realizeCell_of_mem_cells (S.mem_cells_of_mem_vertexSet hv),
      realizePos_of_mem_vertexSet hv, R.cell_vertex hv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.cell_vertex_realize then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.cell_vertex_realize"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.cell_vertex_realize ``Submission.Schoenflies.CellStructure.SubdivData.cell_vertex_realize

/-- Every 1-cell of the subdivided structure is realized by its open arc. -/
theorem cell_edge_realize ⦃g x y : γ⦄ (hl : d.skeleton.IsLink g x y) :
    d.realizeCell R t g =
      edgeArc (d.realizeDrawing R t) g \ {d.realizePos R t x, d.realizePos R t y} := by
  rcases d.skeleton_isLink.1 hl with ⟨hlS, -, hg₁, hg₂⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩
  · rw [realizeCell_of_mem_cells (S.mem_cells_of_mem_edgeSet hlS.edge_mem),
      edgeArc_of_ne hg₁ hg₂, realizePos_of_mem_vertexSet hlS.left_mem,
      realizePos_of_mem_vertexSet hlS.right_mem, R.cell_edge hlS]
  · rw [realizeCell_newEdge₁, edgeArc_newEdge₁]
    rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [realizePos_of_mem_vertexSet d.isLink.left_mem, realizePos_newVertex]
    · rw [realizePos_of_mem_vertexSet d.isLink.left_mem, realizePos_newVertex, _root_.Set.pair_comm]
  · rw [realizeCell_newEdge₂, edgeArc_newEdge₂]
    rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [realizePos_of_mem_vertexSet d.isLink.right_mem, realizePos_newVertex]
    · rw [realizePos_of_mem_vertexSet d.isLink.right_mem, realizePos_newVertex, _root_.Set.pair_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.cell_edge_realize then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.cell_edge_realize"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.cell_edge_realize ``Submission.Schoenflies.CellStructure.SubdivData.cell_edge_realize

section

variable (ht : t ∈ Ioo (0 : ℝ) 1)
include ht

/-- Distinct 0-cells of the subdivided structure sit at distinct points: the new one is an
interior point of a drawn edge, so it is none of the old ones. -/
theorem injOn_realizePos : _root_.Set.InjOn (d.realizePos R t) V(d.skeleton) := by
  intro p hp q hq hpq
  rw [d.skeleton_vertexSet, _root_.Set.mem_insert_iff] at hp hq
  rcases hp with rfl | hp
  · rcases hq with rfl | hq
    · rfl
    · rw [realizePos_newVertex, realizePos_of_mem_vertexSet hq] at hpq
      exact absurd hpq (d.newPos_ne_pos R ht hq)
  · rcases hq with rfl | hq
    · rw [realizePos_of_mem_vertexSet hp, realizePos_newVertex] at hpq
      exact absurd hpq.symm (d.newPos_ne_pos R ht hp)
    · rw [realizePos_of_mem_vertexSet hp, realizePos_of_mem_vertexSet hq] at hpq
      exact R.injOn_pos hp hq hpq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.injOn_realizePos then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.injOn_realizePos"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.injOn_realizePos ``Submission.Schoenflies.CellStructure.SubdivData.injOn_realizePos

theorem edgeArc_newEdge₁_subset :
    edgeArc (d.realizeDrawing R t) d.newEdge₁ ⊆ edgeArc R.drawing d.edge := by
  rw [edgeArc_newEdge₁, edgeArc]
  exact _root_.Set.image_mono ((uIcc_left_subset (d.mem_uIcc_params R ht)).trans (d.uIcc_params R).subset)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.edgeArc_newEdge₁_subset then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.edgeArc_newEdge₁_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.edgeArc_newEdge₁_subset ``Submission.Schoenflies.CellStructure.SubdivData.edgeArc_newEdge₁_subset

theorem edgeArc_newEdge₂_subset :
    edgeArc (d.realizeDrawing R t) d.newEdge₂ ⊆ edgeArc R.drawing d.edge := by
  rw [edgeArc_newEdge₂, edgeArc]
  exact _root_.Set.image_mono ((uIcc_right_subset (d.mem_uIcc_params R ht)).trans (d.uIcc_params R).subset)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.edgeArc_newEdge₂_subset then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.edgeArc_newEdge₂_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.edgeArc_newEdge₂_subset ``Submission.Schoenflies.CellStructure.SubdivData.edgeArc_newEdge₂_subset

/-- **The two new arcs cover the old one.** -/
theorem edgeArc_new_union : edgeArc (d.realizeDrawing R t) d.newEdge₁ ∪
    edgeArc (d.realizeDrawing R t) d.newEdge₂ = edgeArc R.drawing d.edge := by
  rw [edgeArc_newEdge₁, edgeArc_newEdge₂, ← _root_.Set.image_union,
    uIcc_union_uIcc (d.mem_uIcc_params R ht), d.uIcc_params R, edgeArc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.edgeArc_new_union then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.edgeArc_new_union"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.edgeArc_new_union ``Submission.Schoenflies.CellStructure.SubdivData.edgeArc_new_union

/-- **The two new arcs meet exactly at the new point.** -/
theorem edgeArc_new_inter : edgeArc (d.realizeDrawing R t) d.newEdge₁ ∩
    edgeArc (d.realizeDrawing R t) d.newEdge₂ = {R.drawing d.edge t} := by
  rw [edgeArc_newEdge₁, edgeArc_newEdge₂,
    ← (d.injOn_drawing_edge R).mono (d.uIcc_params R).subset |>.image_inter
      (uIcc_left_subset (d.mem_uIcc_params R ht)) (uIcc_right_subset (d.mem_uIcc_params R ht)),
    uIcc_inter_uIcc (d.mem_uIcc_params R ht), _root_.Set.image_singleton]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.edgeArc_new_inter then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.edgeArc_new_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.edgeArc_new_inter ``Submission.Schoenflies.CellStructure.SubdivData.edgeArc_new_inter

omit ht in
theorem posLeft_mem_edgeArc_newEdge₁ :
    R.pos d.left ∈ edgeArc (d.realizeDrawing R t) d.newEdge₁ := by
  rw [edgeArc_newEdge₁, ← d.drawing_leftParam R]
  exact ⟨_, _root_.Set.left_mem_uIcc, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.posLeft_mem_edgeArc_newEdge₁ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.posLeft_mem_edgeArc_newEdge₁"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.posLeft_mem_edgeArc_newEdge₁ ``Submission.Schoenflies.CellStructure.SubdivData.posLeft_mem_edgeArc_newEdge₁

omit ht in
theorem posRight_mem_edgeArc_newEdge₂ :
    R.pos d.right ∈ edgeArc (d.realizeDrawing R t) d.newEdge₂ := by
  rw [edgeArc_newEdge₂, ← d.drawing_rightParam R]
  exact ⟨_, _root_.Set.right_mem_uIcc, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.posRight_mem_edgeArc_newEdge₂ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.posRight_mem_edgeArc_newEdge₂"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.posRight_mem_edgeArc_newEdge₂ ``Submission.Schoenflies.CellStructure.SubdivData.posRight_mem_edgeArc_newEdge₂

omit ht in
theorem newPos_mem_edgeArc_newEdge₁ :
    R.drawing d.edge t ∈ edgeArc (d.realizeDrawing R t) d.newEdge₁ := by
  rw [edgeArc_newEdge₁]; exact ⟨t, _root_.Set.right_mem_uIcc, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.newPos_mem_edgeArc_newEdge₁ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.newPos_mem_edgeArc_newEdge₁"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.newPos_mem_edgeArc_newEdge₁ ``Submission.Schoenflies.CellStructure.SubdivData.newPos_mem_edgeArc_newEdge₁

omit ht in
theorem newPos_mem_edgeArc_newEdge₂ :
    R.drawing d.edge t ∈ edgeArc (d.realizeDrawing R t) d.newEdge₂ := by
  rw [edgeArc_newEdge₂]; exact ⟨t, _root_.Set.left_mem_uIcc, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.newPos_mem_edgeArc_newEdge₂ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.newPos_mem_edgeArc_newEdge₂"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.newPos_mem_edgeArc_newEdge₂ ``Submission.Schoenflies.CellStructure.SubdivData.newPos_mem_edgeArc_newEdge₂

/-- The far endpoint of the old edge misses the near half. -/
theorem posRight_notMem_edgeArc_newEdge₁ :
    R.pos d.right ∉ edgeArc (d.realizeDrawing R t) d.newEdge₁ := by
  rw [edgeArc_newEdge₁, ← d.drawing_rightParam R]
  rintro ⟨s, hs, hseq⟩
  have hsI : s ∈ I :=
    ((uIcc_left_subset (d.mem_uIcc_params R ht)).trans (d.uIcc_params R).subset) hs
  have : s = d.rightParam R := d.injOn_drawing_edge R hsI (d.rightParam_mem_I R) hseq
  exact right_notMem_uIcc_left (d.mem_uIcc_params R ht) (d.rightParam_ne R ht) (this ▸ hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.posRight_notMem_edgeArc_newEdge₁ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.posRight_notMem_edgeArc_newEdge₁"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.posRight_notMem_edgeArc_newEdge₁ ``Submission.Schoenflies.CellStructure.SubdivData.posRight_notMem_edgeArc_newEdge₁

theorem posLeft_notMem_edgeArc_newEdge₂ :
    R.pos d.left ∉ edgeArc (d.realizeDrawing R t) d.newEdge₂ := by
  rw [edgeArc_newEdge₂, ← d.drawing_leftParam R]
  rintro ⟨s, hs, hseq⟩
  have hsI : s ∈ I :=
    ((uIcc_right_subset (d.mem_uIcc_params R ht)).trans (d.uIcc_params R).subset) hs
  have : s = d.leftParam R := d.injOn_drawing_edge R hsI (d.leftParam_mem_I R) hseq
  exact left_notMem_uIcc_right (d.mem_uIcc_params R ht) (d.leftParam_ne R ht) (this ▸ hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.posLeft_notMem_edgeArc_newEdge₂ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.posLeft_notMem_edgeArc_newEdge₂"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.posLeft_notMem_edgeArc_newEdge₂ ``Submission.Schoenflies.CellStructure.SubdivData.posLeft_notMem_edgeArc_newEdge₂

/-- The new point lies on no old edge but the subdivided one. -/
theorem newPos_notMem_edgeArc_of_ne {f : γ} (hf : f ∈ E(S.skel)) (hfe : f ≠ d.edge) :
    R.drawing d.edge t ∉ edgeArc R.drawing f := fun hva =>
  d.newPos_notMem_vertexSet R ht
    (R.isDrawing.arcs_meet_at_vertex (d.edge_mem_edgeSet_graph R)
      (by rw [_root_.Graph.edgeSet_map]; exact hf) (Ne.symm hfe)
      ⟨t, _root_.Set.Ioo_subset_Icc_self ht, rfl⟩ hva)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.newPos_notMem_edgeArc_of_ne then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.newPos_notMem_edgeArc_of_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.newPos_notMem_edgeArc_of_ne ``Submission.Schoenflies.CellStructure.SubdivData.newPos_notMem_edgeArc_of_ne

/-! ### The subdivided drawn skeleton -/

omit ht in
theorem realizeGraph_edgeSet : E(d.realizeGraph R t) = E(d.skeleton) := _root_.Graph.edgeSet_map _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizeGraph_edgeSet then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizeGraph_edgeSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizeGraph_edgeSet ``Submission.Schoenflies.CellStructure.SubdivData.realizeGraph_edgeSet

omit ht in
theorem realizePos_image_vertexSet : d.realizePos R t '' V(S.skel) = R.pos '' V(S.skel) :=
  _root_.Set.image_congr fun _ hv => realizePos_of_mem_vertexSet hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizePos_image_vertexSet then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizePos_image_vertexSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizePos_image_vertexSet ``Submission.Schoenflies.CellStructure.SubdivData.realizePos_image_vertexSet

omit ht in
theorem realizeGraph_vertexSet :
    V(d.realizeGraph R t) = _root_.Insert.insert (R.drawing d.edge t) V(R.graph) := by
  rw [realizeGraph, _root_.Graph.vertexSet_map, d.skeleton_vertexSet, _root_.Set.image_insert_eq, realizePos_newVertex,
    realizePos_image_vertexSet, Realization.vertexSet_graph]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizeGraph_vertexSet then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizeGraph_vertexSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizeGraph_vertexSet ``Submission.Schoenflies.CellStructure.SubdivData.realizeGraph_vertexSet

omit ht in
theorem mem_realizeGraph_vertexSet_of_mem {p : Plane} (hp : p ∈ V(R.graph)) :
    p ∈ V(d.realizeGraph R t) := by
  rw [realizeGraph_vertexSet]; exact _root_.Set.mem_insert_of_mem _ hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.mem_realizeGraph_vertexSet_of_mem then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.mem_realizeGraph_vertexSet_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.mem_realizeGraph_vertexSet_of_mem ``Submission.Schoenflies.CellStructure.SubdivData.mem_realizeGraph_vertexSet_of_mem

omit ht in
/-- An edge of the subdivided drawn skeleton that is neither new is an old edge, and not the
subdivided one. -/
theorem mem_edgeSet_skel_of_ne {f : γ} (hf : f ∈ E(d.realizeGraph R t))
    (h₁ : f ≠ d.newEdge₁) (h₂ : f ≠ d.newEdge₂) : f ∈ E(S.skel) ∧ f ≠ d.edge := by
  rw [realizeGraph_edgeSet, d.skeleton_edgeSet] at hf
  simp only [_root_.Set.mem_insert_iff, _root_.Set.mem_sdiff, _root_.Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | h
  exacts [absurd rfl h₁, absurd rfl h₂, h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.mem_edgeSet_skel_of_ne then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.mem_edgeSet_skel_of_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.mem_edgeSet_skel_of_ne ``Submission.Schoenflies.CellStructure.SubdivData.mem_edgeSet_skel_of_ne

omit ht in
/-- For an old edge the two drawn skeleta have the same links. -/
theorem realizeGraph_isLink_old {f : γ} {x y : Plane} (hf : f ∈ E(S.skel)) (hfe : f ≠ d.edge) :
    (d.realizeGraph R t).IsLink f x y ↔ R.graph.IsLink f x y := by
  constructor
  · rintro ⟨p, q, hpq, rfl, rfl⟩
    rw [d.skeleton_isLink_old_iff hf hfe] at hpq
    rw [realizePos_of_mem_vertexSet hpq.left_mem, realizePos_of_mem_vertexSet hpq.right_mem]
    exact hpq.map R.pos
  · rintro ⟨p, q, hpq, rfl, rfl⟩
    exact ⟨p, q, d.skeleton_isLink_of_old hfe hpq,
      realizePos_of_mem_vertexSet hpq.left_mem, realizePos_of_mem_vertexSet hpq.right_mem⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizeGraph_isLink_old then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizeGraph_isLink_old"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizeGraph_isLink_old ``Submission.Schoenflies.CellStructure.SubdivData.realizeGraph_isLink_old

omit ht in
theorem realizeGraph_inc_old {f : γ} {p : Plane} (hf : f ∈ E(S.skel)) (hfe : f ≠ d.edge) :
    (d.realizeGraph R t).Inc f p ↔ R.graph.Inc f p :=
  exists_congr fun _ => realizeGraph_isLink_old hf hfe

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizeGraph_inc_old then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizeGraph_inc_old"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizeGraph_inc_old ``Submission.Schoenflies.CellStructure.SubdivData.realizeGraph_inc_old

omit ht in
theorem realizeGraph_isLink_newEdge₁ :
    (d.realizeGraph R t).IsLink d.newEdge₁ (R.pos d.left) (R.drawing d.edge t) := by
  have h := d.isLink_newEdge₁.map (d.realizePos R t)
  rwa [realizePos_of_mem_vertexSet d.isLink.left_mem, realizePos_newVertex] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizeGraph_isLink_newEdge₁ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizeGraph_isLink_newEdge₁"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizeGraph_isLink_newEdge₁ ``Submission.Schoenflies.CellStructure.SubdivData.realizeGraph_isLink_newEdge₁

omit ht in
theorem realizeGraph_isLink_newEdge₂ :
    (d.realizeGraph R t).IsLink d.newEdge₂ (R.drawing d.edge t) (R.pos d.right) := by
  have h := d.isLink_newEdge₂.map (d.realizePos R t)
  rwa [realizePos_of_mem_vertexSet d.isLink.right_mem, realizePos_newVertex] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizeGraph_isLink_newEdge₂ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizeGraph_isLink_newEdge₂"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizeGraph_isLink_newEdge₂ ``Submission.Schoenflies.CellStructure.SubdivData.realizeGraph_isLink_newEdge₂

/-- A vertex on the first new arc is one of its two ends. -/
theorem mem_edgeArc_newEdge₁_vertex {p : Plane} (hp : p ∈ V(d.realizeGraph R t))
    (hpa : p ∈ edgeArc (d.realizeDrawing R t) d.newEdge₁) :
    p = R.pos d.left ∨ p = R.drawing d.edge t := by
  rw [realizeGraph_vertexSet, _root_.Set.mem_insert_iff] at hp
  rcases hp with rfl | hp
  · exact Or.inr rfl
  · rcases R.isDrawing.vertex_mem_edgeArc (d.isLink_drawn_edge R) hp
      (edgeArc_newEdge₁_subset ht hpa) with h | h
    · exact Or.inl h
    · exact absurd (h ▸ hpa) (posRight_notMem_edgeArc_newEdge₁ ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.mem_edgeArc_newEdge₁_vertex then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.mem_edgeArc_newEdge₁_vertex"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.mem_edgeArc_newEdge₁_vertex ``Submission.Schoenflies.CellStructure.SubdivData.mem_edgeArc_newEdge₁_vertex

/-- A vertex on the second new arc is one of its two ends. -/
theorem mem_edgeArc_newEdge₂_vertex {p : Plane} (hp : p ∈ V(d.realizeGraph R t))
    (hpa : p ∈ edgeArc (d.realizeDrawing R t) d.newEdge₂) :
    p = R.drawing d.edge t ∨ p = R.pos d.right := by
  rw [realizeGraph_vertexSet, _root_.Set.mem_insert_iff] at hp
  rcases hp with rfl | hp
  · exact Or.inl rfl
  · rcases R.isDrawing.vertex_mem_edgeArc (d.isLink_drawn_edge R) hp
      (edgeArc_newEdge₂_subset ht hpa) with h | h
    · exact absurd (h ▸ hpa) (posLeft_notMem_edgeArc_newEdge₂ ht)
    · exact Or.inr h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.mem_edgeArc_newEdge₂_vertex then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.mem_edgeArc_newEdge₂_vertex"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.mem_edgeArc_newEdge₂_vertex ``Submission.Schoenflies.CellStructure.SubdivData.mem_edgeArc_newEdge₂_vertex

/-! ### Where two edges of the subdivided drawing meet -/

/-- The two new edges meet exactly at the new vertex. -/
theorem edge_inter_new_new {p : Plane}
    (hp₁ : p ∈ edgeArc (d.realizeDrawing R t) d.newEdge₁)
    (hp₂ : p ∈ edgeArc (d.realizeDrawing R t) d.newEdge₂) :
    p ∈ V(d.realizeGraph R t) ∧ (d.realizeGraph R t).Inc d.newEdge₁ p ∧
      (d.realizeGraph R t).Inc d.newEdge₂ p := by
  have hmem : p ∈ ({R.drawing d.edge t} : Set Plane) := by
    rw [← edgeArc_new_inter ht]; exact ⟨hp₁, hp₂⟩
  rw [_root_.Set.mem_singleton_iff] at hmem
  subst hmem
  exact ⟨by rw [realizeGraph_vertexSet]; exact _root_.Set.mem_insert _ _,
    (realizeGraph_isLink_newEdge₁).inc_right, (realizeGraph_isLink_newEdge₂).inc_left⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.edge_inter_new_new then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.edge_inter_new_new"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.edge_inter_new_new ``Submission.Schoenflies.CellStructure.SubdivData.edge_inter_new_new

/-- The first new edge meets an old edge only at the position of `d.left`. -/
theorem edge_inter_newEdge₁_old {g : γ} (hg : g ∈ E(S.skel)) (hge : g ≠ d.edge) {p : Plane}
    (hp₁ : p ∈ edgeArc (d.realizeDrawing R t) d.newEdge₁)
    (hpg : p ∈ edgeArc (d.realizeDrawing R t) g) :
    p ∈ V(d.realizeGraph R t) ∧ (d.realizeGraph R t).Inc d.newEdge₁ p ∧
      (d.realizeGraph R t).Inc g p := by
  have hgc := S.mem_cells_of_mem_edgeSet hg
  rw [edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hgc) (d.ne_newEdge₂_of_mem_cells hgc)] at hpg
  obtain ⟨hpV, -, hpgInc⟩ := R.isDrawing.edge_inter (d.edge_mem_edgeSet_graph R)
    (by rw [_root_.Graph.edgeSet_map]; exact hg) (Ne.symm hge)
    (edgeArc_newEdge₁_subset ht hp₁) hpg
  rcases mem_edgeArc_newEdge₁_vertex ht (mem_realizeGraph_vertexSet_of_mem hpV) hp₁ with
    h | h
  · subst h
    exact ⟨mem_realizeGraph_vertexSet_of_mem hpV, (realizeGraph_isLink_newEdge₁).inc_left,
      (realizeGraph_inc_old hg hge).2 hpgInc⟩
  · exact absurd (h ▸ hpV) (d.newPos_notMem_vertexSet R ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.edge_inter_newEdge₁_old then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.edge_inter_newEdge₁_old"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.edge_inter_newEdge₁_old ``Submission.Schoenflies.CellStructure.SubdivData.edge_inter_newEdge₁_old

/-- The second new edge meets an old edge only at the position of `d.right`. -/
theorem edge_inter_newEdge₂_old {g : γ} (hg : g ∈ E(S.skel)) (hge : g ≠ d.edge) {p : Plane}
    (hp₂ : p ∈ edgeArc (d.realizeDrawing R t) d.newEdge₂)
    (hpg : p ∈ edgeArc (d.realizeDrawing R t) g) :
    p ∈ V(d.realizeGraph R t) ∧ (d.realizeGraph R t).Inc d.newEdge₂ p ∧
      (d.realizeGraph R t).Inc g p := by
  have hgc := S.mem_cells_of_mem_edgeSet hg
  rw [edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hgc) (d.ne_newEdge₂_of_mem_cells hgc)] at hpg
  obtain ⟨hpV, -, hpgInc⟩ := R.isDrawing.edge_inter (d.edge_mem_edgeSet_graph R)
    (by rw [_root_.Graph.edgeSet_map]; exact hg) (Ne.symm hge)
    (edgeArc_newEdge₂_subset ht hp₂) hpg
  rcases mem_edgeArc_newEdge₂_vertex ht (mem_realizeGraph_vertexSet_of_mem hpV) hp₂ with
    h | h
  · exact absurd (h ▸ hpV) (d.newPos_notMem_vertexSet R ht)
  · subst h
    exact ⟨mem_realizeGraph_vertexSet_of_mem hpV,
      (realizeGraph_isLink_newEdge₂).inc_right, (realizeGraph_inc_old hg hge).2 hpgInc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.edge_inter_newEdge₂_old then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.edge_inter_newEdge₂_old"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.edge_inter_newEdge₂_old ``Submission.Schoenflies.CellStructure.SubdivData.edge_inter_newEdge₂_old

omit ht in
/-- Two old edges meet where they met before. -/
theorem edge_inter_old_old {f g : γ} (hf : f ∈ E(S.skel)) (hfe : f ≠ d.edge)
    (hg : g ∈ E(S.skel)) (hge : g ≠ d.edge) (hfg : f ≠ g) {p : Plane}
    (hpf : p ∈ edgeArc (d.realizeDrawing R t) f) (hpg : p ∈ edgeArc (d.realizeDrawing R t) g) :
    p ∈ V(d.realizeGraph R t) ∧ (d.realizeGraph R t).Inc f p ∧ (d.realizeGraph R t).Inc g p := by
  have hfc := S.mem_cells_of_mem_edgeSet hf
  have hgc := S.mem_cells_of_mem_edgeSet hg
  rw [edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hfc) (d.ne_newEdge₂_of_mem_cells hfc)] at hpf
  rw [edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hgc) (d.ne_newEdge₂_of_mem_cells hgc)] at hpg
  obtain ⟨hpV, h₁, h₂⟩ := R.isDrawing.edge_inter (by rw [_root_.Graph.edgeSet_map]; exact hf)
    (by rw [_root_.Graph.edgeSet_map]; exact hg) hfg hpf hpg
  exact ⟨mem_realizeGraph_vertexSet_of_mem hpV, (realizeGraph_inc_old hf hfe).2 h₁,
    (realizeGraph_inc_old hg hge).2 h₂⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.edge_inter_old_old then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.edge_inter_old_old"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.edge_inter_old_old ``Submission.Schoenflies.CellStructure.SubdivData.edge_inter_old_old

/-! ### The subdivided drawing -/

/-- **The subdivided data really is a drawing.** -/
theorem isDrawing_realize : IsDrawing (d.realizeGraph R t) (d.realizeDrawing R t) where
  edge_param := by
    intro f hf
    rw [realizeGraph_edgeSet, d.skeleton_edgeSet] at hf
    simp only [_root_.Set.mem_insert_iff, _root_.Set.mem_sdiff, _root_.Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | ⟨hfS, hfe⟩
    · rw [realizeDrawing_newEdge₁]
      refine ⟨continuousOn_subarc (d.continuousOn_drawing_edge R) (d.leftParam_mem_I R)
          (_root_.Set.Ioo_subset_Icc_self ht),
        injOn_subarc ((d.injOn_drawing_edge R).mono
          (uIcc_subset_I (d.leftParam_mem_I R) (_root_.Set.Ioo_subset_Icc_self ht))) (d.leftParam_ne R ht),
        ?_⟩
      rw [subarc_zero, subarc_one, d.drawing_leftParam R]
      exact realizeGraph_isLink_newEdge₁
    · rw [realizeDrawing_newEdge₂]
      refine ⟨continuousOn_subarc (d.continuousOn_drawing_edge R) (_root_.Set.Ioo_subset_Icc_self ht)
          (d.rightParam_mem_I R),
        injOn_subarc ((d.injOn_drawing_edge R).mono
          (uIcc_subset_I (_root_.Set.Ioo_subset_Icc_self ht) (d.rightParam_mem_I R)))
          (Ne.symm (d.rightParam_ne R ht)), ?_⟩
      rw [subarc_zero, subarc_one, d.drawing_rightParam R]
      exact realizeGraph_isLink_newEdge₂
    · have hfc := S.mem_cells_of_mem_edgeSet hfS
      rw [realizeDrawing_of_mem_cells hfc]
      have hd := R.isDrawing.edge_param
        (show f ∈ E(R.graph) by rw [Realization.edgeSet_graph]; exact hfS)
      exact ⟨hd.1, hd.2.1, (realizeGraph_isLink_old hfS hfe).2 hd.2.2⟩
  vertex_mem_edgeArc := by
    intro f x y v hl hv hva
    by_cases hf₁ : f = d.newEdge₁
    · subst hf₁
      rcases hl.eq_and_eq_or_eq_and_eq (realizeGraph_isLink_newEdge₁) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact mem_edgeArc_newEdge₁_vertex ht hv hva
      · exact (mem_edgeArc_newEdge₁_vertex ht hv hva).symm
    · by_cases hf₂ : f = d.newEdge₂
      · subst hf₂
        rcases hl.eq_and_eq_or_eq_and_eq (realizeGraph_isLink_newEdge₂) with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact mem_edgeArc_newEdge₂_vertex ht hv hva
        · exact (mem_edgeArc_newEdge₂_vertex ht hv hva).symm
      · obtain ⟨hfS, hfe⟩ := mem_edgeSet_skel_of_ne hl.edge_mem hf₁ hf₂
        rw [edgeArc_of_ne hf₁ hf₂] at hva
        rw [realizeGraph_isLink_old hfS hfe] at hl
        rw [realizeGraph_vertexSet, _root_.Set.mem_insert_iff] at hv
        rcases hv with rfl | hv
        · exact absurd hva (newPos_notMem_edgeArc_of_ne ht hfS hfe)
        · exact R.isDrawing.vertex_mem_edgeArc hl hv hva
  edge_inter := by
    intro f g hf hg hfg p hpf hpg
    by_cases hf₁ : f = d.newEdge₁
    · subst hf₁
      by_cases hg₂ : g = d.newEdge₂
      · subst hg₂
        exact edge_inter_new_new ht hpf hpg
      · obtain ⟨hgS, hge⟩ := mem_edgeSet_skel_of_ne hg (Ne.symm hfg) hg₂
        exact edge_inter_newEdge₁_old ht hgS hge hpf hpg
    · by_cases hf₂ : f = d.newEdge₂
      · subst hf₂
        by_cases hg₁ : g = d.newEdge₁
        · subst hg₁
          obtain ⟨h₁, h₂, h₃⟩ := edge_inter_new_new ht hpg hpf
          exact ⟨h₁, h₃, h₂⟩
        · obtain ⟨hgS, hge⟩ := mem_edgeSet_skel_of_ne hg hg₁ (Ne.symm hfg)
          exact edge_inter_newEdge₂_old ht hgS hge hpf hpg
      · obtain ⟨hfS, hfe⟩ := mem_edgeSet_skel_of_ne hf hf₁ hf₂
        by_cases hg₁ : g = d.newEdge₁
        · subst hg₁
          obtain ⟨h₁, h₂, h₃⟩ := edge_inter_newEdge₁_old ht hfS hfe hpg hpf
          exact ⟨h₁, h₃, h₂⟩
        · by_cases hg₂ : g = d.newEdge₂
          · subst hg₂
            obtain ⟨h₁, h₂, h₃⟩ := edge_inter_newEdge₂_old ht hfS hfe hpg hpf
            exact ⟨h₁, h₃, h₂⟩
          · obtain ⟨hgS, hge⟩ := mem_edgeSet_skel_of_ne hg hg₁ hg₂
            exact edge_inter_old_old hfS hfe hgS hge hfg hpf hpg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.isDrawing_realize then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.isDrawing_realize"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.isDrawing_realize ``Submission.Schoenflies.CellStructure.SubdivData.isDrawing_realize

/-! ### The two new open edges, as arcs -/

/-- The first new edge is drawn as an arc from the position of `d.left` to the new point. -/
theorem isArcBetween_newEdge₁ : IsArcBetween (edgeArc (d.realizeDrawing R t) d.newEdge₁)
    (R.pos d.left) (R.drawing d.edge t) := by
  rw [edgeArc_newEdge₁, ← d.drawing_leftParam R]
  exact isArcBetween_subarc_of_injOn_I (d.continuousOn_drawing_edge R) (d.injOn_drawing_edge R)
    (d.leftParam_mem_I R) (_root_.Set.Ioo_subset_Icc_self ht) (d.leftParam_ne R ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.isArcBetween_newEdge₁ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.isArcBetween_newEdge₁"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.isArcBetween_newEdge₁ ``Submission.Schoenflies.CellStructure.SubdivData.isArcBetween_newEdge₁

/-- The second new edge is drawn as an arc from the new point to the position of `d.right`. -/
theorem isArcBetween_newEdge₂ : IsArcBetween (edgeArc (d.realizeDrawing R t) d.newEdge₂)
    (R.drawing d.edge t) (R.pos d.right) := by
  rw [edgeArc_newEdge₂, ← d.drawing_rightParam R]
  exact isArcBetween_subarc_of_injOn_I (d.continuousOn_drawing_edge R) (d.injOn_drawing_edge R)
    (_root_.Set.Ioo_subset_Icc_self ht) (d.rightParam_mem_I R) (Ne.symm (d.rightParam_ne R ht))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.isArcBetween_newEdge₂ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.isArcBetween_newEdge₂"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.isArcBetween_newEdge₂ ``Submission.Schoenflies.CellStructure.SubdivData.isArcBetween_newEdge₂

end

/-! ### The realization of the subdivided structure -/

/-- **The realization of an edge subdivision.** The new 0-cell goes to the point of the drawn
edge at parameter `t`, the two new 1-cells are drawn by the two halves of that parametrization,
and every surviving cell is exactly where it was.

There is no geometric side condition: everything the construction needs is already carried by
`R`, and is extracted by the lemmas above rather than assumed. -/
noncomputable def realize (d : S.SubdivData) (R : S.Realization) (t : ℝ)
    (ht : t ∈ _root_.Set.Ioo (0 : ℝ) 1) : (S.subdivideEdge d).Realization where
  pos := d.realizePos R t
  drawing := d.realizeDrawing R t
  injOn_pos := injOn_realizePos ht
  isDrawing := isDrawing_realize ht
  cell := d.realizeCell R t
  cell_vertex := cell_vertex_realize
  cell_edge := cell_edge_realize

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realize then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realize"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realize ``Submission.Schoenflies.CellStructure.SubdivData.realize

variable (ht : t ∈ Ioo (0 : ℝ) 1)

@[simp] theorem realize_pos : (d.realize R t ht).pos = d.realizePos R t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realize_pos then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realize_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realize_pos ``Submission.Schoenflies.CellStructure.SubdivData.realize_pos

@[simp] theorem realize_drawing : (d.realize R t ht).drawing = d.realizeDrawing R t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realize_drawing then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realize_drawing"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realize_drawing ``Submission.Schoenflies.CellStructure.SubdivData.realize_drawing

@[simp] theorem realize_cell : (d.realize R t ht).cell = d.realizeCell R t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realize_cell then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realize_cell"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realize_cell ``Submission.Schoenflies.CellStructure.SubdivData.realize_cell

include ht

/-! ### The realization refines the old one -/

theorem closure_realizeCell_newEdge₁ :
    closure (d.realizeCell R t d.newEdge₁) = edgeArc (d.realizeDrawing R t) d.newEdge₁ := by
  rw [realizeCell_newEdge₁, ← edgeArc_newEdge₁]
  exact (isArcBetween_newEdge₁ ht).closure_diff_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.closure_realizeCell_newEdge₁ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.closure_realizeCell_newEdge₁"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.closure_realizeCell_newEdge₁ ``Submission.Schoenflies.CellStructure.SubdivData.closure_realizeCell_newEdge₁

theorem closure_realizeCell_newEdge₂ :
    closure (d.realizeCell R t d.newEdge₂) = edgeArc (d.realizeDrawing R t) d.newEdge₂ := by
  rw [realizeCell_newEdge₂, ← edgeArc_newEdge₂]
  exact (isArcBetween_newEdge₂ ht).closure_diff_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.closure_realizeCell_newEdge₂ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.closure_realizeCell_newEdge₂"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.closure_realizeCell_newEdge₂ ``Submission.Schoenflies.CellStructure.SubdivData.closure_realizeCell_newEdge₂

/-- **The old open edge is cut into the two new open edges and the new 0-cell.** -/
theorem realizeCell_edge_eq : R.cell d.edge = d.realizeCell R t d.newEdge₁ ∪
    d.realizeCell R t d.newVertex ∪ d.realizeCell R t d.newEdge₂ := by
  rw [R.cell_edge d.isLink, realizeCell_newEdge₁, realizeCell_newVertex, realizeCell_newEdge₂,
    ← edgeArc_newEdge₁, ← edgeArc_newEdge₂, ← edgeArc_new_union ht]
  ext p
  simp only [_root_.Set.mem_union, _root_.Set.mem_sdiff, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨hp | hp, hL, hR⟩
    · by_cases hM : p = R.drawing d.edge t
      · exact Or.inl (Or.inr hM)
      · exact Or.inl (Or.inl ⟨hp, hL, hM⟩)
    · by_cases hM : p = R.drawing d.edge t
      · exact Or.inl (Or.inr hM)
      · exact Or.inr ⟨hp, hM, hR⟩
  · rintro ((⟨hp, hL, hM⟩ | rfl) | ⟨hp, hM, hR⟩)
    · exact ⟨Or.inl hp, hL, fun h => posRight_notMem_edgeArc_newEdge₁ ht (h ▸ hp)⟩
    · exact ⟨Or.inl newPos_mem_edgeArc_newEdge₁, d.newPos_ne_pos R ht d.isLink.left_mem,
        d.newPos_ne_pos R ht d.isLink.right_mem⟩
    · exact ⟨Or.inr hp, fun h => posLeft_notMem_edgeArc_newEdge₂ ht (h ▸ hp), hR⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realizeCell_edge_eq then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realizeCell_edge_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realizeCell_edge_eq ``Submission.Schoenflies.CellStructure.SubdivData.realizeCell_edge_eq

theorem nonempty_realizeCell_newEdge₁ : (d.realizeCell R t d.newEdge₁).Nonempty := by
  rw [realizeCell_newEdge₁, ← edgeArc_newEdge₁]
  exact (isArcBetween_newEdge₁ ht).nonempty_diff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.nonempty_realizeCell_newEdge₁ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.nonempty_realizeCell_newEdge₁"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.nonempty_realizeCell_newEdge₁ ``Submission.Schoenflies.CellStructure.SubdivData.nonempty_realizeCell_newEdge₁

theorem nonempty_realizeCell_newEdge₂ : (d.realizeCell R t d.newEdge₂).Nonempty := by
  rw [realizeCell_newEdge₂, ← edgeArc_newEdge₂]
  exact (isArcBetween_newEdge₂ ht).nonempty_diff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.nonempty_realizeCell_newEdge₂ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.nonempty_realizeCell_newEdge₂"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.nonempty_realizeCell_newEdge₂ ``Submission.Schoenflies.CellStructure.SubdivData.nonempty_realizeCell_newEdge₂

omit ht in
theorem disjoint_newEdge₁_newVertex :
    Disjoint (d.realizeCell R t d.newEdge₁) (d.realizeCell R t d.newVertex) := by
  rw [realizeCell_newEdge₁, realizeCell_newVertex]
  exact disjoint_left.2 fun _ hp hq => hp.2 (Or.inr (mem_singleton_iff.1 hq))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.disjoint_newEdge₁_newVertex then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.disjoint_newEdge₁_newVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.disjoint_newEdge₁_newVertex ``Submission.Schoenflies.CellStructure.SubdivData.disjoint_newEdge₁_newVertex

omit ht in
theorem disjoint_newEdge₂_newVertex :
    Disjoint (d.realizeCell R t d.newEdge₂) (d.realizeCell R t d.newVertex) := by
  rw [realizeCell_newEdge₂, realizeCell_newVertex]
  exact disjoint_left.2 fun _ hp hq => hp.2 (Or.inl (mem_singleton_iff.1 hq))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.disjoint_newEdge₂_newVertex then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.disjoint_newEdge₂_newVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.disjoint_newEdge₂_newVertex ``Submission.Schoenflies.CellStructure.SubdivData.disjoint_newEdge₂_newVertex

theorem disjoint_newEdge₁_newEdge₂ :
    Disjoint (d.realizeCell R t d.newEdge₁) (d.realizeCell R t d.newEdge₂) := by
  refine disjoint_left.2 fun p hp hq => ?_
  rw [realizeCell_newEdge₁, ← edgeArc_newEdge₁] at hp
  rw [realizeCell_newEdge₂, ← edgeArc_newEdge₂] at hq
  have : p ∈ ({R.drawing d.edge t} : Set Plane) := by
    rw [← edgeArc_new_inter ht]; exact ⟨hp.1, hq.1⟩
  exact hp.2 (Or.inr (mem_singleton_iff.1 this))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.disjoint_newEdge₁_newEdge₂ then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.disjoint_newEdge₁_newEdge₂"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.disjoint_newEdge₁_newEdge₂ ``Submission.Schoenflies.CellStructure.SubdivData.disjoint_newEdge₁_newEdge₂

/-- **The subdivided realization refines the given one** — every field of
`SubdivData.IsRefinement`. With `IsRefinement.isCellDecomposition_and_isFaceJordan` this hands a
consumer `IsCellDecomposition`, `IsFaceJordan` and `Refines` at the new stage. -/
theorem isRefinement_realize : d.IsRefinement R (d.realize R t ht) where
  cell_eq := fun _ hc _ => realizeCell_of_mem_cells hc
  cell_edge := realizeCell_edge_eq ht
  nonempty := by
    rintro c (rfl | rfl | rfl)
    · rw [realize_cell, realizeCell_newVertex]
      exact ⟨R.drawing d.edge t, rfl⟩
    · exact nonempty_realizeCell_newEdge₁ ht
    · exact nonempty_realizeCell_newEdge₂ ht
  disjoint := by
    rintro c τ (rfl | rfl | rfl) (rfl | rfl | rfl) hne
    · exact absurd rfl hne
    · exact (disjoint_newEdge₁_newVertex (t := t)).symm
    · exact (disjoint_newEdge₂_newVertex (t := t)).symm
    · exact disjoint_newEdge₁_newVertex
    · exact absurd rfl hne
    · exact disjoint_newEdge₁_newEdge₂ ht
    · exact disjoint_newEdge₂_newVertex
    · exact (disjoint_newEdge₁_newEdge₂ ht).symm
    · exact absurd rfl hne
  closure_newVertex := by
    simp only [realize_cell]
    rw [realizeCell_newVertex, closure_singleton]
  closure_newEdge₁ := by
    simp only [realize_cell]
    rw [closure_realizeCell_newEdge₁ ht, realizeCell_newVertex,
      R.cell_vertex d.isLink.left_mem, realizeCell_newEdge₁, ← edgeArc_newEdge₁]
    exact (diff_pair_union_union posLeft_mem_edgeArc_newEdge₁ newPos_mem_edgeArc_newEdge₁).symm
  closure_newEdge₂ := by
    simp only [realize_cell]
    rw [closure_realizeCell_newEdge₂ ht, realizeCell_newVertex,
      R.cell_vertex d.isLink.right_mem, realizeCell_newEdge₂, ← edgeArc_newEdge₂,
      _root_.Set.pair_comm (R.drawing d.edge t) (R.pos d.right)]
    exact (diff_pair_union_union posRight_mem_edgeArc_newEdge₂ newPos_mem_edgeArc_newEdge₂).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.isRefinement_realize then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.isRefinement_realize"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.isRefinement_realize ``Submission.Schoenflies.CellStructure.SubdivData.isRefinement_realize

/-- **The whole induction step over the first constructor, constructed.** One edge subdivision of
a realization satisfying (i) and (vii) produces a realization satisfying (i) and (vii) and
refining it, constructing the refined realization in the conclusion. -/
theorem realize_isCellDecomposition_and_isFaceJordan (hS : S.CombInvariants) {D : Set Plane}
    (h : R.IsCellDecomposition D) (hJ : R.IsFaceJordan) :
    (d.realize R t ht).IsCellDecomposition D ∧ (d.realize R t ht).IsFaceJordan ∧
      (d.realize R t ht).Refines R d.parent :=
  (isRefinement_realize ht).isCellDecomposition_and_isFaceJordan hS h hJ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.realize_isCellDecomposition_and_isFaceJordan then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.realize_isCellDecomposition_and_isFaceJordan"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.realize_isCellDecomposition_and_isFaceJordan ``Submission.Schoenflies.CellStructure.SubdivData.realize_isCellDecomposition_and_isFaceJordan

/-! ### The subdivision does not move the skeleton

Cutting an edge in two adds a point that was already on the drawing and replaces one arc by two
whose union is that arc. So the realized 1-skeleton is literally the same set — which is what
lets a skeleton homeomorphism be transported across a subdivision without being rebuilt. -/

theorem pointSet_realize :
    pointSet (d.realizeGraph R t) (d.realizeDrawing R t) = pointSet R.graph R.drawing := by
  have hedge : (⋃ f ∈ E(R.graph), edgeArc R.drawing f) =
      edgeArc R.drawing d.edge ∪ ⋃ f ∈ E(S.skel) \ {d.edge}, edgeArc R.drawing f := by
    rw [← _root_.Set.biUnion_insert, _root_.Set.insert_sdiff_singleton,
      _root_.Set.insert_eq_of_mem (show d.edge ∈ E(S.skel) from d.edge_mem_edgeSet), Realization.edgeSet_graph]
  have hnew : (⋃ f ∈ E(d.realizeGraph R t), edgeArc (d.realizeDrawing R t) f) =
      edgeArc R.drawing d.edge ∪ ⋃ f ∈ E(S.skel) \ {d.edge}, edgeArc R.drawing f := by
    rw [realizeGraph_edgeSet, d.skeleton_edgeSet, _root_.Set.biUnion_insert, _root_.Set.biUnion_insert,
      _root_.Set.iUnion₂_congr (fun f (hf : f ∈ E(S.skel) \ {d.edge}) =>
        edgeArc_of_ne (d := d) (R := R) (t := t)
          (d.ne_newEdge₁_of_mem_cells (S.mem_cells_of_mem_edgeSet hf.1))
          (d.ne_newEdge₂_of_mem_cells (S.mem_cells_of_mem_edgeSet hf.1))),
      ← _root_.Set.union_assoc, edgeArc_new_union ht]
  have hM : R.drawing d.edge t ∈ edgeArc R.drawing d.edge := ⟨t, _root_.Set.Ioo_subset_Icc_self ht, rfl⟩
  rw [pointSet, pointSet, hnew, hedge, realizeGraph_vertexSet, _root_.Set.insert_union,
    _root_.Set.insert_eq_of_mem (_root_.Set.mem_union_right _ (_root_.Set.mem_union_left _ hM))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.pointSet_realize then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.pointSet_realize"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.pointSet_realize ``Submission.Schoenflies.CellStructure.SubdivData.pointSet_realize

/-- **An edge subdivision does not move the realized 1-skeleton.** -/
theorem skeletonSet_realize : (d.realize R t ht).skeletonSet = R.skeletonSet := pointSet_realize ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.CellStructure.SubdivData.skeletonSet_realize then
    throwError "Refusing to shadow existing declaration Schoenflies.CellStructure.SubdivData.skeletonSet_realize"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.CellStructure.SubdivData.skeletonSet_realize ``Submission.Schoenflies.CellStructure.SubdivData.skeletonSet_realize

end SubdivData

end CellStructure

end Schoenflies
