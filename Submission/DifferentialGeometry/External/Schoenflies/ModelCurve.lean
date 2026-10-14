/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
/-
Modified for this project; see MODIFICATIONS.md for the local changes.
-/
import Submission.DifferentialGeometry.External.Schoenflies.Concatenate
import Submission.DifferentialGeometry.External.Schoenflies.Polygonal
import Submission.DifferentialGeometry.External.Schoenflies.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# The model curve, and the parametrization of a Jordan curve by it

The blueprint's model curve is `S = ∂Q`, the boundary of the square `Q = [-1,1]²`, and *not*
the unit circle. That is a deliberate choice: this development is trigonometry-free, so a
traversal of the round circle by an interval is unavailable, whereas `S` is four segments
glued end to end and each segment is an arc by `isArcBetween_segment`. The blueprint says so
explicitly ("Nothing in this document needs the unit circle in place of `S`").

`modelCurve` is defined by the sup norm, `‖x‖∞ = 1`, which is the same square the rest of the
development already speaks about (`Plane.closedSquare 0 1`), and it is cut into its four sides
by `modelCurve_eq_sides`.

## The content of Lemma 3.1

The lemma has three clauses. Only the first is proved here; the other two are already on
`main`, transported along the homeomorphism the first clause supplies:

* *"`γ` induces a homeomorphism from `S` onto `C`"* — `isJordanCurve_modelCurve` together with
  `IsJordanCurve.homeomorph_modelCurve`. The general fact behind it is `IsLoop.exists_homeomorph`:
  a loop is a quotient map of `[0,1]` which identifies exactly `0` with `1`, so *any two* loops
  induce a homeomorphism between their images, matching parameter for parameter.
* *"two distinct points divide `C` into two simple arcs meeting exactly in those points"* — this
  is `IsJordanCurve.two_arcs` in `Schoenflies/TwoArcs.lean`, proved directly on the parameter
  interval, which is strictly stronger than transporting it from `S`.
* *"the relatively open subarcs form a basis of the subspace topology"* — `openArc_isRelOpen`,
  `openArc_subarc_isRelOpen` and `basic_piece_inside_ball` in `Schoenflies/Subarc.lean`.

The route to the homeomorphism is the blueprint's, with the sequence argument replaced by its
point-set content: `t ↦ γ t` is a continuous surjection from the compact `[0,1]` onto the
Hausdorff `C`, hence a closed map, hence a *quotient* map; so a map out of `C` is continuous as
soon as its composite with the parametrization is. That is exactly what the blueprint's
subsequence chase establishes, and it is one line here.

## Blueprint

* `modelCurve` — Lemma 3.1, the model curve `S = ∂Q` with `Q = [-1,1]²`.
* `modelCurve_eq_sides` — the decomposition of `S` into its four sides.
* `modelCurve_eq_frontier` — `S` is literally the topological boundary of `Q`.
* `isJordanCurve_modelCurve` — `S` is a Jordan curve.
* `IsLoop.param_eq_or`, `IsLoop.eq_of_eq` — a loop identifies exactly the two endpoints of the
  parameter interval.
* `IsLoop.exists_homeomorph` — two loops induce a homeomorphism of their images.
* `IsJordanCurve.homeomorph`, `IsJordanCurve.homeomorph_modelCurve`,
  `IsJordanCurve.modelCurve_homeomorph` — Lemma 3.1, first clause.
-/

open _root_.Set _root_.Topology _root_.unitInterval

namespace Schoenflies

/-! ### Segments with a constant coordinate

The four sides of the square are axis-parallel, so each is pinned by one coordinate and swept
by the other. Two lemmas serve all four. -/

/-- A horizontal segment: constant second coordinate, first coordinate sweeping a real
segment. -/
theorem mem_segment_horiz {u v c : ℝ} {x : Plane} :
    x ∈ segment ℝ (Plane.mk u c) (Plane.mk v c) ↔ x 1 = c ∧ x 0 ∈ segment ℝ u v := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq, rfl⟩
    refine ⟨?_, p, q, hp, hq, hpq, ?_⟩
    · rw [Plane.smul_add_apply, Plane.mk_one, Plane.mk_one]
      linear_combination c * hpq
    · rw [Plane.smul_add_apply, Plane.mk_zero, Plane.mk_zero]
      simp [smul_eq_mul]
  · rintro ⟨hx1, p, q, hp, hq, hpq, hx0⟩
    refine ⟨p, q, hp, hq, hpq, ?_⟩
    ext i
    fin_cases i
    · change (p • Plane.mk u c + q • Plane.mk v c) 0 = x 0
      rw [Plane.smul_add_apply, Plane.mk_zero, Plane.mk_zero, ← hx0]
      simp [smul_eq_mul]
    · change (p • Plane.mk u c + q • Plane.mk v c) 1 = x 1
      rw [Plane.smul_add_apply, Plane.mk_one, Plane.mk_one, hx1]
      linear_combination c * hpq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.mem_segment_horiz then
    throwError "Refusing to shadow existing declaration Schoenflies.mem_segment_horiz"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.mem_segment_horiz ``Submission.Schoenflies.mem_segment_horiz

/-- A vertical segment: constant first coordinate, second coordinate sweeping a real
segment. -/
theorem mem_segment_vert {c u v : ℝ} {x : Plane} :
    x ∈ segment ℝ (Plane.mk c u) (Plane.mk c v) ↔ x 0 = c ∧ x 1 ∈ segment ℝ u v := by
  constructor
  · rintro ⟨p, q, hp, hq, hpq, rfl⟩
    refine ⟨?_, p, q, hp, hq, hpq, ?_⟩
    · rw [Plane.smul_add_apply, Plane.mk_zero, Plane.mk_zero]
      linear_combination c * hpq
    · rw [Plane.smul_add_apply, Plane.mk_one, Plane.mk_one]
      simp [smul_eq_mul]
  · rintro ⟨hx0, p, q, hp, hq, hpq, hx1⟩
    refine ⟨p, q, hp, hq, hpq, ?_⟩
    ext i
    fin_cases i
    · change (p • Plane.mk c u + q • Plane.mk c v) 0 = x 0
      rw [Plane.smul_add_apply, Plane.mk_zero, Plane.mk_zero, hx0]
      linear_combination c * hpq
    · change (p • Plane.mk c u + q • Plane.mk c v) 1 = x 1
      rw [Plane.smul_add_apply, Plane.mk_one, Plane.mk_one, ← hx1]
      simp [smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.mem_segment_vert then
    throwError "Refusing to shadow existing declaration Schoenflies.mem_segment_vert"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.mem_segment_vert ``Submission.Schoenflies.mem_segment_vert

theorem segment_one_neg_one : segment ℝ (1 : ℝ) (-1) = _root_.Set.Icc (-1) 1 := by
  rw [segment_symm]
  exact segment_eq_Icc (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.segment_one_neg_one then
    throwError "Refusing to shadow existing declaration Schoenflies.segment_one_neg_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.segment_one_neg_one ``Submission.Schoenflies.segment_one_neg_one

theorem segment_neg_one_one : segment ℝ (-1 : ℝ) 1 = _root_.Set.Icc (-1) 1 :=
  segment_eq_Icc (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.segment_neg_one_one then
    throwError "Refusing to shadow existing declaration Schoenflies.segment_neg_one_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.segment_neg_one_one ``Submission.Schoenflies.segment_neg_one_one

/-! ### The model curve and its four sides -/

/-- The model curve `S = ∂Q`, the boundary of the square `Q = [-1,1]²`, described by the sup
norm. -/
def modelCurve : Set Plane := {x : Plane | Plane.supNorm x = 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.modelCurve then
    throwError "Refusing to shadow existing declaration Schoenflies.modelCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.modelCurve ``Submission.Schoenflies.modelCurve

/-- The corner `(1, 1)`. -/
def cornerNE : Plane := Plane.mk 1 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.cornerNE then
    throwError "Refusing to shadow existing declaration Schoenflies.cornerNE"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.cornerNE ``Submission.Schoenflies.cornerNE

/-- The corner `(-1, 1)`. -/
def cornerNW : Plane := Plane.mk (-1) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.cornerNW then
    throwError "Refusing to shadow existing declaration Schoenflies.cornerNW"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.cornerNW ``Submission.Schoenflies.cornerNW

/-- The corner `(-1, -1)`. -/
def cornerSW : Plane := Plane.mk (-1) (-1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.cornerSW then
    throwError "Refusing to shadow existing declaration Schoenflies.cornerSW"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.cornerSW ``Submission.Schoenflies.cornerSW

/-- The corner `(1, -1)`. -/
def cornerSE : Plane := Plane.mk 1 (-1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.cornerSE then
    throwError "Refusing to shadow existing declaration Schoenflies.cornerSE"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.cornerSE ``Submission.Schoenflies.cornerSE

/-- The top side of the square, traversed from `(1,1)` to `(-1,1)`. -/
def sideTop : Set Plane := segment ℝ cornerNE cornerNW

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.sideTop then
    throwError "Refusing to shadow existing declaration Schoenflies.sideTop"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.sideTop ``Submission.Schoenflies.sideTop

/-- The left side of the square, traversed from `(-1,1)` to `(-1,-1)`. -/
def sideLeft : Set Plane := segment ℝ cornerNW cornerSW

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.sideLeft then
    throwError "Refusing to shadow existing declaration Schoenflies.sideLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.sideLeft ``Submission.Schoenflies.sideLeft

/-- The bottom side of the square, traversed from `(-1,-1)` to `(1,-1)`. -/
def sideBottom : Set Plane := segment ℝ cornerSW cornerSE

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.sideBottom then
    throwError "Refusing to shadow existing declaration Schoenflies.sideBottom"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.sideBottom ``Submission.Schoenflies.sideBottom

/-- The right side of the square, traversed from `(1,-1)` to `(1,1)`. -/
def sideRight : Set Plane := segment ℝ cornerSE cornerNE

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.sideRight then
    throwError "Refusing to shadow existing declaration Schoenflies.sideRight"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.sideRight ``Submission.Schoenflies.sideRight

theorem mem_sideTop {x : Plane} : x ∈ sideTop ↔ x 1 = 1 ∧ |x 0| ≤ 1 := by
  rw [sideTop, cornerNE, cornerNW, mem_segment_horiz, segment_one_neg_one]
  simp [abs_le, and_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.mem_sideTop then
    throwError "Refusing to shadow existing declaration Schoenflies.mem_sideTop"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.mem_sideTop ``Submission.Schoenflies.mem_sideTop

theorem mem_sideLeft {x : Plane} : x ∈ sideLeft ↔ x 0 = -1 ∧ |x 1| ≤ 1 := by
  rw [sideLeft, cornerNW, cornerSW, mem_segment_vert, segment_one_neg_one]
  simp [abs_le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.mem_sideLeft then
    throwError "Refusing to shadow existing declaration Schoenflies.mem_sideLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.mem_sideLeft ``Submission.Schoenflies.mem_sideLeft

theorem mem_sideBottom {x : Plane} : x ∈ sideBottom ↔ x 1 = -1 ∧ |x 0| ≤ 1 := by
  rw [sideBottom, cornerSW, cornerSE, mem_segment_horiz, segment_neg_one_one]
  simp [abs_le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.mem_sideBottom then
    throwError "Refusing to shadow existing declaration Schoenflies.mem_sideBottom"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.mem_sideBottom ``Submission.Schoenflies.mem_sideBottom

theorem mem_sideRight {x : Plane} : x ∈ sideRight ↔ x 0 = 1 ∧ |x 1| ≤ 1 := by
  rw [sideRight, cornerSE, cornerNE, mem_segment_vert, segment_neg_one_one]
  simp [abs_le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.mem_sideRight then
    throwError "Refusing to shadow existing declaration Schoenflies.mem_sideRight"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.mem_sideRight ``Submission.Schoenflies.mem_sideRight

/-- The model curve is the union of the four sides. The sup norm reaches `1` exactly when one
coordinate is `±1` and the other is dominated by it. -/
theorem modelCurve_eq_sides :
    modelCurve = (sideTop ∪ sideLeft) ∪ (sideBottom ∪ sideRight) := by
  ext x
  simp only [modelCurve, _root_.Set.mem_ofPred_eq, _root_.Set.mem_union, mem_sideTop, mem_sideLeft, mem_sideBottom,
    mem_sideRight, Plane.supNorm]
  constructor
  · intro h
    have h0 : |x 0| ≤ 1 := h ▸ le_max_left _ _
    have h1 : |x 1| ≤ 1 := h ▸ le_max_right _ _
    rcases max_choice |x 0| |x 1| with hm | hm
    · -- the first coordinate attains the maximum, so it is `±1`
      have hx : |x 0| = 1 := hm ▸ h
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hx with h' | h'
      · exact Or.inr (Or.inr ⟨h', h1⟩)
      · exact Or.inl (Or.inr ⟨h', h1⟩)
    · have hx : |x 1| = 1 := hm ▸ h
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hx with h' | h'
      · exact Or.inl (Or.inl ⟨h', h0⟩)
      · exact Or.inr (Or.inl ⟨h', h0⟩)
  · rintro ((⟨h1, h0⟩ | ⟨h0, h1⟩) | (⟨h1, h0⟩ | ⟨h0, h1⟩))
    · rw [show |x 1| = 1 by rw [h1]; norm_num]
      exact max_eq_right h0
    · rw [show |x 0| = 1 by rw [h0]; norm_num]
      exact max_eq_left h1
    · rw [show |x 1| = 1 by rw [h1]; norm_num]
      exact max_eq_right h0
    · rw [show |x 0| = 1 by rw [h0]; norm_num]
      exact max_eq_left h1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.modelCurve_eq_sides then
    throwError "Refusing to shadow existing declaration Schoenflies.modelCurve_eq_sides"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.modelCurve_eq_sides ``Submission.Schoenflies.modelCurve_eq_sides

/-! ### The model curve is a Jordan curve -/

theorem cornerNE_ne_cornerNW : cornerNE ≠ cornerNW := by
  intro h
  have := congrArg (fun p : Plane => p 0) h
  norm_num [cornerNE, cornerNW] at this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.cornerNE_ne_cornerNW then
    throwError "Refusing to shadow existing declaration Schoenflies.cornerNE_ne_cornerNW"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.cornerNE_ne_cornerNW ``Submission.Schoenflies.cornerNE_ne_cornerNW

theorem cornerNW_ne_cornerSW : cornerNW ≠ cornerSW := by
  intro h
  have := congrArg (fun p : Plane => p 1) h
  norm_num [cornerNW, cornerSW] at this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.cornerNW_ne_cornerSW then
    throwError "Refusing to shadow existing declaration Schoenflies.cornerNW_ne_cornerSW"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.cornerNW_ne_cornerSW ``Submission.Schoenflies.cornerNW_ne_cornerSW

theorem cornerSW_ne_cornerSE : cornerSW ≠ cornerSE := by
  intro h
  have := congrArg (fun p : Plane => p 0) h
  norm_num [cornerSW, cornerSE] at this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.cornerSW_ne_cornerSE then
    throwError "Refusing to shadow existing declaration Schoenflies.cornerSW_ne_cornerSE"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.cornerSW_ne_cornerSE ``Submission.Schoenflies.cornerSW_ne_cornerSE

theorem cornerSE_ne_cornerNE : cornerSE ≠ cornerNE := by
  intro h
  have := congrArg (fun p : Plane => p 1) h
  norm_num [cornerSE, cornerNE] at this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.cornerSE_ne_cornerNE then
    throwError "Refusing to shadow existing declaration Schoenflies.cornerSE_ne_cornerNE"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.cornerSE_ne_cornerNE ``Submission.Schoenflies.cornerSE_ne_cornerNE

theorem isArcBetween_sideTop : IsArcBetween sideTop cornerNE cornerNW :=
  isArcBetween_segment cornerNE_ne_cornerNW

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.isArcBetween_sideTop then
    throwError "Refusing to shadow existing declaration Schoenflies.isArcBetween_sideTop"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.isArcBetween_sideTop ``Submission.Schoenflies.isArcBetween_sideTop

theorem isArcBetween_sideLeft : IsArcBetween sideLeft cornerNW cornerSW :=
  isArcBetween_segment cornerNW_ne_cornerSW

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.isArcBetween_sideLeft then
    throwError "Refusing to shadow existing declaration Schoenflies.isArcBetween_sideLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.isArcBetween_sideLeft ``Submission.Schoenflies.isArcBetween_sideLeft

theorem isArcBetween_sideBottom : IsArcBetween sideBottom cornerSW cornerSE :=
  isArcBetween_segment cornerSW_ne_cornerSE

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.isArcBetween_sideBottom then
    throwError "Refusing to shadow existing declaration Schoenflies.isArcBetween_sideBottom"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.isArcBetween_sideBottom ``Submission.Schoenflies.isArcBetween_sideBottom

theorem isArcBetween_sideRight : IsArcBetween sideRight cornerSE cornerNE :=
  isArcBetween_segment cornerSE_ne_cornerNE

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.isArcBetween_sideRight then
    throwError "Refusing to shadow existing declaration Schoenflies.isArcBetween_sideRight"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.isArcBetween_sideRight ``Submission.Schoenflies.isArcBetween_sideRight

/-- Consecutive sides meet only in the corner they share. -/
theorem sideTop_meet_sideLeft : ∀ z ∈ sideTop, z ∈ sideLeft → z = cornerNW := by
  intro z hz hz'
  rw [mem_sideTop] at hz
  rw [mem_sideLeft] at hz'
  ext i
  fin_cases i
  · simpa [cornerNW] using hz'.1
  · simpa [cornerNW] using hz.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.sideTop_meet_sideLeft then
    throwError "Refusing to shadow existing declaration Schoenflies.sideTop_meet_sideLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.sideTop_meet_sideLeft ``Submission.Schoenflies.sideTop_meet_sideLeft

theorem sideBottom_meet_sideRight : ∀ z ∈ sideBottom, z ∈ sideRight → z = cornerSE := by
  intro z hz hz'
  rw [mem_sideBottom] at hz
  rw [mem_sideRight] at hz'
  ext i
  fin_cases i
  · simpa [cornerSE] using hz'.1
  · simpa [cornerSE] using hz.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.sideBottom_meet_sideRight then
    throwError "Refusing to shadow existing declaration Schoenflies.sideBottom_meet_sideRight"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.sideBottom_meet_sideRight ``Submission.Schoenflies.sideBottom_meet_sideRight

/-- The upper half of the model curve: two sides from `(1,1)` to `(-1,-1)`. -/
theorem isArcBetween_upperSides : IsArcBetween (sideTop ∪ sideLeft) cornerNE cornerSW :=
  isArcBetween_sideTop.concatenate isArcBetween_sideLeft sideTop_meet_sideLeft

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.isArcBetween_upperSides then
    throwError "Refusing to shadow existing declaration Schoenflies.isArcBetween_upperSides"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.isArcBetween_upperSides ``Submission.Schoenflies.isArcBetween_upperSides

/-- The lower half of the model curve: two sides back from `(-1,-1)` to `(1,1)`. -/
theorem isArcBetween_lowerSides : IsArcBetween (sideBottom ∪ sideRight) cornerSW cornerNE :=
  isArcBetween_sideBottom.concatenate isArcBetween_sideRight sideBottom_meet_sideRight

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.isArcBetween_lowerSides then
    throwError "Refusing to shadow existing declaration Schoenflies.isArcBetween_lowerSides"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.isArcBetween_lowerSides ``Submission.Schoenflies.isArcBetween_lowerSides

/-- The two halves of the model curve meet exactly in the two corners they share: opposite
sides are pinned to opposite values of one coordinate, so they are disjoint. -/
theorem upperSides_meet_lowerSides :
    ∀ z ∈ sideTop ∪ sideLeft, z ∈ sideBottom ∪ sideRight → z = cornerNE ∨ z = cornerSW := by
  rintro z (hz | hz) (hz' | hz')
  · -- top and bottom: `z 1 = 1` and `z 1 = -1`
    rw [mem_sideTop] at hz
    rw [mem_sideBottom] at hz'
    rw [hz.1] at hz'
    norm_num at hz'
  · -- top and right: the corner `(1,1)`
    rw [mem_sideTop] at hz
    rw [mem_sideRight] at hz'
    refine Or.inl ?_
    ext i
    fin_cases i
    · simpa [cornerNE] using hz'.1
    · simpa [cornerNE] using hz.1
  · -- left and bottom: the corner `(-1,-1)`
    rw [mem_sideLeft] at hz
    rw [mem_sideBottom] at hz'
    refine Or.inr ?_
    ext i
    fin_cases i
    · simpa [cornerSW] using hz.1
    · simpa [cornerSW] using hz'.1
  · -- left and right: `z 0 = -1` and `z 0 = 1`
    rw [mem_sideLeft] at hz
    rw [mem_sideRight] at hz'
    rw [hz.1] at hz'
    norm_num at hz'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.upperSides_meet_lowerSides then
    throwError "Refusing to shadow existing declaration Schoenflies.upperSides_meet_lowerSides"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.upperSides_meet_lowerSides ``Submission.Schoenflies.upperSides_meet_lowerSides

/-- **The model curve is a Jordan curve.** Four segments glued end to end; no trigonometry
anywhere. -/
theorem isJordanCurve_modelCurve : IsJordanCurve modelCurve := by
  rw [modelCurve_eq_sides]
  exact IsJordanCurve.of_two_arcs isArcBetween_upperSides isArcBetween_lowerSides
    upperSides_meet_lowerSides

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.isJordanCurve_modelCurve then
    throwError "Refusing to shadow existing declaration Schoenflies.isJordanCurve_modelCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.isJordanCurve_modelCurve ``Submission.Schoenflies.isJordanCurve_modelCurve

theorem isCompact_modelCurve : IsCompact modelCurve :=
  isJordanCurve_modelCurve.isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.isCompact_modelCurve then
    throwError "Refusing to shadow existing declaration Schoenflies.isCompact_modelCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.isCompact_modelCurve ``Submission.Schoenflies.isCompact_modelCurve

theorem cornerNE_mem_modelCurve : cornerNE ∈ modelCurve := by
  rw [modelCurve_eq_sides]
  exact Or.inl isArcBetween_upperSides.left_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.cornerNE_mem_modelCurve then
    throwError "Refusing to shadow existing declaration Schoenflies.cornerNE_mem_modelCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.cornerNE_mem_modelCurve ``Submission.Schoenflies.cornerNE_mem_modelCurve

/-! ### The model curve is the boundary of the square

This is the blueprint's description `S = ∂Q` with `Q = [-1,1]²`, and the check that the sup-norm
definition above is the intended one. The only content is that a point of sup norm exactly `1`
is *not* interior to the square: scaling it out by a factor `1 + δ` leaves the square while
moving an arbitrarily small distance. -/

theorem smul_coord (a : ℝ) (x : Plane) (i : Fin 2) : (a • x) i = a * x i := by simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.smul_coord then
    throwError "Refusing to shadow existing declaration Schoenflies.smul_coord"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.smul_coord ``Submission.Schoenflies.smul_coord

theorem mem_closedSquare_zero_one {x : Plane} :
    x ∈ Plane.closedSquare 0 1 ↔ Plane.supNorm x ≤ 1 := by
  simp [Plane.closedSquare]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.mem_closedSquare_zero_one then
    throwError "Refusing to shadow existing declaration Schoenflies.mem_closedSquare_zero_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.mem_closedSquare_zero_one ``Submission.Schoenflies.mem_closedSquare_zero_one

theorem mem_openSquare_zero_one {x : Plane} :
    x ∈ Plane.openSquare 0 1 ↔ Plane.supNorm x < 1 := by
  simp [Plane.openSquare]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.mem_openSquare_zero_one then
    throwError "Refusing to shadow existing declaration Schoenflies.mem_openSquare_zero_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.mem_openSquare_zero_one ``Submission.Schoenflies.mem_openSquare_zero_one

theorem modelCurve_subset_closedSquare : modelCurve ⊆ Plane.closedSquare 0 1 :=
  fun _ hx => mem_closedSquare_zero_one.mpr (le_of_eq hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.modelCurve_subset_closedSquare then
    throwError "Refusing to shadow existing declaration Schoenflies.modelCurve_subset_closedSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.modelCurve_subset_closedSquare ``Submission.Schoenflies.modelCurve_subset_closedSquare

/-- A point of the model curve is not interior to the square: pushing it radially outwards by
a factor `1 + δ` leaves the square, and `δ` may be taken as small as one likes. -/
theorem notMem_interior_closedSquare {x : Plane} (hx : Plane.supNorm x = 1) :
    x ∉ interior (Plane.closedSquare 0 1) := by
  intro hmem
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hmem
  obtain ⟨ε, hε, hball⟩ := hmem
  have hx' : _root_.Max.max |x 0| |x 1| = 1 := hx
  have hx0 : x ≠ 0 := by
    intro h
    rw [h] at hx
    simp [Plane.supNorm] at hx
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set δ : ℝ := ε / (2 * ‖x‖) with hδdef
  have hδ : 0 < δ := div_pos hε (by linarith)
  -- the pushed-out point is within `ε/2` of `x`
  have hdist : _root_.Dist.dist ((1 + δ) • x) x < ε := by
    have hsub : (1 + δ) • x - x = δ • x := by module
    have hmul : δ * ‖x‖ = ε / 2 := by
      rw [hδdef]; field_simp
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδ, hmul]
    linarith
  have hin : Plane.supNorm ((1 + δ) • x) ≤ 1 :=
    mem_closedSquare_zero_one.mp (hball (Metric.mem_ball.mpr hdist))
  -- but the coordinate that attained the sup norm has grown past `1`
  have hgrown : 1 + δ ≤ Plane.supNorm ((1 + δ) • x) := by
    rcases max_choice |x 0| |x 1| with hm | hm
    · have h0 : |x 0| = 1 := by rw [← hm]; exact hx'
      calc 1 + δ = |(1 + δ) * x 0| := by
            rw [abs_mul, h0, abs_of_pos (by linarith), mul_one]
        _ = |((1 + δ) • x) 0| := by rw [smul_coord]
        _ ≤ Plane.supNorm ((1 + δ) • x) := Plane.abs_zero_le_supNorm _
    · have h1 : |x 1| = 1 := by rw [← hm]; exact hx'
      calc 1 + δ = |(1 + δ) * x 1| := by
            rw [abs_mul, h1, abs_of_pos (by linarith), mul_one]
        _ = |((1 + δ) • x) 1| := by rw [smul_coord]
        _ ≤ Plane.supNorm ((1 + δ) • x) := Plane.abs_one_le_supNorm _
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.notMem_interior_closedSquare then
    throwError "Refusing to shadow existing declaration Schoenflies.notMem_interior_closedSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.notMem_interior_closedSquare ``Submission.Schoenflies.notMem_interior_closedSquare

theorem interior_closedSquare_zero_one :
    interior (Plane.closedSquare 0 1) = Plane.openSquare 0 1 := by
  refine subset_antisymm (fun x hx => ?_) ?_
  · rw [mem_openSquare_zero_one]
    rcases lt_or_eq_of_le (mem_closedSquare_zero_one.mp (interior_subset hx)) with h | h
    · exact h
    · exact absurd hx (notMem_interior_closedSquare h)
  · exact (Plane.isOpen_openSquare 0 1).subset_interior_iff.mpr fun x hx =>
      mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hx).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.interior_closedSquare_zero_one then
    throwError "Refusing to shadow existing declaration Schoenflies.interior_closedSquare_zero_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.interior_closedSquare_zero_one ``Submission.Schoenflies.interior_closedSquare_zero_one

/-- **The model curve is `∂Q`**, the topological boundary of the closed square `Q = [-1,1]²`. -/
theorem modelCurve_eq_frontier : modelCurve = frontier (Plane.closedSquare 0 1) := by
  rw [(Plane.isClosed_closedSquare 0 1).frontier_eq, interior_closedSquare_zero_one]
  ext x
  simp only [modelCurve, _root_.Set.mem_ofPred_eq, _root_.Set.mem_sdiff, mem_closedSquare_zero_one,
    mem_openSquare_zero_one, not_lt]
  exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.modelCurve_eq_frontier then
    throwError "Refusing to shadow existing declaration Schoenflies.modelCurve_eq_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.modelCurve_eq_frontier ``Submission.Schoenflies.modelCurve_eq_frontier

/-! ### A loop identifies exactly the ends of the parameter interval -/

namespace IsLoop

variable {f g : ℝ → Plane}

/-- Two parameters of `[0,1]` with the same image under a loop are equal, or are the two ends
of the interval. This is the whole of a loop's non-injectivity. -/
theorem param_eq_or (hf : IsLoop f) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (h : f s = f t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  by_cases hs1 : s = 1 <;> by_cases ht1 : t = 1
  · exact Or.inl (hs1.trans ht1.symm)
  · -- `s` is the finish, so the value is also taken at the start, and `t` is the start
    subst hs1
    have h0 : (0 : ℝ) = t :=
      hf.injOn ⟨le_rfl, zero_lt_one⟩ ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩ (hf.closes.trans h)
    exact Or.inr (Or.inr ⟨rfl, h0.symm⟩)
  · subst ht1
    have h0 : s = 0 :=
      hf.injOn ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩ ⟨le_rfl, zero_lt_one⟩ (h.trans hf.closes.symm)
    exact Or.inr (Or.inl ⟨h0, rfl⟩)
  · exact Or.inl
      (hf.injOn ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩ ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩ h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.param_eq_or then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.param_eq_or"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.param_eq_or ``Submission.Schoenflies.IsLoop.param_eq_or

/-- Every loop makes the *same* identifications on `[0,1]`. This is what lets a loop be
transported to any other loop: the induced map on images is well defined. -/
theorem eq_of_eq (hf : IsLoop f) (hg : IsLoop g) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I)
    (h : f s = f t) : g s = g t := by
  rcases hf.param_eq_or hs ht h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact hg.closes
  · exact hg.closes.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.eq_of_eq then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.eq_of_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.eq_of_eq ``Submission.Schoenflies.IsLoop.eq_of_eq

/-- **Any two loops induce a homeomorphism between their images, matching parameters.**

`t ↦ f t` is a continuous surjection of the compact `[0,1]` onto the Hausdorff image, hence a
closed map, hence a quotient map; so a map out of the image is continuous as soon as its
composite with the parametrization is. The induced map is well defined by `eq_of_eq`, and
bijective because `eq_of_eq` runs in both directions. -/
theorem exists_homeomorph (hf : IsLoop f) (hg : IsLoop g) :
    ∃ h : ↥(f '' I) ≃ₜ ↥(g '' I),
      ∀ (t : ℝ) (ht : t ∈ I), (h ⟨f t, _root_.Set.mem_image_of_mem f ht⟩ : Plane) = g t := by
  classical
  have : CompactSpace ↥I := isCompact_iff_compactSpace.mp isCompact_I
  have : CompactSpace ↥(f '' I) :=
    isCompact_iff_compactSpace.mp (isCompact_I.image_of_continuousOn hf.continuousOn)
  -- the two parametrizations, read as maps of subtypes
  set q : ↥I → ↥(f '' I) := fun t => ⟨f t, _root_.Set.mem_image_of_mem f t.2⟩ with hq
  set q' : ↥I → ↥(g '' I) := fun t => ⟨g t, _root_.Set.mem_image_of_mem g t.2⟩ with hq'
  have hqc : Continuous q := (hf.continuousOn.domRestrict).subtype_mk _
  have hq'c : Continuous q' := (hg.continuousOn.domRestrict).subtype_mk _
  have hqs : Function.Surjective q := by
    rintro ⟨z, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  have hq's : Function.Surjective q' := by
    rintro ⟨z, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  have hquot : _root_.Topology.IsQuotientMap q := (hqc.isClosedMap).isQuotientMap hqc hqs
  -- the induced map, defined by picking a parameter and reading off the other loop
  set F : ↥(f '' I) → ↥(g '' I) := fun a => q' (Classical.choose (hqs a)) with hF
  have hFq : ∀ t : ↥I, F (q t) = q' t := by
    intro t
    have hchoice := Classical.choose_spec (hqs (q t))
    exact Subtype.ext
      (hf.eq_of_eq hg (Classical.choose (hqs (q t))).2 t.2 (congrArg Subtype.val hchoice))
  have hFc : Continuous F := by
    refine hquot.continuous_iff.mpr ?_
    have : F ∘ q = q' := funext hFq
    rw [this]
    exact hq'c
  have hFinj : Function.Injective F := by
    intro a b hab
    obtain ⟨s, rfl⟩ := hqs a
    obtain ⟨t, rfl⟩ := hqs b
    rw [hFq, hFq] at hab
    exact Subtype.ext (hg.eq_of_eq hf s.2 t.2 (congrArg Subtype.val hab))
  have hFsurj : Function.Surjective F := by
    intro b
    obtain ⟨t, rfl⟩ := hq's b
    exact ⟨q t, hFq t⟩
  refine ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hFinj, hFsurj⟩) hFc,
    fun t ht => ?_⟩
  exact congrArg Subtype.val (hFq ⟨t, ht⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsLoop.exists_homeomorph then
    throwError "Refusing to shadow existing declaration Schoenflies.IsLoop.exists_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsLoop.exists_homeomorph ``Submission.Schoenflies.IsLoop.exists_homeomorph

end IsLoop

/-! ### Lemma 3.1: parametrization by the model curve -/

namespace IsJordanCurve

/-- **Any two Jordan curves are homeomorphic.** -/
theorem homeomorph {C D : Set Plane} (hC : IsJordanCurve C) (hD : IsJordanCurve D) :
    Nonempty (↥C ≃ₜ ↥D) := by
  obtain ⟨f, hf, rfl⟩ := hC
  obtain ⟨g, hg, rfl⟩ := hD
  obtain ⟨h, -⟩ := hf.exists_homeomorph hg
  exact ⟨h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsJordanCurve.homeomorph then
    throwError "Refusing to shadow existing declaration Schoenflies.IsJordanCurve.homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsJordanCurve.homeomorph ``Submission.Schoenflies.IsJordanCurve.homeomorph

/-- **Lemma 3.1.** A Jordan curve is homeomorphic to the model curve `S = ∂Q`. -/
theorem homeomorph_modelCurve {C : Set Plane} (hC : IsJordanCurve C) :
    Nonempty (↥C ≃ₜ ↥modelCurve) :=
  hC.homeomorph isJordanCurve_modelCurve

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsJordanCurve.homeomorph_modelCurve then
    throwError "Refusing to shadow existing declaration Schoenflies.IsJordanCurve.homeomorph_modelCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsJordanCurve.homeomorph_modelCurve ``Submission.Schoenflies.IsJordanCurve.homeomorph_modelCurve

/-- **Lemma 3.1**, the other direction: the model curve maps homeomorphically onto any Jordan
curve. This is the form the blueprint states — `γ` induces a homeomorphism from `S` onto
`C`. -/
theorem modelCurve_homeomorph {C : Set Plane} (hC : IsJordanCurve C) :
    Nonempty (↥modelCurve ≃ₜ ↥C) :=
  isJordanCurve_modelCurve.homeomorph hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.IsJordanCurve.modelCurve_homeomorph then
    throwError "Refusing to shadow existing declaration Schoenflies.IsJordanCurve.modelCurve_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.IsJordanCurve.modelCurve_homeomorph ``Submission.Schoenflies.IsJordanCurve.modelCurve_homeomorph

end IsJordanCurve

end Schoenflies
