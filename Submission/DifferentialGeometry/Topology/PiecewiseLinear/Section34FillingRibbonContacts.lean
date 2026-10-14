import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingNeighborhoodQuadrants
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalCancellation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem horizontal_spoke (a : Bool) {p : ℝ × ℝ} :
    p ∈ segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf (if a then 0 else 2)) ↔
      p.1 ∈ (if a then _root_.Set.Icc (0 : ℝ) 1 else _root_.Set.Icc (-1 : ℝ) 0) ∧ p.2 = 0 := by
  cases a
  · simp only [Bool.false_eq_true, ↓reduceIte, mem_segment_zero_prod_iff]
    constructor
    · rintro ⟨t, ht₀, ht₁, hx, hy⟩
      norm_num [fourSpokeModelLeaf] at hx hy
      exact ⟨⟨by linarith, by linarith⟩, hy⟩
    · rintro ⟨⟨hx₀, hx₁⟩, hy⟩
      exact ⟨-p.1, by linarith, by linarith, by simp [fourSpokeModelLeaf],
        by simpa [fourSpokeModelLeaf] using hy⟩
  · simp only [↓reduceIte, mem_segment_zero_prod_iff]
    constructor
    · rintro ⟨t, ht₀, ht₁, hx, hy⟩
      norm_num [fourSpokeModelLeaf] at hx hy
      exact ⟨⟨by linarith, by linarith⟩, hy⟩
    · rintro ⟨⟨hx₀, hx₁⟩, hy⟩
      exact ⟨p.1, hx₀, hx₁, by simp [fourSpokeModelLeaf],
        by simpa [fourSpokeModelLeaf] using hy⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.horizontal_spoke
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.horizontal_spoke target :: scope.openDecls } }

private theorem vertical_spoke (b : Bool) {p : ℝ × ℝ} :
    p ∈ segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf (if b then 1 else 3)) ↔
      p.1 = 0 ∧ p.2 ∈ (if b then _root_.Set.Icc (0 : ℝ) 1 else _root_.Set.Icc (-1 : ℝ) 0) := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, mem_segment_zero_prod_iff]
    constructor
    · rintro ⟨t, ht₀, ht₁, hx, hy⟩
      norm_num [fourSpokeModelLeaf] at hx hy
      exact ⟨hx, by constructor <;> linarith⟩
    · rintro ⟨hx, hy₀, hy₁⟩
      exact ⟨-p.2, by linarith, by linarith,
        by simpa [fourSpokeModelLeaf] using hx, by simp [fourSpokeModelLeaf]⟩
  · simp only [↓reduceIte, mem_segment_zero_prod_iff]
    constructor
    · rintro ⟨t, ht₀, ht₁, hx, hy⟩
      norm_num [fourSpokeModelLeaf] at hx hy
      exact ⟨hx, by constructor <;> linarith⟩
    · rintro ⟨hx, hy₀, hy₁⟩
      exact ⟨p.2, hy₀, hy₁,
        by simpa [fourSpokeModelLeaf] using hx, by simp [fourSpokeModelLeaf]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.vertical_spoke
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.vertical_spoke target :: scope.openDecls } }

private theorem quadrant_inter_horizontal (a b : Bool) :
    section34CrossingQuadrant a b ∩
      (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 0) ∪
        segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 2)) =
      segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf (if a then 0 else 2)) := by
  ext p
  change (p ∈ section34CrossingQuadrant a b ∧
    (p ∈ segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf (if _root_.Bool.true then 0 else 2)) ∨
      p ∈ segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf (if _root_.Bool.false then 0 else 2)))) ↔ _
  rw [horizontal_spoke, horizontal_spoke, horizontal_spoke]
  cases a <;> cases b <;>
    simp only [section34CrossingQuadrant, Bool.false_eq_true, ↓reduceIte, _root_.Set.mem_prod, _root_.Set.mem_Icc] <;>
    constructor <;> intro h
  all_goals aesop

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.quadrant_inter_horizontal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.quadrant_inter_horizontal target :: scope.openDecls } }

private theorem quadrant_inter_vertical (a b : Bool) :
    section34CrossingQuadrant a b ∩
      (segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 1) ∪
        segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf 3)) =
      segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf (if b then 1 else 3)) := by
  ext p
  change (p ∈ section34CrossingQuadrant a b ∧
    (p ∈ segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf (if _root_.Bool.true then 1 else 3)) ∨
      p ∈ segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf (if _root_.Bool.false then 1 else 3)))) ↔ _
  rw [vertical_spoke, vertical_spoke, vertical_spoke]
  cases a <;> cases b <;>
    simp only [section34CrossingQuadrant, Bool.false_eq_true, ↓reduceIte, _root_.Set.mem_prod, _root_.Set.mem_Icc] <;>
    constructor <;> intro h
  all_goals aesop

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.quadrant_inter_vertical
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.quadrant_inter_vertical target :: scope.openDecls } }

theorem IsCylindricalDiagram.filling_face_ribbon_contacts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ℝ × ℝ) × ℝ → E} {C R A B F D : Set E}
    (hf : IsCylindricalDiagram f spliceSquare C)
    (hends : ∀ x ∈ spliceSquare, f (x, 0) = f (x, 1))
    (hfirst : f '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2) = C ∩ A)
    (hsecond : f '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3) = C ∩ B)
    {a b : Bool}
    (hquadrant : f '' (section34CrossingQuadrant a b ×ˢ _root_.Set.Icc (0 : ℝ) 1) = C ∩ R)
    (hF : A ∩ R = F) (hD : B ∩ R = D) :
    C ∩ F = f '' section34MarkedRibbon (if a then 0 else 2) ∧
      C ∩ D = f '' section34MarkedRibbon (if b then 1 else 3) := by
  have hleft : C ∩ F = (C ∩ R) ∩ (C ∩ A) := by
    rw [← hF]
    ext x
    simp only [_root_.Set.mem_inter_iff]
    tauto
  have hright : C ∩ D = (C ∩ R) ∩ (C ∩ B) := by
    rw [← hD]
    ext x
    simp only [_root_.Set.mem_inter_iff]
    tauto
  rw [hleft, hright, ← hquadrant, ← hfirst, ← hsecond]
  simp only [section34MarkedRibbon, ← _root_.Set.union_prod]
  constructor
  · rw [hf.inter_images_base_regions hends
      (section34_crossing_quadrant_subset_square a b)
      (_root_.Set.union_subset (segment_zero_fourSpokeModelLeaf_subset 0)
        (segment_zero_fourSpokeModelLeaf_subset 2)), quadrant_inter_horizontal]
  · rw [hf.inter_images_base_regions hends
      (section34_crossing_quadrant_subset_square a b)
      (_root_.Set.union_subset (segment_zero_fourSpokeModelLeaf_subset 1)
        (segment_zero_fourSpokeModelLeaf_subset 3)), quadrant_inter_vertical]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.filling_face_ribbon_contacts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.filling_face_ribbon_contacts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.filling_face_ribbon_contacts ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.filling_face_ribbon_contacts

end DifferentialGeometry.Topology.PiecewiseLinear
