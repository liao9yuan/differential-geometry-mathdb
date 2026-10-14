/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossQuarterLink
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallPairArc
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CurvePrism

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric _root_.Submission.Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

def crossHalfPlane (i : Fin 4) : Set ((ℝ × ℝ) × ℝ) :=
  {p | ∃ a : ℝ, 0 ≤ a ∧ p.1 = a • fourSpokeModelLeaf i}

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlane with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlane"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlane ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlane

def crossHalfPlaneRectangle (r z : ℝ) (i : Fin 4) : Set ((ℝ × ℝ) × ℝ) :=
  segment ℝ (0 : ℝ × ℝ) (r • fourSpokeModelLeaf i) ×ˢ _root_.Set.Icc (z - r) (z + r)

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlaneRectangle with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlaneRectangle"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlaneRectangle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlaneRectangle

private theorem zero_ne_smul_leaf (i : Fin 4) {r : ℝ} (hr : 0 < r) :
    (0 : ℝ × ℝ) ≠ r • fourSpokeModelLeaf i := by
  exact (smul_ne_zero hr.ne' (fourSpokeModelLeaf_ne_zero i)).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.zero_ne_smul_leaf
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.zero_ne_smul_leaf target :: scope.openDecls } }

theorem isPLBall_crossHalfPlaneRectangle (i : Fin 4) {r z : ℝ} (hr : 0 < r) :
    IsPLBall 2 (crossHalfPlaneRectangle r z i) :=
  isPLBall_two_prod (isPLBall_segment (zero_ne_smul_leaf i hr)) (isPLBall_Icc (by linarith))

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_crossHalfPlaneRectangle with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_crossHalfPlaneRectangle"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_crossHalfPlaneRectangle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_crossHalfPlaneRectangle

open _root_.Classical in
theorem boundaryComplex_space_crossHalfPlaneRectangle (i : Fin 4) {r z : ℝ} (hr : 0 < r)
    (K : Geometry.SimplicialComplex ℝ ((ℝ × ℝ) × ℝ)) [Finite K.faces]
    [d : DecidableEq ((ℝ × ℝ) × ℝ)]
    (hK : K.space = crossHalfPlaneRectangle r z i) :
    (boundaryComplex 2 K).space =
      segment ℝ (0 : ℝ × ℝ) (r • fourSpokeModelLeaf i) ×ˢ {z - r, z + r} ∪
        ({0, r • fourSpokeModelLeaf i} : Set (ℝ × ℝ)) ×ˢ _root_.Set.Icc (z - r) (z + r) := by
  have hd : d = fun x y => Classical.propDecidable (x = y) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq ((ℝ × ℝ) × ℝ) := Classical.decEq _
  let _ : DecidableEq (ℝ × ℝ) := Classical.decEq _
  have hne := zero_ne_smul_leaf i hr
  let A := simplexComplex ({0, r • fourSpokeModelLeaf i} : Finset (ℝ × ℝ))
    (affineIndependent_coe_pair hne)
  let _ : Finite A.faces := (simplexComplex_faces_finite _ _).to_subtype
  have hAspace : A.space = segment ℝ (0 : ℝ × ℝ) (r • fourSpokeModelLeaf i) := by
    rw [simplexComplex_space _ _ (by simp), Finset.coe_pair, convexHull_pair]
  have hA : IsPLBall 1 A.space := hAspace.symm ▸ isPLBall_segment hne
  have hAb : (boundaryComplex 1 A).space = ({0, r • fourSpokeModelLeaf i} : Set (ℝ × ℝ)) := by
    change (boundaryComplex 1 (simplexComplex _ (affineIndependent_coe_pair hne))).space = _
    rw [boundaryComplex_simplexComplex (n := 0) (affineIndependent_coe_pair hne)
      (Finset.card_pair hne), simplexBoundary_pair_space hne]
  have hprod : K.space = A.space ×ˢ _root_.Set.Icc (z - r) (z + r) := by
    rw [hAspace]
    exact hK
  rw [boundaryComplex_space_prism_one A hA (by linarith) K hprod, hAspace, hAb]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_crossHalfPlaneRectangle with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_crossHalfPlaneRectangle"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_crossHalfPlaneRectangle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_crossHalfPlaneRectangle

private theorem mem_scaled_arm_iff (i : Fin 4) {r : ℝ} (hr : 0 < r) {p : ℝ × ℝ} :
    p ∈ segment ℝ (0 : ℝ × ℝ) (r • fourSpokeModelLeaf i) ↔
      ∃ a ∈ _root_.Set.Icc (0 : ℝ) r, p = a • fourSpokeModelLeaf i := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t * r, ⟨mul_nonneg ht.1 hr.le, ?_⟩, ?_⟩
    · nlinarith [ht.2]
    · simp only [smul_zero, zero_add, smul_smul]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a / r, ⟨div_nonneg ha.1 hr.le, (div_le_one hr).mpr ha.2⟩, ?_⟩
    simp only [smul_zero, zero_add, smul_smul, div_mul_cancel₀ _ hr.ne']

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_scaled_arm_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.mem_scaled_arm_iff target :: scope.openDecls } }

theorem crossHalfPlaneRectangle_subset_closedBall (i : Fin 4) {r z : ℝ} (hr : 0 < r) :
    crossHalfPlaneRectangle r z i ⊆ _root_.Metric.closedBall ((0 : ℝ × ℝ), z) r := by
  rintro ⟨p, t⟩ ⟨hp, ht⟩
  obtain ⟨a, ha, rfl⟩ := (mem_scaled_arm_iff i hr).mp hp
  rw [_root_.Metric.mem_closedBall, Prod.dist_eq, max_le_iff, dist_zero_right, Real.dist_eq]
  constructor
  · rw [norm_smul, norm_fourSpokeModelLeaf, mul_one, Real.norm_of_nonneg ha.1]
    exact ha.2
  · exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlaneRectangle_subset_closedBall with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlaneRectangle_subset_closedBall"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlaneRectangle_subset_closedBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlaneRectangle_subset_closedBall

theorem mem_crossHalfPlaneRectangle_iff_of_mem_ball (i : Fin 4) {r z : ℝ} (hr : 0 < r)
    {p : (ℝ × ℝ) × ℝ} (hp : p ∈ _root_.Metric.ball ((0 : ℝ × ℝ), z) r) :
    p ∈ crossHalfPlaneRectangle r z i ↔ p ∈ crossHalfPlane i := by
  have hp' := hp
  rw [_root_.Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right, Real.dist_eq] at hp'
  constructor
  · intro h
    obtain ⟨a, ha, heq⟩ := (mem_scaled_arm_iff i hr).mp h.1
    exact ⟨a, ha.1, heq⟩
  · rintro ⟨a, ha, heq⟩
    have har : a < r := by
      have h := hp'.1
      rw [heq, norm_smul, norm_fourSpokeModelLeaf, mul_one, Real.norm_of_nonneg ha] at h
      exact h
    exact ⟨(mem_scaled_arm_iff i hr).mpr ⟨a, ⟨ha, har.le⟩, heq⟩,
      ⟨by linarith [(abs_lt.mp hp'.2).1], by linarith [(abs_lt.mp hp'.2).2]⟩⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_crossHalfPlaneRectangle_iff_of_mem_ball with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_crossHalfPlaneRectangle_iff_of_mem_ball"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_crossHalfPlaneRectangle_iff_of_mem_ball ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_crossHalfPlaneRectangle_iff_of_mem_ball

open _root_.Classical in
theorem mem_boundaryComplex_crossHalfPlaneRectangle_iff_of_mem_ball
    (i : Fin 4) {r z : ℝ} (hr : 0 < r)
    (K : Geometry.SimplicialComplex ℝ ((ℝ × ℝ) × ℝ)) [Finite K.faces]
    [d : DecidableEq ((ℝ × ℝ) × ℝ)]
    (hK : K.space = crossHalfPlaneRectangle r z i)
    {p : (ℝ × ℝ) × ℝ} (hp : p ∈ _root_.Metric.ball ((0 : ℝ × ℝ), z) r) :
    p ∈ (boundaryComplex 2 K).space ↔ p.1 = 0 := by
  have hp' := hp
  rw [_root_.Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right, Real.dist_eq] at hp'
  have ht : p.2 ∈ _root_.Set.Ioo (z - r) (z + r) :=
    ⟨by linarith [(abs_lt.mp hp'.2).1], by linarith [(abs_lt.mp hp'.2).2]⟩
  have hleaf : p.1 ≠ r • fourSpokeModelLeaf i := by
    intro heq
    have h := hp'.1
    rw [heq, norm_smul, norm_fourSpokeModelLeaf, mul_one, Real.norm_of_nonneg hr.le] at h
    exact lt_irrefl r h
  rw [boundaryComplex_space_crossHalfPlaneRectangle i hr K hK]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · rcases h with h | h
      · exact (ht.1.ne' h).elim
      · exact (ht.2.ne h).elim
    · exact h.resolve_right hleaf
  · intro h
    exact Or.inr ⟨Or.inl h, ht.1.le, ht.2.le⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_boundaryComplex_crossHalfPlaneRectangle_iff_of_mem_ball with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_boundaryComplex_crossHalfPlaneRectangle_iff_of_mem_ball"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_boundaryComplex_crossHalfPlaneRectangle_iff_of_mem_ball ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_boundaryComplex_crossHalfPlaneRectangle_iff_of_mem_ball

theorem crossHalfPlaneRectangle_subset_crossHalfPlane (i : Fin 4) {r z : ℝ} (hr : 0 < r) :
    crossHalfPlaneRectangle r z i ⊆ crossHalfPlane i := by
  intro p hp
  obtain ⟨a, ha, heq⟩ := (mem_scaled_arm_iff i hr).mp hp.1
  exact ⟨a, ha.1, heq⟩

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlaneRectangle_subset_crossHalfPlane with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlaneRectangle_subset_crossHalfPlane"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlaneRectangle_subset_crossHalfPlane ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlaneRectangle_subset_crossHalfPlane

theorem crossHalfPlane_subset_crossPlanes (i : Fin 4) : crossHalfPlane i ⊆ crossPlanes := by
  rintro p ⟨a, -, heq⟩
  change p.1.1 = 0 ∨ p.1.2 = 0
  rw [heq]
  rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;>
    simp [fourSpokeModelLeaf]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlane_subset_crossPlanes with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlane_subset_crossPlanes"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlane_subset_crossPlanes ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossHalfPlane_subset_crossPlanes

end DifferentialGeometry.Topology.PiecewiseLinear
