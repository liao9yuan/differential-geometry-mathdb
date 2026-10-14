/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.TaperedInwardPush

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Fixing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {B W R D : Set E} {ρ : E × ℝ → E}

theorem IsPLHomeomorphOn.exists_pos_forall_le_seam_union
    (hρ : IsPLHomeomorphOn ρ (B ×ˢ _root_.Set.Icc (0 : ℝ) 1) W) (hW : IsPolyhedron W) (hD : IsPolyhedron D)
    (hBD : Disjoint B D) (hbottom : ∀ x ∈ B, ρ (x, 0) = x) {g : E → ℝ} {a : ℝ} (ha : 0 < a)
    (haone : a ≤ 1)
    (hseam : ∀ y ∈ B, ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, ρ (y, t) ∈ R → g y = 0 ∨ a ≤ t) :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧
      ∀ y ∈ B, ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, ρ (y, t) ∈ R ∪ D → g y = 0 ∨ b ≤ t := by
  obtain ⟨c, hc, -, hcle⟩ := hρ.exists_pos_forall_le_of_disjoint hW hD hBD hbottom
  refine ⟨min a c, lt_min ha hc, (min_le_left _ _).trans haone, ?_⟩
  intro y hy t ht hmem
  rcases hmem with hmem | hmem
  · rcases hseam y hy t ht hmem with h0 | hle
    · exact Or.inl h0
    · exact Or.inr ((min_le_left _ _).trans hle)
  · exact Or.inr ((min_le_right _ _).trans (hcle y hy t ht hmem))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_pos_forall_le_seam_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_pos_forall_le_seam_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_pos_forall_le_seam_union ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_pos_forall_le_seam_union

theorem IsPLHomeomorphOn.exists_piecewiseAffineOn_inward_leftInvOn_taper_fixing_dist_lt
    (hρ : IsPLHomeomorphOn ρ (B ×ˢ _root_.Set.Icc (0 : ℝ) 1) W) (hW : IsPolyhedron W) (hR : IsPolyhedron R)
    (hD : IsPolyhedron D) (hBD : Disjoint B D) (hDWR : D ⊆ W ∪ R) (hBc : IsCompact B)
    (hbottom : ∀ x ∈ B, ρ (x, 0) = x) {g : E → ℝ} (hgpl : IsPiecewiseAffineOn g _root_.Set.univ)
    (hgpos : ∀ y : E, 0 ≤ g y) {a : ℝ} (ha : 0 < a) (haone : a ≤ 1)
    (hseam : ∀ y ∈ B, ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, ρ (y, t) ∈ R → g y = 0 ∨ a ≤ t)
    {Z : Type*} [MetricSpace Z] {h : E → Z} (hh : ContinuousOn h W) {ε : ℝ} (hε : 0 < ε) :
    ∃ f f' : E → E, IsPiecewiseAffineOn f (W ∪ R) ∧ _root_.Set.InjOn f (W ∪ R) ∧
      _root_.Set.MapsTo f (W ∪ R) (W ∪ R) ∧ (∀ x ∈ W ∪ R, f x ∈ B → x ∈ B ∧ g x = 0) ∧
      _root_.Set.EqOn f id R ∧ _root_.Set.EqOn f id D ∧
      (∀ y ∈ B, g y = 0 → ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, f (ρ (y, t)) = ρ (y, t)) ∧
      IsPiecewiseAffineOn f' (W ∪ R) ∧ _root_.Set.MapsTo f' (W ∪ R) (W ∪ R) ∧ _root_.Set.EqOn f' id R ∧
      EqOn f' id D ∧ _root_.Set.LeftInvOn f' f (W ∪ R) ∧ ∀ x ∈ W ∪ R, _root_.Dist.dist (h (f x)) (h x) < ε := by
  obtain ⟨b, hb, hbone, hbseam⟩ :=
    hρ.exists_pos_forall_le_seam_union hW hD hBD hbottom ha haone hseam
  have hunion : W ∪ (R ∪ D) = W ∪ R := by
    rw [← _root_.Set.union_assoc]
    exact union_eq_left.mpr hDWR
  obtain ⟨f, f', hfpl, hfinj, hfmap, hfB, hfRD, hfix0, hf'pl, hf'map, hf'RD, hinv, hdist⟩ :=
    hρ.exists_piecewiseAffineOn_inward_leftInvOn_taper_dist_lt hW (hR.union hD) hBc hbottom
      hgpl hgpos hb hbone hbseam hh hε
  rw [hunion] at hfpl hfinj hfmap hfB hf'pl hf'map hinv hdist
  exact ⟨f, f', hfpl, hfinj, hfmap, hfB, fun x hx => hfRD (_root_.Set.mem_union_left D hx),
    fun x hx => hfRD (_root_.Set.mem_union_right R hx), hfix0, hf'pl, hf'map,
    fun x hx => hf'RD (_root_.Set.mem_union_left D hx), fun x hx => hf'RD (_root_.Set.mem_union_right R hx),
    hinv, hdist⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_piecewiseAffineOn_inward_leftInvOn_taper_fixing_dist_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_piecewiseAffineOn_inward_leftInvOn_taper_fixing_dist_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_piecewiseAffineOn_inward_leftInvOn_taper_fixing_dist_lt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.exists_piecewiseAffineOn_inward_leftInvOn_taper_fixing_dist_lt

end Fixing

end DifferentialGeometry.Topology.PiecewiseLinear
