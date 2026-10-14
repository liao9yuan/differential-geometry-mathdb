/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.RectangleArcPair
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CylindricalDiagram

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem exists_cylindricalDiagram_of_disk_pair {a b : ℝ} (hab : a < b)
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsPLBall 2 K.space) (hL : IsPLBall 2 L.space)
    {D₀ D₁ : Set E} (hD₁ : IsPLBall 1 D₁) (hdis : Disjoint D₀ D₁)
    (hD₀K : D₀ ⊆ (boundaryComplex 2 K).space) (hD₁K : D₁ ⊆ (boundaryComplex 2 K).space)
    (hD₀L : D₀ ⊆ (boundaryComplex 2 L).space) (hD₁L : D₁ ⊆ (boundaryComplex 2 L).space)
    (hinter : K.space ∩ L.space = D₀ ∪ D₁)
    {g₀ : ℝ → E} (hg₀ : IsPLHomeomorphOn g₀ (_root_.Set.Icc a b) D₀) :
    ∃ φ : ℝ × ℝ → E, IsCylindricalDiagram φ (_root_.Set.Icc a b) (K.space ∪ L.space) ∧
      ∀ x ∈ _root_.Set.Icc a b, φ (x, 0) = g₀ x := by
  let _ : DecidableEq E := Classical.decEq _
  have hP := isPLBall_Icc hab
  obtain ⟨f, hf, hf₀, hfm⟩ := exists_isPLHomeomorphOn_rectangle_map_ends hab
    (by norm_num : (0 : ℝ) < 1 / 2) K hK hD₀K hD₁ hD₁K hdis hg₀
  have hmidpoly : IsPolyhedron (_root_.Set.Icc a b ×ˢ {(1 / 2 : ℝ)}) :=
    (hP.of_isPLHomeomorphOn (hP.isPolyhedron.isPLHomeomorphOn_prod_const (1 / 2))).isPolyhedron
  have hfmid : IsPLHomeomorphOn f (_root_.Set.Icc a b ×ˢ {1 / 2}) D₁ := by
    have h := hf.restrict hmidpoly (fun _ hx => ⟨hx.1, hx.2.symm ▸ ⟨by norm_num, le_rfl⟩⟩)
    rwa [hfm] at h
  let g₁ : ℝ → E := fun x => f (x, 1 / 2)
  have hg₁ : IsPLHomeomorphOn g₁ (_root_.Set.Icc a b) D₁ :=
    (hP.isPolyhedron.isPLHomeomorphOn_prod_const (1 / 2)).trans hfmid
  obtain ⟨g, hg, hgm, hg₁⟩ := exists_isPLHomeomorphOn_rectangle_map_ends hab
    (by norm_num : (1 / 2 : ℝ) < 1) L hL hD₁L (hP.of_isPLHomeomorphOn hg₀) hD₀L hdis.symm hg₁
  have hfzero : f '' (_root_.Set.Icc a b ×ˢ {0}) = D₀ := by
    have heq : _root_.Set.EqOn (f ∘ fun x : ℝ => (x, (0 : ℝ))) g₀ (_root_.Set.Icc a b) := hf₀
    rw [← (hP.isPolyhedron.isPLHomeomorphOn_prod_const 0).image_eq, _root_.Set.image_image]
    exact heq.image_eq.trans hg₀.image_eq
  have hfg : _root_.Set.EqOn f g (_root_.Set.Icc a b ×ˢ {1 / 2}) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    change t = 1 / 2 at ht
    subst t
    exact (hgm x hx).symm
  refine ⟨_,
    isCylindricalDiagram_piecewise hP.isPolyhedron hf hg hfzero hg₁ hfm hfg hinter, ?_⟩
  intro x hx
  simp only [Set.piecewise,
    if_pos (show (x, (0 : ℝ)) ∈ _root_.Set.Icc a b ×ˢ _root_.Set.Icc 0 (1 / 2) from ⟨hx, by norm_num⟩)]
  exact hf₀ x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_cylindricalDiagram_of_disk_pair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_cylindricalDiagram_of_disk_pair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_cylindricalDiagram_of_disk_pair ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_cylindricalDiagram_of_disk_pair

end DifferentialGeometry.Topology.PiecewiseLinear
