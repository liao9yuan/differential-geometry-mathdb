/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolvedCell

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem exists_plCrossSeamReading_of_four_source_pages
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {chart : (ℝ × ℝ) × ℝ → M} {G : SingularTwoCell M}
    {Z₀ Z₁ Z₂ Z₃ Jpos Jneg : Set (EuclideanSpace ℝ (Fin 2))}
    {g₀ g₁ g₂ g₃ : EuclideanSpace ℝ (Fin 2) → (ℝ × ℝ) × ℝ}
    (hZ₀ : IsPolyhedron Z₀) (hZ₁ : IsPolyhedron Z₁)
    (hZ₂ : IsPolyhedron Z₂) (hZ₃ : IsPolyhedron Z₃)
    (hg₀ : IsPLHomeomorphOn g₀ Z₀ (crossRayPosX ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hg₁ : IsPLHomeomorphOn g₁ Z₁ (crossRayNegX ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hg₂ : IsPLHomeomorphOn g₂ Z₂ (crossRayPosY ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hg₃ : IsPLHomeomorphOn g₃ Z₃ (crossRayNegY ×ˢ _root_.Set.Icc (0 : ℝ) 1))
    (hJpos : Z₀ ∩ Z₃ = Jpos) (hJneg : Z₁ ∩ Z₂ = Jneg)
    (hdisj₀₁ : Disjoint Z₀ Z₁) (hdisj₀₂ : Disjoint Z₀ Z₂)
    (hdisj₁₃ : Disjoint Z₁ Z₃) (hdisj₂₃ : Disjoint Z₂ Z₃)
    (hseamPos : _root_.Set.EqOn g₀ g₃ Jpos) (hseamNeg : _root_.Set.EqOn g₁ g₂ Jneg)
    (hinterPos : _root_.Set.SurjOn g₀ (Z₀ ∩ Z₃)
      ((crossRayPosX ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ (crossRayNegY ×ˢ _root_.Set.Icc (0 : ℝ) 1)))
    (hinterNeg : _root_.Set.SurjOn g₁ (Z₁ ∩ Z₂)
      ((crossRayNegX ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ (crossRayPosY ×ˢ _root_.Set.Icc (0 : ℝ) 1)))
    (hG₀ : _root_.Set.EqOn (⇑G) (chart ∘ g₀) Z₀)
    (hG₁ : _root_.Set.EqOn (⇑G) (chart ∘ g₁) Z₁)
    (hG₂ : _root_.Set.EqOn (⇑G) (chart ∘ g₂) Z₂)
    (hG₃ : _root_.Set.EqOn (⇑G) (chart ∘ g₃) Z₃)
    (hsource : (Z₀ ∪ Z₃) ∪ (Z₁ ∪ Z₂) =
      G.domain ∩ ⇑G ⁻¹' (chart '' spliceCylinder))
    (hboundary₀ : ∀ x ∈ Z₀,
      (x ∈ frontier G.domain ↔ (g₀ x).2 = 0 ∨ (g₀ x).2 = 1))
    (hboundary₁ : ∀ x ∈ Z₁,
      (x ∈ frontier G.domain ↔ (g₁ x).2 = 0 ∨ (g₁ x).2 = 1))
    (hboundary₂ : ∀ x ∈ Z₂,
      (x ∈ frontier G.domain ↔ (g₂ x).2 = 0 ∨ (g₂ x).2 = 1))
    (hboundary₃ : ∀ x ∈ Z₃,
      (x ∈ frontier G.domain ↔ (g₃ x).2 = 0 ∨ (g₃ x).2 = 1))
    (hwall₀ : ∀ x ∈ Z₀ ∩ closure (G.domain \ ((Z₀ ∪ Z₃) ∪ (Z₁ ∪ Z₂))),
      g₀ x ∈ spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1)
    (hwall₁ : ∀ x ∈ Z₁ ∩ closure (G.domain \ ((Z₀ ∪ Z₃) ∪ (Z₁ ∪ Z₂))),
      g₁ x ∈ spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1)
    (hwall₂ : ∀ x ∈ Z₂ ∩ closure (G.domain \ ((Z₀ ∪ Z₃) ∪ (Z₁ ∪ Z₂))),
      g₂ x ∈ spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1)
    (hwall₃ : ∀ x ∈ Z₃ ∩ closure (G.domain \ ((Z₀ ∪ Z₃) ∪ (Z₁ ∪ Z₂))),
      g₃ x ∈ spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1) :
    Nonempty (PLCrossSeamReading chart G) := by
  have hfgPos : _root_.Set.EqOn g₀ g₃ (Z₀ ∩ Z₃) := by
    intro x hx
    exact hseamPos (hJpos.symm ▸ hx)
  have hinterPos' : _root_.Set.SurjOn g₀ (Z₀ ∩ Z₃)
      ((crossRayPosX ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ (crossRayNegY ×ˢ _root_.Set.Icc (0 : ℝ) 1)) := hinterPos
  obtain ⟨cpos, hcpos, hc₀, hc₃⟩ :=
    exists_isPLHomeomorphOn_union hZ₀ hZ₃ hg₀ hg₃ hfgPos hinterPos'
  have hfgNeg : _root_.Set.EqOn g₁ g₂ (Z₁ ∩ Z₂) := by
    intro x hx
    exact hseamNeg (hJneg.symm ▸ hx)
  have hinterNeg' : _root_.Set.SurjOn g₁ (Z₁ ∩ Z₂)
      ((crossRayNegX ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ (crossRayPosY ×ˢ _root_.Set.Icc (0 : ℝ) 1)) := hinterNeg
  obtain ⟨cneg, hcneg, hc₁, hc₂⟩ :=
    exists_isPLHomeomorphOn_union hZ₁ hZ₂ hg₁ hg₂ hfgNeg hinterNeg'
  have htargetPos :
      (crossRayPosX ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∪ (crossRayNegY ×ˢ _root_.Set.Icc (0 : ℝ) 1) = bentSheetPos := by
    rw [bentSheetPos, bentArcPos, Set.union_prod]
  have htargetNeg :
      (crossRayNegX ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∪ (crossRayPosY ×ˢ _root_.Set.Icc (0 : ℝ) 1) = bentSheetNeg := by
    rw [bentSheetNeg, bentArcNeg, Set.union_prod]
  rw [htargetPos] at hcpos
  rw [htargetNeg] at hcneg
  let sourcePos : Set (EuclideanSpace ℝ (Fin 2)) := Z₀ ∪ Z₃
  let sourceNeg : Set (EuclideanSpace ℝ (Fin 2)) := Z₁ ∪ Z₂
  have hsourceDisjoint : Disjoint sourcePos sourceNeg := by
    rw [Set.disjoint_left]
    intro x hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Set.disjoint_left.mp hdisj₀₁ hx hy
    · exact Set.disjoint_left.mp hdisj₀₂ hx hy
    · exact Set.disjoint_left.mp hdisj₁₃ hy hx
    · exact Set.disjoint_left.mp hdisj₂₃ hy hx
  let P : Set (EuclideanSpace ℝ (Fin 2)) := sourcePos ∪ sourceNeg
  have hsource' : sourcePos ∪ sourceNeg =
      G.domain ∩ ⇑G ⁻¹' (chart '' spliceCylinder) := by
    simpa [sourcePos, sourceNeg, P] using hsource
  have hPpoly : IsPolyhedron P := by
    dsimp [P, sourcePos, sourceNeg]
    exact (hZ₀.union hZ₃).union (hZ₁.union hZ₂)
  let face : Set (EuclideanSpace ℝ (Fin 2)) := closure (G.domain \ P)
  have hfacePoly : IsPolyhedron face := by
    dsimp [face]
    exact G.isPLBall_domain.isPolyhedron.closure_sdiff hPpoly
  have hfaceSubset : face ⊆ G.domain := by
    dsimp [face]
    exact closure_minimal _root_.Set.sdiff_subset G.isPLBall_domain.isPolyhedron.isClosed
  have hcover : sourcePos ∪ sourceNeg ∪ face = G.domain := by
    apply Subset.antisymm
    · intro x hx
      rcases hx with hx | hx
      · have hxdomain := hsource'.symm ▸ hx
        exact hxdomain.1
      · exact hfaceSubset hx
    · intro x hx
      by_cases hxp : x ∈ P
      · exact Or.inl hxp
      · exact Or.inr (subset_closure ⟨hx, hxp⟩)
  classical
  let coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ) :=
    fun x => if x ∈ sourcePos then (_root_.Bool.true, cpos x) else (_root_.Bool.false, cneg x)
  have hcoordPos : _root_.Set.EqOn (fun x => (coord x).2) cpos sourcePos := by
    intro x hx
    simp [coord, hx]
  have hcoordNeg : _root_.Set.EqOn (fun x => (coord x).2) cneg sourceNeg := by
    intro x hx
    have hnot : x ∉ sourcePos := fun hxp =>
      Set.disjoint_left.mp hsourceDisjoint hxp hx
    simp [coord, hnot]
  have hboundary : ∀ x ∈ sourcePos ∪ sourceNeg,
      (x ∈ frontier G.domain ↔ (coord x).2.2 = 0 ∨ (coord x).2.2 = 1) := by
    intro x hx
    rcases hx with hx | hx
    · rcases hx with hx | hx
      · have hcx : (coord x).2 = cpos x := hcoordPos (Or.inl hx)
        have hcg : cpos x = g₀ x := hc₀ hx
        rw [hcx, hcg]
        exact hboundary₀ x hx
      · have hcx : (coord x).2 = cpos x := hcoordPos (Or.inr hx)
        have hcg : cpos x = g₃ x := hc₃ hx
        rw [hcx, hcg]
        exact hboundary₃ x hx
    · rcases hx with hx | hx
      · have hcx : (coord x).2 = cneg x := hcoordNeg (Or.inl hx)
        have hcg : cneg x = g₁ x := hc₁ hx
        rw [hcx, hcg]
        exact hboundary₁ x hx
      · have hcx : (coord x).2 = cneg x := hcoordNeg (Or.inr hx)
        have hcg : cneg x = g₂ x := hc₂ hx
        rw [hcx, hcg]
        exact hboundary₂ x hx
  have hwall : ∀ x ∈ (sourcePos ∪ sourceNeg) ∩ face,
      (coord x).2 ∈ spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1 := by
    intro x hx
    have hfacex := hx.2
    rcases hx.1 with hx | hx
    · rcases hx with hx | hx
      · have hcx : (coord x).2 = cpos x := hcoordPos (Or.inl hx)
        have hcg : cpos x = g₀ x := hc₀ hx
        rw [hcx, hcg]
        exact hwall₀ x ⟨hx, by simpa [face] using hfacex⟩
      · have hcx : (coord x).2 = cpos x := hcoordPos (Or.inr hx)
        have hcg : cpos x = g₃ x := hc₃ hx
        rw [hcx, hcg]
        exact hwall₃ x ⟨hx, by simpa [face] using hfacex⟩
    · rcases hx with hx | hx
      · have hcx : (coord x).2 = cneg x := hcoordNeg (Or.inl hx)
        have hcg : cneg x = g₁ x := hc₁ hx
        rw [hcx, hcg]
        exact hwall₁ x ⟨hx, by simpa [face] using hfacex⟩
      · have hcx : (coord x).2 = cneg x := hcoordNeg (Or.inr hx)
        have hcg : cneg x = g₂ x := hc₂ hx
        rw [hcx, hcg]
        exact hwall₂ x ⟨hx, by simpa [face] using hfacex⟩
  have hreglued : _root_.Set.EqOn (⇑G) (chart ∘ crossSeamInclude ∘ coord)
      (sourcePos ∪ sourceNeg) := by
    intro x hx
    rcases hx with hx | hx
    · rcases hx with hx | hx
      · have hcx : (coord x).2 = cpos x := hcoordPos (Or.inl hx)
        calc
          G x = chart (g₀ x) := hG₀ hx
          _ = chart (cpos x) := congrArg chart (hc₀ hx).symm
          _ = chart (crossSeamInclude (coord x)) := by rw [crossSeamInclude, hcx]
      · have hcx : (coord x).2 = cpos x := hcoordPos (Or.inr hx)
        calc
          G x = chart (g₃ x) := hG₃ hx
          _ = chart (cpos x) := congrArg chart (hc₃ hx).symm
          _ = chart (crossSeamInclude (coord x)) := by rw [crossSeamInclude, hcx]
    · rcases hx with hx | hx
      · have hcx : (coord x).2 = cneg x := hcoordNeg (Or.inl hx)
        calc
          G x = chart (g₁ x) := hG₁ hx
          _ = chart (cneg x) := congrArg chart (hc₁ hx).symm
          _ = chart (crossSeamInclude (coord x)) := by rw [crossSeamInclude, hcx]
      · have hcx : (coord x).2 = cneg x := hcoordNeg (Or.inr hx)
        calc
          G x = chart (g₂ x) := hG₂ hx
          _ = chart (cneg x) := congrArg chart (hc₂ hx).symm
          _ = chart (crossSeamInclude (coord x)) := by rw [crossSeamInclude, hcx]
  let R : PLCrossSeamReading chart G := {
    coord := coord
    sourcePos := sourcePos
    sourceNeg := sourceNeg
    face := face
    isPLHomeomorphOn_pos := hcpos.congr hcoordPos
    isPLHomeomorphOn_neg := hcneg.congr hcoordNeg
    coord_fst_pos := by
      intro x hx
      simp [coord, hx]
    coord_fst_neg := by
      intro x hx
      have hnot : x ∉ sourcePos := fun hxp =>
        Set.disjoint_left.mp hsourceDisjoint hxp hx
      simp [coord, hnot]
    source_eq := hsource'
    isPolyhedron_face := hfacePoly
    union_eq := hcover
    reglued_eq := hreglued
    overlap_lateral := hwall
    boundary_iff_end := hboundary }
  exact ⟨R⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_plCrossSeamReading_of_four_source_pages then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_plCrossSeamReading_of_four_source_pages"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_plCrossSeamReading_of_four_source_pages ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_plCrossSeamReading_of_four_source_pages

end DifferentialGeometry.Topology.PiecewiseLinear
