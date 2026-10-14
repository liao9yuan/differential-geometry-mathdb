/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerEssentialSeams
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.TorusMixedAnnulus
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLAnnulusReversal
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSeamDeletion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def oddTorusSeams (T'' : ℤ → Set E3) (i : ℤ) : Set (Set E3) :=
  traceCircles (T'' (2 * i)) (T'' (2 * i + 1)) ∪
    traceCircles (T'' (2 * i + 1)) (T'' (2 * (i + 1)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oddTorusSeams then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oddTorusSeams"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oddTorusSeams ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oddTorusSeams

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.finite_oddTorusSeams
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    (oddTorusSeams T'' i).Finite := by
  apply (htw.finite_traceCircles (2 * i)).union
  simpa only [show 2 * i + 1 + 1 = 2 * (i + 1) by omega] using
    htw.finite_traceCircles (2 * i + 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.finite_oddTorusSeams then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.finite_oddTorusSeams"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.finite_oddTorusSeams ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.finite_oddTorusSeams

theorem IsCanonicalTower.oddTorusSeams_pairwiseDisjoint
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    (oddTorusSeams T'' i).PairwiseDisjoint id := by
  have hTdis : Disjoint (T'' (2 * i)) (T'' (2 * (i + 1))) :=
    (htw.apart (2 * i) (2 * (i + 1)) (by rw [le_abs]; omega)).mono
      (htw.boundary_subset_outer _) (htw.boundary_subset_outer _)
  intro G hG H hH hGH
  rcases hG with hG | hG <;> rcases hH with hH | hH
  · exact pairwiseDisjoint_traceCircles _ _ hG hH hGH
  · exact hTdis.mono ((traceCircles_subset hG).trans _root_.Set.inter_subset_left)
      ((traceCircles_subset hH).trans _root_.Set.inter_subset_right)
  · exact hTdis.symm.mono ((traceCircles_subset hG).trans _root_.Set.inter_subset_right)
      ((traceCircles_subset hH).trans _root_.Set.inter_subset_left)
  · exact pairwiseDisjoint_traceCircles _ _ hG hH hGH

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.oddTorusSeams_pairwiseDisjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.oddTorusSeams_pairwiseDisjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.oddTorusSeams_pairwiseDisjoint ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.oddTorusSeams_pairwiseDisjoint

theorem IsCanonicalTower.exists_mixed_oddPiece_annulus
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    ∃ Glo Ghi B : Set E3,
      Glo ∈ traceCircles (canonicalOddPiece S'' T'' i) (T'' (2 * i)) ∧
      Ghi ∈ traceCircles (canonicalOddPiece S'' T'' i) (T'' (2 * (i + 1))) ∧
      ¬ boundsDiskIn Glo (T'' (2 * i + 1)) ∧
      ¬ boundsDiskIn Ghi (T'' (2 * i + 1)) ∧
      IsPLAnnulusWithEnds B Glo Ghi ∧ B ⊆ T'' (2 * i + 1) ∧
      Disjoint (B \ (Glo ∪ Ghi))
        (⋃ G ∈ {G ∈ oddTorusSeams T'' i | ¬ boundsDiskIn G (T'' (2 * i + 1))}, G) ∧
      IsClosed (T'' (2 * i + 1) \ (B \ (Glo ∪ Ghi))) ∧
      closure (B \ (Glo ∪ Ghi)) = B ∧
      ∀ x ∈ B \ (Glo ∪ Ghi), connectedComponentIn
        (T'' (2 * i + 1) \
          ⋃ G ∈ {G ∈ oddTorusSeams T'' i | ¬ boundsDiskIn G (T'' (2 * i + 1))}, G) x =
        B \ (Glo ∪ Ghi) := by
  classical
  let L := traceCircles (T'' (2 * i)) (T'' (2 * i + 1))
  let H := traceCircles (T'' (2 * i + 1)) (T'' (2 * (i + 1)))
  let Γ := {G ∈ oddTorusSeams T'' i | ¬ boundsDiskIn G (T'' (2 * i + 1))}
  have hΓfin : Γ.Finite := (htw.finite_oddTorusSeams i).subset fun _ hG => hG.1
  let _ := hΓfin.to_subtype
  have hΓsphere : ∀ G : Γ, IsPLSphere 1 (G : Set E3) := by
    intro G
    rcases G.property.1 with hG | hG
    · exact traceCircles_isPLSphere hG
    · exact traceCircles_isPLSphere hG
  have hΓsub : ∀ G : Γ, (G : Set E3) ⊆ T'' (2 * i + 1) := by
    intro G
    rcases G.property.1 with hG | hG
    · exact (traceCircles_subset hG).trans _root_.Set.inter_subset_right
    · exact (traceCircles_subset hG).trans _root_.Set.inter_subset_left
  have hΓdis : Pairwise fun G H : Γ => Disjoint (G : Set E3) (H : Set E3) := by
    intro G H hne
    exact htw.oddTorusSeams_pairwiseDisjoint i G.property.1 H.property.1
      (fun heq => hne (Subtype.ext heq))
  have hLH : Disjoint L H := by
    apply disjoint_left.mpr
    intro G hL hH
    obtain ⟨x, hx⟩ := (traceCircles_isPLSphere hL).nonempty
    have hlow := (traceCircles_subset hL hx).1
    have hhigh := (traceCircles_subset hH hx).2
    exact disjoint_left.mp
      (htw.apart (2 * i) (2 * (i + 1)) (by rw [le_abs]; omega))
      (htw.boundary_subset_outer _ hlow) (htw.boundary_subset_outer _ hhigh)
  obtain ⟨Glo, Ghi, hlo, hhi, hloe, hhie, -, -, -⟩ := htw.exists_essential_oddPiece_seams i
  have hlo' : Glo ∈ L := by
    simpa only [L, traceCircles, htw.oddPiece_inter_even, _root_.Set.inter_comm] using hlo
  have hhi' : Ghi ∈ H := by
    simpa only [H, traceCircles, htw.oddPiece_inter_even] using hhi
  let lo : Γ := ⟨Glo, Or.inl hlo', hloe⟩
  let hi : Γ := ⟨Ghi, Or.inr hhi', hhie⟩
  let color : Γ → Bool := fun G => _root_.Decidable.decide ((G : Set E3) ∈ L)
  have hcolors : color lo ≠ color hi := by
    have hhinL : Ghi ∉ L := fun h => disjoint_left.mp hLH h hhi'
    simp only [color, lo, hi, hlo', hhinL, decide_true, decide_false, ne_eq,
      Bool.true_eq_false, not_false_eq_true]
  have hsolid : IsCombinatorialSolidTorus (S'' (2 * i + 1)) := by
    simpa using (htw.config (2 * i + 1)).isPolyhedralSolidTorus 0
  obtain ⟨a, b, B, hab, hB, hBT, hBdis, hBclosed, hBcl, hBcomp⟩ :=
    hsolid.exists_annulus_between_essential_circles_of_ne_colors
      (fun G : Γ => (G : Set E3)) hΓsphere
      (fun G => by rw [← htw.boundary_eq]; exact hΓsub G) hΓdis
      (fun G => by rw [← htw.boundary_eq]; exact G.property.2) color hcolors
  have hunion : (⋃ G : Γ, (G : Set E3)) = ⋃ G ∈ Γ, G := by
    ext x
    simp only [_root_.Set.mem_iUnion, Subtype.exists, exists_prop]
  rw [hunion] at hBdis hBcomp
  rw [← htw.boundary_eq] at hBT hBclosed hBcomp
  have hreverse : ∀ G ∈ L, G ∈ traceCircles (canonicalOddPiece S'' T'' i) (T'' (2 * i)) :=
    fun G hG => by
      simpa only [L, traceCircles, htw.oddPiece_inter_even, _root_.Set.inter_comm] using hG
  have hforward : ∀ G ∈ H, G ∈ traceCircles (canonicalOddPiece S'' T'' i)
      (T'' (2 * (i + 1))) := fun G hG => by
    simpa only [H, traceCircles, htw.oddPiece_inter_even] using hG
  by_cases haL : (a : Set E3) ∈ L
  · have hbnL : (b : Set E3) ∉ L := by
      intro hbL
      exact hab (by simp only [color, haL, hbL])
    have hbH : (b : Set E3) ∈ H := b.property.1.resolve_left hbnL
    exact ⟨a, b, B, hreverse a haL, hforward b hbH, a.property.2, b.property.2,
      hB, hBT, hBdis, hBclosed, hBcl, hBcomp⟩
  · have hbL : (b : Set E3) ∈ L := by
      by_contra hbnL
      exact hab (by simp only [color, haL, hbnL])
    have haH : (a : Set E3) ∈ H := a.property.1.resolve_left haL
    refine ⟨b, a, B, hreverse b hbL, hforward a haH, b.property.2, a.property.2,
      hB.symm, hBT, ?_, ?_, ?_, ?_⟩
    · simpa only [_root_.Set.union_comm] using hBdis
    · simpa only [_root_.Set.union_comm] using hBclosed
    · simpa only [_root_.Set.union_comm] using hBcl
    · simpa only [_root_.Set.union_comm] using hBcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.exists_mixed_oddPiece_annulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.exists_mixed_oddPiece_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.exists_mixed_oddPiece_annulus ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.exists_mixed_oddPiece_annulus

end DifferentialGeometry.Topology.PiecewiseLinear
