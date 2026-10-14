/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCollarRayOwnership
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCollarLink
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeLabels

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem exists_four_derived_collar_marks_outside_caps
    (hD : NormalSingularCellData D BdM B)
    {ι : M → E} (hι : Function.Injective ι) (hPL : IsPiecewiseAffineOn (ι ∘ D) D.domain)
    {c : hD.singularSet.Branch} {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ)
    (R Γ : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hΓR : Γ.faces ⊆ R.faces) (hΓ : Γ.space = ι '' hD.singularSet.branchCarrier c)
    {a : Bool → EuclideanSpace ℝ (Fin 2)} (ha : ∀ b, a b ∈ J)
    (hp : {ι (D (a _root_.Bool.false))} ∈ R.faces) (hDa : ∀ b, D (a b) = D (a _root_.Bool.false))
    (harm : ∀ b positive : Bool, (PiecewiseLinear.restrict R
      ((fun t : ℝ => ι (D (ρ (a b, t)))) ''
        (if positive then _root_.Set.Icc (0 : ℝ) 1 else _root_.Set.Icc (-1 : ℝ) 0))).space =
      (fun t : ℝ => ι (D (ρ (a b, t)))) ''
        (if positive then _root_.Set.Icc (0 : ℝ) 1 else _root_.Set.Icc (-1 : ℝ) 0))
    {A : Bool → Set (EuclideanSpace ℝ (Fin 2))} (hAc : ∀ b, IsClosed (A b))
    (hAA : Disjoint (A _root_.Bool.false) (A _root_.Bool.true)) (haA : ∀ b, a b ∈ A b)
    (hpre : ∀ x ∈ D.domain,
      ι (D x) ∈ (derivedNeighborhoodCell R {ι (D (a _root_.Bool.false))}).space → x ∈ A _root_.Bool.false ∪ A _root_.Bool.true)
    {t₀ t₁ : Finset E} (ht₀ : t₀ ∈ Γ.faces) (ht₁ : t₁ ∈ Γ.faces)
    (hne₀ : t₀ ≠ {ι (D (a _root_.Bool.false))}) (hne₁ : t₁ ≠ {ι (D (a _root_.Bool.false))})
    {D₀ D₁ : Set E} (hcap₀ : D₀ ⊆ (derivedNeighborhoodCell R t₀).space)
    (hcap₁ : D₁ ⊆ (derivedNeighborhoodCell R t₁).space) :
    ∃ v : Fin 4 → ℝ,
      (∀ i, v i ∈ _root_.Set.Icc (-1 : ℝ) 1) ∧ 0 < v 0 ∧ 0 < v 1 ∧ v 2 < 0 ∧ v 3 < 0 ∧
      ∀ i, ι (D (ρ (a (fourSpokeLabel i).1, v i))) ∈
        ((derivedNeighborhoodCellBase R {ι (D (a _root_.Bool.false))}).space ∩
          (ι ∘ D) '' (A (fourSpokeLabel i).1 ∩ collarHalf J ρ (fourSpokeLabel i).2)) \
            (D₀ ∪ D₁) := by
  have hex : ∀ i : Fin 4, ∃ v ∈ _root_.Set.Icc (-1 : ℝ) 1,
      (if (fourSpokeLabel i).2 then 0 < v else v < 0) ∧
      ι (D (ρ (a (fourSpokeLabel i).1, v))) ∈
        ((derivedNeighborhoodCellBase R {ι (D (a _root_.Bool.false))}).space ∩
          (ι ∘ D) '' (A (fourSpokeLabel i).1 ∩ collarHalf J ρ (fourSpokeLabel i).2)) \
            (D₀ ∪ D₁) := by
    intro i
    let b := (fourSpokeLabel i).1
    let positive := (fourSpokeLabel i).2
    have hbR : {ι (D (a b))} ∈ R.faces := by rw [hDa b]; exact hp
    have hdis : Disjoint (A b) (A (!b)) := by
      cases b
      · exact hAA
      · exact hAA.symm
    have hpreb : ∀ x ∈ D.domain,
        ι (D x) ∈ (derivedNeighborhoodCell R {ι (D (a b))}).space → x ∈ A b ∪ A (!b) := by
      intro x hx hxc
      rw [hDa b] at hxc
      have h := hpre x hx hxc
      cases b
      · exact h
      · exact h.symm
    obtain ⟨v, hv, hsign, hvA, hbase⟩ := hD.exists_derived_collar_ray_in_source_sheet hι hPL hρ
      (ha b) R hbR positive (harm b positive) (hAc b) (hAc (!b)) hdis (haA b) hpreb
    let F : ℝ → E := fun t => ι (D (ρ (a b, t)))
    let I : Set ℝ := if positive then _root_.Set.Icc 0 1 else _root_.Set.Icc (-1) 0
    let K := PiecewiseLinear.restrict R (F '' I)
    have hKsp : K.space = F '' I := harm b positive
    have hKI : K.space ∩ Γ.space = {ι (D (a _root_.Bool.false))} := by
      rw [hKsp, hΓ]
      have hIsub : I ⊆ _root_.Set.Icc (-1 : ℝ) 1 := by
        dsimp only [I]
        split_ifs
        · exact _root_.Set.Icc_subset_Icc (by norm_num) le_rfl
        · exact _root_.Set.Icc_subset_Icc le_rfl (by norm_num)
      have h0 : (0 : ℝ) ∈ I := by dsimp only [I]; split_ifs <;> norm_num
      rw [hD.collar_arm_inter_branchCarrier hι hρ (ha b) hIsub h0, hDa b]
    have hdis₀ := derivedNeighborhoodCell_disjoint_of_subcomplex_inter_singleton R Γ K
      hΓR (restrict_faces_subset R _) hp hKI ht₀ hne₀
    have hdis₁ := derivedNeighborhoodCell_disjoint_of_subcomplex_inter_singleton R Γ K
      hΓR (restrict_faces_subset R _) hp hKI ht₁ hne₁
    have hx : F v ∈ (derivedNeighborhoodCellBase R {ι (D (a b))}).space ∩ F '' I :=
      hbase.symm ▸ _root_.Set.mem_singleton (F v)
    refine ⟨v, hv, hsign, ⟨?_, ⟨ρ (a b, v), hvA, rfl⟩⟩, ?_⟩
    · have hxs := hx.1
      rwa [hDa b] at hxs
    · have hxK : F v ∈ K.space := hKsp.symm ▸ hx.2
      rintro (h₀ | h₁)
      · exact disjoint_left.mp hdis₀ (hcap₀ h₀) hxK
      · exact disjoint_left.mp hdis₁ (hcap₁ h₁) hxK
  choose v hv hsign hmem using hex
  exact ⟨v, hv, hsign 0, hsign 1, hsign 2, hsign 3, hmem⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_four_derived_collar_marks_outside_caps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_four_derived_collar_marks_outside_caps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_four_derived_collar_marks_outside_caps ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_four_derived_collar_marks_outside_caps

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData
