/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.JordanRelativeMatching
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PlanarCellUnion
import Submission.DifferentialGeometry.Topology.PlanarJordan.RegionRecognition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

section PlanarUnion

open _root_.Metric _root_.Submission.Metric _root_.Submission.Schoenflies _root_.unitInterval

namespace DifferentialGeometry.Topology.PlanarJordan

theorem nonempty_homeomorph_closure_inside {Γ : Set Plane} (hΓ : IsJordanCurve Γ) :
    Nonempty (closure (inside Γ) ≃ₜ _root_.Metric.closedBall (0 : Plane) 1) := by
  have hs : IsJordanCurve (_root_.Metric.sphere (0 : Plane) 1) := by
    simpa only [Subtype.range_coe] using isJordanCurve_range_of_isEmbedding_circle
      (Topology.IsEmbedding.subtypeVal :
        Topology.IsEmbedding (Subtype.val : _root_.Metric.sphere (0 : Plane) 1 → Plane))
  have hfr := frontier_closedBall (0 : Plane) one_ne_zero
  have hi : (interior (_root_.Metric.closedBall (0 : Plane) 1)).Nonempty := by
    rw [interior_closedBall (0 : Plane) one_ne_zero]
    exact nonempty_ball.mpr one_pos
  have hreg : closure (inside (_root_.Metric.sphere (0 : Plane) 1)) = _root_.Metric.closedBall 0 1 := by
    simpa only [hfr] using closure_inside_frontier_eq_of_isCompact
      (_root_.ProperSpace.isCompact_closedBall (0 : Plane) 1) (hfr.symm ▸ hs) hi
  obtain ⟨e, he, -⟩ := Homeomorph.exists_image_closed_region_eqOn_compl hΓ hs isOpen_univ
    _root_.PreconnectedSpace.isPreconnected_univ (_root_.Set.subset_univ _) (_root_.Set.subset_univ _)
  rw [hreg] at he
  exact ⟨(e.image _).trans (Homeomorph.setCongr he)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.nonempty_homeomorph_closure_inside then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.nonempty_homeomorph_closure_inside"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.nonempty_homeomorph_closure_inside ``Submission.DifferentialGeometry.Topology.PlanarJordan.nonempty_homeomorph_closure_inside

theorem isTopologicalCell_union_of_isTopologicalCell_inter {A B : Set Plane}
    (hA : Nonempty (A ≃ₜ _root_.Metric.closedBall (0 : Plane) 1))
    (hB : Nonempty (B ≃ₜ _root_.Metric.closedBall (0 : Plane) 1))
    (hAB : Nonempty ((A ∩ B : Set Plane) ≃ₜ _root_.Metric.closedBall (0 : Plane) 1)) :
    Nonempty ((A ∪ B : Set Plane) ≃ₜ _root_.Metric.closedBall (0 : Plane) 1) := by
  classical
  obtain ⟨φA⟩ := hA
  obtain ⟨φB⟩ := hB
  obtain ⟨φC⟩ := hAB
  have hAc := isCompact_of_homeomorphClosedBall φA
  have hBc := isCompact_of_homeomorphClosedBall φB
  have hCcl := (isCompact_of_homeomorphClosedBall φC).isClosed
  have hAcl := hAc.isClosed
  have hBcl := hBc.isClosed
  have hJA := isJordanCurve_frontier_of_homeomorphClosedBall φA
  have hJB := isJordanCurve_frontier_of_homeomorphClosedBall φB
  have hJC := isJordanCurve_frontier_of_homeomorphClosedBall φC
  have hiA := interior_eq_inside_frontier_of_homeomorphClosedBall φA
  have hiB := interior_eq_inside_frontier_of_homeomorphClosedBall φB
  have hiC := interior_eq_inside_frontier_of_homeomorphClosedBall φC
  have hclA : closure (interior A) = A := by
    rw [hiA]
    exact closure_inside_frontier_eq_of_homeomorphClosedBall φA
  have hclB : closure (interior B) = B := by
    rw [hiB]
    exact closure_inside_frontier_eq_of_homeomorphClosedBall φB
  have hintC : interior (A ∩ B) = interior A ∩ interior B := interior_inter
  obtain ⟨f, hfc, hfi, hfim, hffix⟩ := exists_matching_of_inside_subset hJC hJA (by
    rw [← hiC, ← hiA]
    exact interior_mono _root_.Set.inter_subset_left)
  obtain ⟨g, hgc, hgi, hgim, hgfix⟩ := exists_matching_of_inside_subset hJC hJB (by
    rw [← hiC, ← hiB]
    exact interior_mono _root_.Set.inter_subset_right)
  have hScover : ∀ x ∈ frontier (A ∩ B), x ∈ frontier A ∨ x ∈ frontier B := by
    intro x hx
    have hxC : x ∈ A ∩ B := hCcl.frontier_subset hx
    by_contra hcon
    rw [not_or] at hcon
    have hxA : x ∈ interior A := (mem_interior_iff_notMem_frontier hxC.1).mpr hcon.1
    have hxB : x ∈ interior B := (mem_interior_iff_notMem_frontier hxC.2).mpr hcon.2
    apply hx.2
    rw [hintC]
    exact ⟨hxA, hxB⟩
  have hJAC : ∀ z ∈ frontier A, z ∈ A ∩ B → z ∈ frontier (A ∩ B) := by
    intro z hzA hzC
    refine ⟨subset_closure hzC, fun hzi => hzA.2 ?_⟩
    rw [hintC] at hzi
    exact hzi.1
  have hJBC : ∀ z ∈ frontier B, z ∈ A ∩ B → z ∈ frontier (A ∩ B) := by
    intro z hzB hzC
    refine ⟨subset_closure hzC, fun hzi => hzB.2 ?_⟩
    rw [hintC] at hzi
    exact hzi.2
  have hfA : ∀ x ∈ frontier (A ∩ B), f x ∈ frontier A := fun x hx => by
    rw [← hfim]
    exact _root_.Set.mem_image_of_mem f hx
  have hgB : ∀ x ∈ frontier (A ∩ B), g x ∈ frontier B := fun x hx => by
    rw [← hgim]
    exact _root_.Set.mem_image_of_mem g hx
  set S := frontier (A ∩ B) with hS
  set η : Plane → Plane := fun x => if x ∈ frontier A then g x else f x with hη
  have hηA : ∀ x, x ∈ frontier A → η x = g x := fun x hx => if_pos hx
  have hηB : ∀ x ∈ S, x ∈ frontier B → η x = f x := by
    intro x hxS hxB
    by_cases hxA : x ∈ frontier A
    · rw [hηA x hxA, hgfix x ⟨hxS, hxB⟩, hffix x ⟨hxS, hxA⟩]
    · exact if_neg hxA
  have hcov : S ∩ frontier A ∪ S ∩ frontier B = S := by
    apply Subset.antisymm
    · rintro x (hx | hx) <;> exact hx.1
    · intro x hx
      rcases hScover x hx with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hηc : ContinuousOn η S := by
    rw [← hcov]
    refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_frontier.inter isClosed_frontier)
      (isClosed_frontier.inter isClosed_frontier)
    · exact (hgc.mono _root_.Set.inter_subset_left).congr fun x hx => hηA x hx.2
    · exact (hfc.mono _root_.Set.inter_subset_left).congr fun x hx => hηB x hx.1 hx.2
  have hcross : ∀ x ∈ S, ∀ y ∈ S, y ∉ frontier A → g x ≠ f y := by
    intro x hx y hy hyA hxy
    have hzB : f y ∈ frontier B := by
      rw [← hxy]
      exact hgB x hx
    have hzC : f y ∈ A ∩ B := ⟨hAcl.frontier_subset (hfA y hy), hBcl.frontier_subset hzB⟩
    have hzS : f y ∈ S := hJAC _ (hfA y hy) hzC
    have hyz : f y = y := hfi hzS hy (hffix _ ⟨hzS, hfA y hy⟩)
    apply hyA
    rw [← hyz]
    exact hfA y hy
  have hηi : _root_.Set.InjOn η S := by
    intro x hx y hy hxy
    by_cases hxA : x ∈ frontier A <;> by_cases hyA : y ∈ frontier A
    · rw [hηA x hxA, hηA y hyA] at hxy
      exact hgi hx hy hxy
    · rw [hηA x hxA, hηB y hy ((hScover y hy).resolve_left hyA)] at hxy
      exact absurd hxy (hcross x hx y hy hyA)
    · rw [hηB x hx ((hScover x hx).resolve_left hxA), hηA y hyA] at hxy
      exact absurd hxy.symm (hcross y hy x hx hxA)
    · rw [hηB x hx ((hScover x hx).resolve_left hxA),
        hηB y hy ((hScover y hy).resolve_left hyA)] at hxy
      exact hfi hx hy hxy
  have hηim : η '' S = (A ∪ B) \ (interior A ∪ interior B) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases hxA : x ∈ frontier A
      · rw [hηA x hxA]
        have hgx := hgB x hx
        refine ⟨Or.inr (hBcl.frontier_subset hgx), ?_⟩
        rintro (hi | hi)
        · have hgC : g x ∈ A ∩ B := ⟨interior_subset hi, hBcl.frontier_subset hgx⟩
          have hgS := hJBC _ hgx hgC
          have hgxx : g x = x := hgi hgS hx (hgfix _ ⟨hgS, hgx⟩)
          rw [hgxx] at hi
          exact hxA.2 hi
        · exact hgx.2 hi
      · have hxB := (hScover x hx).resolve_left hxA
        rw [hηB x hx hxB]
        have hfx := hfA x hx
        refine ⟨Or.inl (hAcl.frontier_subset hfx), ?_⟩
        rintro (hi | hi)
        · exact hfx.2 hi
        · have hfC : f x ∈ A ∩ B := ⟨hAcl.frontier_subset hfx, interior_subset hi⟩
          have hfS := hJAC _ hfx hfC
          have hfxx : f x = x := hfi hfS hx (hffix _ ⟨hfS, hfx⟩)
          rw [hfxx] at hfx
          exact hxA hfx
    · rintro ⟨hzAB, hzint⟩
      obtain ⟨hzA', hzB'⟩ : z ∉ interior A ∧ z ∉ interior B := not_or.mp hzint
      by_cases hzA : z ∈ A
      · have hzJA : z ∈ frontier A := ⟨subset_closure hzA, hzA'⟩
        by_cases hzB : z ∈ B
        · have hzS := hJAC z hzJA ⟨hzA, hzB⟩
          have hzJB : z ∈ frontier B := ⟨subset_closure hzB, hzB'⟩
          refine ⟨z, hzS, ?_⟩
          rw [hηA z hzJA]
          exact hgfix z ⟨hzS, hzJB⟩
        · rw [← hfim] at hzJA
          obtain ⟨y, hy, hyz⟩ := hzJA
          by_cases hyA : y ∈ frontier A
          · have hyz' : y = z := (hffix y ⟨hy, hyA⟩).symm.trans hyz
            exact absurd (hyz' ▸ (hCcl.frontier_subset hy).2) hzB
          · refine ⟨y, hy, ?_⟩
            rw [hηB y hy ((hScover y hy).resolve_left hyA), hyz]
      · have hzB : z ∈ B := Or.resolve_left hzAB hzA
        have hzJB : z ∈ frontier B := ⟨subset_closure hzB, hzB'⟩
        rw [← hgim] at hzJB
        obtain ⟨y, hy, hyz⟩ := hzJB
        by_cases hyA : y ∈ frontier A
        · refine ⟨y, hy, ?_⟩
          rw [hηA y hyA, hyz]
        · have hyB := (hScover y hy).resolve_left hyA
          have hyz' : y = z := (hgfix y ⟨hy, hyB⟩).symm.trans hyz
          exact absurd (hyz' ▸ (hCcl.frontier_subset hy).1) hzA
  set U := interior A ∪ interior B with hU
  have hUo : IsOpen U := isOpen_interior.union isOpen_interior
  have hclU : closure U = A ∪ B := by rw [closure_union, hclA, hclB]
  have hfrU : frontier U = (A ∪ B) \ U := by rw [hUo.frontier_eq, hclU]
  have hUb : Bornology.IsBounded U :=
    (hAc.union hBc).isBounded.subset (_root_.Set.union_subset_union interior_subset interior_subset)
  have hUne : U.Nonempty :=
    (interior_nonempty_of_homeomorphClosedBall φA).mono _root_.Set.subset_union_left
  obtain ⟨γ, hγ, hγS⟩ := hJC
  have hmaps : _root_.Set.MapsTo γ I S := fun t ht => by
    rw [← hγS]
    exact _root_.Set.mem_image_of_mem γ ht
  have hloop : IsLoop (η ∘ γ) :=
    ⟨hηc.comp hγ.continuousOn hmaps, congrArg η hγ.closes, fun s hs t ht h =>
      hγ.injOn hs ht (hηi (hmaps (_root_.Set.Ico_subset_Icc_self hs)) (hmaps (_root_.Set.Ico_subset_Icc_self ht)) h)⟩
  have hΓ : IsJordanCurve ((A ∪ B) \ U) := ⟨η ∘ γ, hloop, by rw [_root_.Set.image_comp, hγS, hηim]⟩
  have hUin : U = inside ((A ∪ B) \ U) :=
    eq_inside_of_isOpen_isBounded_frontier_subset hΓ hUo hUb hUne hfrU.subset _root_.Set.disjoint_sdiff_right
  obtain ⟨e⟩ := nonempty_homeomorph_closure_inside hΓ
  have heq : closure (inside ((A ∪ B) \ U)) = A ∪ B := by rw [← hUin, hclU]
  exact ⟨(Homeomorph.setCongr heq).symm.trans e⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.isTopologicalCell_union_of_isTopologicalCell_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.isTopologicalCell_union_of_isTopologicalCell_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.isTopologicalCell_union_of_isTopologicalCell_inter ``Submission.DifferentialGeometry.Topology.PlanarJordan.isTopologicalCell_union_of_isTopologicalCell_inter

end DifferentialGeometry.Topology.PlanarJordan

end PlanarUnion

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Leaves

theorem exists_isTopologicalCellWithInterior_union_consecutive
    {P : Fin 4 → EuclideanSpace ℝ (Fin 3)} {D Dint : Fin 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hc : IsPlanarCellChain P D Dint) (j : Fin 2) :
    ∃ Eint : Set (EuclideanSpace ℝ (Fin 3)),
      IsTopologicalCellWithInterior 2 (D j.castSucc ∪ D j.succ) Eint ∧
        Dint j.castSucc ⊆ Eint ∧ Dint j.succ ⊆ Eint := by
  exact exists_isTopologicalCellWithInterior_union_consecutive_of_diskUnion
    (fun hA hB hAB => PlanarJordan.isTopologicalCell_union_of_isTopologicalCell_inter hA hB hAB)
    hc j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isTopologicalCellWithInterior_union_consecutive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isTopologicalCellWithInterior_union_consecutive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isTopologicalCellWithInterior_union_consecutive ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isTopologicalCellWithInterior_union_consecutive

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
