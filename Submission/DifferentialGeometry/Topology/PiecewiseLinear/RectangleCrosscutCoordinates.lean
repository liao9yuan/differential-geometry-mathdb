/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscutPair
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallGluingTwo
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem exists_rectangle_eq_on_boundary_arc
    {D A : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D)
    {η : ℝ → E} (hη : IsPLHomeomorphOn η (_root_.Set.Icc 0 1) A)
    (hAbd : A ⊆ r '' stdSimplexBoundary 2)
    {a b c : ℝ} (hab : a < b) (hc : c = a ∨ c = b) :
    ∃ f : ℝ × ℝ → E, IsPLHomeomorphOn f (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc a b) D ∧
      ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, f (t, c) = η t := by
  classical
  let _ : DecidableEq (ℝ × ℝ) := Classical.decEq _
  let _ : DecidableEq E := Classical.decEq _
  have hI : IsPLBall 1 (_root_.Set.Icc (0 : ℝ) 1) := isPLBall_Icc zero_lt_one
  have hP : IsPLBall 2 (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc a b) :=
    isPLBall_two_prod hI (isPLBall_Icc hab)
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  obtain ⟨K, hKfin, hKspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hLfin, hLspace⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hK : IsPLBall 2 K.space := hKspace.symm ▸ hP
  have hL : IsPLBall 2 L.space := hLspace.symm ▸ hD
  have hside : _root_.Set.Icc (0 : ℝ) 1 ×ˢ {c} ⊆ (boundaryComplex 2 K).space := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank
      (by simp [Module.finrank_prod]) K hK.isCombinatorialManifoldWithBoundary, hKspace,
      frontier_prod_eq, isClosed_Icc.closure_eq, frontier_Icc hab.le]
    exact fun z hz => Or.inl ⟨hz.1, (show z.2 = c from hz.2).symm ▸ hc⟩
  have hAL : A ⊆ (boundaryComplex 2 L).space :=
    hAbd.trans (hr.image_stdSimplexBoundary_eq_boundaryComplex L hLspace).subset
  have hg : IsPLHomeomorphOn (η ∘ Prod.fst) (_root_.Set.Icc (0 : ℝ) 1 ×ˢ {c}) A :=
    (hI.isPolyhedron.isPLHomeomorphOn_fst_prod_const c).trans hη
  obtain ⟨f, hf, hfg⟩ := exists_isPLHomeomorphOn_eqOn_arc_of_boundaryComplex_of_ambient
    K L hK hL (hI.of_isPLHomeomorphOn
      (hI.isPolyhedron.isPLHomeomorphOn_prod_const c)) hside hg hAL
  rw [hKspace, hLspace] at hf
  exact ⟨f, hf, fun t ht => hfg ⟨ht, rfl⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_rectangle_eq_on_boundary_arc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.exists_rectangle_eq_on_boundary_arc target :: scope.openDecls } }

theorem exists_isPLHomeomorphOn_rectangle_eq_on_crosscut
    {D A : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D)
    {η : ℝ → E} (hη : IsPLHomeomorphOn η (_root_.Set.Icc 0 1) A) (hAD : A ⊆ D)
    (hmeet : A ∩ (r '' stdSimplexBoundary 2) = {η 0, η 1}) :
    ∃ g : ℝ × ℝ → E,
      IsPLHomeomorphOn g (_root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (-1 : ℝ) 1) D ∧
      ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, g (t, 0) = η t := by
  classical
  obtain ⟨U, V, R, S, u, v, γ, δ, hu, hv, -, -, -, -, -, -, hUV, hUiV,
      huBd, hvBd, -, -, -, -⟩ :=
    exists_disk_pair_with_boundary_arcs_of_proper_arc hr hη hAD hmeet
  have hAU : A ⊆ u '' stdSimplexBoundary 2 := subset_union_left.trans huBd.symm.subset
  have hAV : A ⊆ v '' stdSimplexBoundary 2 := subset_union_left.trans hvBd.symm.subset
  obtain ⟨f₀, hf₀, hf₀η⟩ := exists_rectangle_eq_on_boundary_arc hu hη hAU
    (by norm_num : (-1 : ℝ) < 0) (Or.inr rfl)
  obtain ⟨f₁, hf₁, hf₁η⟩ := exists_rectangle_eq_on_boundary_arc hv hη hAV
    (by norm_num : (0 : ℝ) < 1) (Or.inl rfl)
  let P₀ : Set (ℝ × ℝ) := _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (-1 : ℝ) 0
  let P₁ : Set (ℝ × ℝ) := _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1
  have hP₀ : IsPolyhedron P₀ := isHPolytope_Icc.isPolyhedron.prod
    isHPolytope_Icc.isPolyhedron
  have hP₁ : IsPolyhedron P₁ := isHPolytope_Icc.isPolyhedron.prod
    isHPolytope_Icc.isPolyhedron
  have hmid : P₀ ∩ P₁ = _root_.Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} := by
    ext ⟨x, t⟩
    constructor
    · rintro ⟨⟨hx, -, ht0⟩, ⟨-, h0t, -⟩⟩
      exact ⟨hx, le_antisymm ht0 h0t⟩
    · rintro ⟨hx, ht⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨⟨hx, by norm_num⟩, hx, by norm_num⟩
  have heq : _root_.Set.EqOn f₀ f₁ (P₀ ∩ P₁) := by
    intro z hz
    obtain ⟨hx, ht⟩ := hmid.subset hz
    have hz0 : z = (z.1, (0 : ℝ)) := Prod.ext rfl ht
    rw [hz0, hf₀η z.1 hx, hf₁η z.1 hx]
  have him : f₀ '' (P₀ ∩ P₁) = U ∩ V := by
    rw [hUiV, hmid]
    have heqη : _root_.Set.EqOn f₀ (η ∘ Prod.fst) (_root_.Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}) := by
      rintro ⟨x, t⟩ ⟨hx, ht⟩
      have ht0 : t = 0 := ht
      subst t
      exact hf₀η x hx
    rw [heqη.image_eq, _root_.Set.image_comp, _root_.Set.fst_image_prod]
    · exact hη.image_eq
    · exact _root_.Set.singleton_nonempty _
  have hcover : P₀ ∪ P₁ = _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (-1 : ℝ) 1 := by
    ext ⟨x, t⟩
    constructor
    · rintro (⟨hx, hlow, hhigh⟩ | ⟨hx, hlow, hhigh⟩)
      · exact ⟨hx, hlow, hhigh.trans (by norm_num)⟩
      · exact ⟨hx, (by norm_num : (-1 : ℝ) ≤ 0).trans hlow, hhigh⟩
    · rintro ⟨hx, hlow, hhigh⟩
      rcases le_total t 0 with ht | ht
      · exact Or.inl ⟨hx, hlow, ht⟩
      · exact Or.inr ⟨hx, ht, hhigh⟩
  let _ : DecidablePred (· ∈ P₀) := fun _ => Classical.propDecidable _
  have hg := hf₀.piecewise hf₁ hP₀ hP₁ heq him
  rw [hcover, hUV] at hg
  refine ⟨P₀.piecewise f₀ f₁, hg, fun t ht => ?_⟩
  rw [P₀.piecewise_eq_of_mem f₀ f₁ (show (t, (0 : ℝ)) ∈ P₀ from ⟨ht, by norm_num⟩)]
  exact hf₀η t ht

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_rectangle_eq_on_crosscut with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_rectangle_eq_on_crosscut"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_rectangle_eq_on_crosscut ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_rectangle_eq_on_crosscut

end DifferentialGeometry.Topology.PiecewiseLinear
