/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CircleAnnulusOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem isPLHomeomorphOn_half_sub :
    IsPLHomeomorphOn (fun s : ℝ => 1 / 2 - s) (_root_.Set.Icc 0 (1 / 2)) (_root_.Set.Icc 0 (1 / 2)) := by
  have hpl : IsPiecewiseAffineOn (fun s : ℝ => 1 / 2 - s) (_root_.Set.Icc 0 (1 / 2)) :=
    isPiecewiseAffineOn_of_affine_of_isHPolytope
      (AffineMap.const ℝ ℝ (1 / 2) - AffineMap.id ℝ ℝ) isHPolytope_Icc
  refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
    isHPolytope_Icc.isPolyhedron hpl ⟨?_, ?_, ?_⟩
  · intro s hs
    constructor <;> linarith [hs.1, hs.2]
  · intro s _ t _ hst
    linarith
  · intro t ht
    refine ⟨1 / 2 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_half_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_half_sub target :: scope.openDecls } }

private theorem isPLHomeomorphOn_sub_half :
    IsPLHomeomorphOn (fun s : ℝ => s - 1 / 2) (_root_.Set.Icc (1 / 2) 1) (_root_.Set.Icc 0 (1 / 2)) := by
  have hpl : IsPiecewiseAffineOn (fun s : ℝ => s - 1 / 2) (_root_.Set.Icc (1 / 2) 1) :=
    isPiecewiseAffineOn_of_affine_of_isHPolytope
      (AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ (1 / 2)) isHPolytope_Icc
  refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
    isHPolytope_Icc.isPolyhedron hpl ⟨?_, ?_, ?_⟩
  · intro s hs
    constructor <;> linarith [hs.1, hs.2]
  · intro s _ t _ hst
    linarith
  · intro t ht
    refine ⟨t + 1 / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_sub_half
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_sub_half target :: scope.openDecls } }

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem exists_isPLHomeomorphOn_flip_arc_of_exchange
    {A B : Set E} {γ δ : ℝ → E} (hγ : IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) A)
    (hδ : IsPLHomeomorphOn δ (_root_.Set.Icc 0 1) B) (hδ0 : δ 0 = γ 0)
    (hinter : A ∩ B = {γ 0, γ 1}) {r : E → E}
    (hrγ : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, r (γ t) = δ t)
    (hrδ : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, r (δ t) = γ t) :
    ∃ (C : Set E) (ε : ℝ → E), IsPLHomeomorphOn ε (_root_.Set.Icc 0 1) C ∧ C ⊆ A ∪ B ∧
      ∀ s ∈ _root_.Set.Icc (0 : ℝ) 1, r (ε s) = ε (1 - s) := by
  have hhalfSub : _root_.Set.Icc (0 : ℝ) (1 / 2) ⊆ _root_.Set.Icc (0 : ℝ) 1 :=
    fun _ hx => ⟨hx.1, hx.2.trans (by norm_num)⟩
  have hγhalf := hγ.restrict isHPolytope_Icc.isPolyhedron hhalfSub
  have hδhalf := hδ.restrict isHPolytope_Icc.isPolyhedron hhalfSub
  have hleft := isPLHomeomorphOn_half_sub.trans hγhalf
  have hright := isPLHomeomorphOn_sub_half.trans hδhalf
  have hmeet : _root_.Set.Icc (0 : ℝ) (1 / 2) ∩ _root_.Set.Icc (1 / 2 : ℝ) 1 = {1 / 2} := by
    ext s
    simp only [_root_.Set.mem_inter_iff, _root_.Set.mem_Icc, _root_.Set.mem_singleton_iff]
    constructor
    · rintro ⟨hs, ht⟩
      linarith [hs.2, ht.1]
    · rintro rfl
      norm_num
  have himg : (γ '' _root_.Set.Icc (0 : ℝ) (1 / 2)) ∩ (δ '' _root_.Set.Icc (0 : ℝ) (1 / 2)) = {γ 0} := by
    ext x
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, ⟨t, ht, hts⟩⟩
      have hx : γ s ∈ A ∩ B :=
        ⟨hγ.bijOn.mapsTo (hhalfSub hs), hts ▸ hδ.bijOn.mapsTo (hhalfSub ht)⟩
      rw [hinter] at hx
      rcases hx with hzero | hone
      · exact hzero
      · have hsone : s = 1 := hγ.bijOn.injOn (hhalfSub hs) (by norm_num) hone
        linarith [hs.2]
    · intro hx
      have hx0 : x = γ 0 := hx
      subst x
      exact ⟨⟨0, by norm_num, rfl⟩, ⟨0, by norm_num, hδ0⟩⟩
  have heq : _root_.Set.EqOn (γ ∘ fun s : ℝ => 1 / 2 - s) (δ ∘ fun s : ℝ => s - 1 / 2)
      (_root_.Set.Icc (0 : ℝ) (1 / 2) ∩ _root_.Set.Icc (1 / 2 : ℝ) 1) := by
    intro s hs
    have hs' : s = 1 / 2 := hmeet.subset hs
    rw [hs']
    simpa only [Function.comp_apply, sub_self] using hδ0.symm
  have hsurj : _root_.Set.SurjOn (γ ∘ fun s : ℝ => 1 / 2 - s)
      (_root_.Set.Icc (0 : ℝ) (1 / 2) ∩ _root_.Set.Icc (1 / 2 : ℝ) 1)
      ((γ '' _root_.Set.Icc (0 : ℝ) (1 / 2)) ∩ (δ '' _root_.Set.Icc (0 : ℝ) (1 / 2))) := by
    rw [himg]
    intro x hx
    have hx' : x = γ 0 := hx
    refine ⟨1 / 2, hmeet.symm.subset rfl, ?_⟩
    simpa only [Function.comp_apply, sub_self] using hx'.symm
  obtain ⟨ε, hε, hεleft, hεright⟩ := exists_isPLHomeomorphOn_union
    isHPolytope_Icc.isPolyhedron isHPolytope_Icc.isPolyhedron hleft hright heq hsurj
  have hcover : _root_.Set.Icc (0 : ℝ) (1 / 2) ∪ _root_.Set.Icc (1 / 2 : ℝ) 1 = _root_.Set.Icc (0 : ℝ) 1 := by
    ext s
    simp only [_root_.Set.mem_union, _root_.Set.mem_Icc]
    constructor
    · rintro (hs | hs)
      · exact ⟨hs.1, by linarith [hs.2]⟩
      · exact ⟨by linarith [hs.1], hs.2⟩
    · intro hs
      by_cases hle : s ≤ 1 / 2
      · exact Or.inl ⟨hs.1, hle⟩
      · exact Or.inr ⟨le_of_not_ge hle, hs.2⟩
  rw [hcover] at hε
  refine ⟨_, ε, hε, ?_, ?_⟩
  · intro x hx
    rcases hx with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · exact Or.inl (hγ.bijOn.mapsTo (hhalfSub hs))
    · exact Or.inr (hδ.bijOn.mapsTo (hhalfSub hs))
  · intro s hs
    by_cases hle : s ≤ 1 / 2
    · have hsleft : s ∈ _root_.Set.Icc (0 : ℝ) (1 / 2) := ⟨hs.1, hle⟩
      have hflipright : 1 - s ∈ _root_.Set.Icc (1 / 2 : ℝ) 1 :=
        ⟨by linarith, by linarith [hs.1]⟩
      rw [hεleft hsleft, hεright hflipright]
      change r (γ (1 / 2 - s)) = δ ((1 - s) - 1 / 2)
      rw [hrγ (1 / 2 - s) ⟨by linarith, by linarith [hs.1]⟩]
      congr 1
      ring
    · have hsright : s ∈ _root_.Set.Icc (1 / 2 : ℝ) 1 := ⟨le_of_not_ge hle, hs.2⟩
      have hflipleft : 1 - s ∈ _root_.Set.Icc (0 : ℝ) (1 / 2) :=
        ⟨by linarith [hs.2], by linarith⟩
      rw [hεright hsright, hεleft hflipleft]
      change r (δ (s - 1 / 2)) = γ (1 / 2 - (1 - s))
      rw [hrδ (s - 1 / 2) ⟨by linarith, by linarith [hs.2]⟩]
      congr 1
      ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_flip_arc_of_exchange
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_flip_arc_of_exchange target :: scope.openDecls } }

theorem exists_isPLHomeomorphOn_reflection_arc {S : Set E} (hS : IsPLSphere 1 S) :
    ∃ (r : E → E) (A : Set E) (γ : ℝ → E),
      IsPLHomeomorphOn r S S ∧ ¬ IsPLCirclePositive S r ∧
        (∀ x ∈ S, r (r x) = x) ∧ IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) A ∧ A ⊆ S ∧
        ∀ s ∈ _root_.Set.Icc (0 : ℝ) 1, r (γ s) = γ (1 - s) := by
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_pair_ne_of_isPLSphere_one hS
  obtain ⟨A, B, γ, δ, hγ, hδ, hγ0, hγ1, hδ0, hδ1, hunion, hinter⟩ :=
    exists_arc_decomposition_of_isPLSphere_one hS hp hq hpq
  have hδγ0 : δ 0 = γ 0 := hδ0.trans hγ0.symm
  have hδγ1 : δ 1 = γ 1 := hδ1.trans hγ1.symm
  have hinter' : A ∩ B = {γ 0, γ 1} := by rw [hinter, hγ0, hγ1]
  obtain ⟨r, hr, hneg, hrγ, hrδ, hinvol⟩ :=
    exists_isPLHomeomorphOn_reflection_of_arc_decomposition hγ hδ hδγ0 hδγ1 hunion hinter'
  obtain ⟨C, ε, hε, hC, hflip⟩ :=
    exists_isPLHomeomorphOn_flip_arc_of_exchange hγ hδ hδγ0 hinter' hrγ hrδ
  exact ⟨r, C, ε, hr, hneg, hinvol, hε, hunion ▸ hC, hflip⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_reflection_arc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_reflection_arc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_reflection_arc ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_reflection_arc

end DifferentialGeometry.Topology.PiecewiseLinear
