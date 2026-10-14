/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34TubeChain
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceEnvelopes
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Derived

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology _root_.Metric _root_.Submission.Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_mem_forall_notMem_of_finite {𝒮 : Set (Set E3)} (h𝒮 : 𝒮.Finite)
    (hcl : ∀ B ∈ 𝒮, IsClosed B) (hint : ∀ B ∈ 𝒮, interior B = ∅) {O : Set E3} (hO : IsOpen O)
    (hne : O.Nonempty) : ∃ x ∈ O, ∀ B ∈ 𝒮, x ∉ B := by
  have hZ : IsClosed (⋃₀ 𝒮) ∧ interior (⋃₀ 𝒮) = ∅ := by
    induction 𝒮, h𝒮 using Set.Finite.induction_on with
    | empty => simp
    | @insert B 𝒯 _ _ ih =>
      obtain ⟨ihc, ihi⟩ := ih (fun B' hB' => hcl B' (_root_.Set.mem_insert_of_mem _ hB'))
        (fun B' hB' => hint B' (_root_.Set.mem_insert_of_mem _ hB'))
      rw [_root_.Set.sUnion_insert, _root_.Set.union_comm]
      exact ⟨ihc.union (hcl B (_root_.Set.mem_insert _ _)),
        (interior_union_isClosed_of_interior_empty ihc (hint B (_root_.Set.mem_insert _ _))).trans ihi⟩
  by_contra hno
  push Not at hno
  obtain ⟨x, hx⟩ := hne
  have hsub : O ⊆ ⋃₀ 𝒮 := fun y hy => by
    obtain ⟨B, hB, hyB⟩ := hno y hy
    exact ⟨B, hB, hyB⟩
  have := interior_maximal hsub hO hx
  rw [hZ.2] at this
  exact this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_mem_forall_notMem_of_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_mem_forall_notMem_of_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_mem_forall_notMem_of_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_mem_forall_notMem_of_finite

theorem interior_affineSpan_eq_empty {s : Finset E3} (hs : s.card ≤ 3) :
    interior (affineSpan ℝ (s : Set E3) : Set E3) = ∅ := by
  classical
  rcases s.eq_empty_or_nonempty with h0 | hpos
  · subst h0
    simp
  by_contra hne
  rw [← ne_eq, ← _root_.Set.nonempty_iff_ne_empty] at hne
  have htop := affineSpan_eq_top_of_nonempty_interior
    (hne.mono (interior_mono (subset_convexHull ℝ _)))
  rw [AffineSubspace.affineSpan_coe] at htop
  have hdir := congrArg AffineSubspace.direction htop
  rw [direction_affineSpan, AffineSubspace.direction_top] at hdir
  have hfin := congrArg (fun S : Submodule ℝ E3 => Module.finrank ℝ S) hdir
  simp only [finrank_top, finrank_euclideanSpace_fin] at hfin
  obtain ⟨n, hn⟩ : ∃ n, s.card = n + 1 := ⟨s.card - 1, by have := hpos.card_pos; omega⟩
  have hle := finrank_vectorSpan_image_finset_le ℝ (id : E3 → E3) s hn
  rw [Finset.image_id] at hle
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.interior_affineSpan_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.interior_affineSpan_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.interior_affineSpan_eq_empty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.interior_affineSpan_eq_empty

theorem interior_setOf_inner_eq_eq_empty {n : E3} (hn : n ≠ 0) (c : ℝ) :
    interior {x : E3 | _root_.Inner.inner ℝ n x = c} = ∅ := by
  by_contra hne
  rw [← ne_eq, ← _root_.Set.nonempty_iff_ne_empty] at hne
  obtain ⟨y, hy⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hy
  have hnn : 0 < _root_.Inner.inner ℝ n n := real_inner_self_pos.mpr hn
  set t := r / (2 * (‖n‖ + 1)) with ht
  have ht0 : 0 < t := div_pos hr (by positivity)
  have hmem : y + t • n ∈ _root_.Metric.ball y r := by
    rw [_root_.Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0,
      ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg n]
  have h1 := interior_subset (hball hmem)
  have h2 := interior_subset hy
  simp only [_root_.Set.mem_ofPred_eq] at h1 h2
  rw [inner_add_right, real_inner_smul_right, h2] at h1
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.interior_setOf_inner_eq_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.interior_setOf_inner_eq_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.interior_setOf_inner_eq_eq_empty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.interior_setOf_inner_eq_eq_empty

theorem notMem_segment_of_notMem_affineSpan {u v e : E3} (hue : u ≠ e)
    (hv : v ∉ affineSpan ℝ ({u, e} : Set E3)) : e ∉ segment ℝ u v := by
  intro he
  rw [segment_eq_image'] at he
  obtain ⟨t, ⟨ht0, -⟩, heq⟩ := he
  rcases ht0.lt_or_eq with htpos | htz
  · apply hv
    have hv' : v = AffineMap.lineMap u e (1 / t) := by
      rw [AffineMap.lineMap_apply_module', ← heq]
      rw [add_sub_cancel_left, smul_smul, one_div, inv_mul_cancel₀ htpos.ne', one_smul]
      abel
    rw [hv']
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
  · subst htz
    simp only [zero_smul, add_zero] at heq
    exact hue heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.notMem_segment_of_notMem_affineSpan then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.notMem_segment_of_notMem_affineSpan"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.notMem_segment_of_notMem_affineSpan ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.notMem_segment_of_notMem_affineSpan

theorem disjoint_segment_of_notMem_affineSpan {u v e₁ e₂ : E3}
    (hu : u ∉ affineSpan ℝ ({e₁, e₂} : Set E3))
    (hv : v ∉ affineSpan ℝ ({u, e₁, e₂} : Set E3)) :
    Disjoint (segment ℝ u v) (segment ℝ e₁ e₂) := by
  refine Set.disjoint_left.mpr fun x hxuv hxe => ?_
  have hxA : x ∈ affineSpan ℝ ({e₁, e₂} : Set E3) :=
    convexHull_subset_affineSpan _ (by rw [convexHull_pair]; exact hxe)
  rw [segment_eq_image'] at hxuv
  obtain ⟨t, ⟨ht0, -⟩, rfl⟩ := hxuv
  rcases ht0.lt_or_eq with htpos | htz
  · apply hv
    have hsub : affineSpan ℝ ({e₁, e₂} : Set E3) ≤ affineSpan ℝ ({u, e₁, e₂} : Set E3) :=
      affineSpan_mono ℝ (_root_.Set.subset_insert _ _)
    have huA : u ∈ affineSpan ℝ ({u, e₁, e₂} : Set E3) :=
      mem_affineSpan ℝ (_root_.Set.mem_insert _ _)
    have hv' : v = AffineMap.lineMap u (u + t • (v - u)) (1 / t) := by
      rw [AffineMap.lineMap_apply_module', add_sub_cancel_left, smul_smul, one_div,
        inv_mul_cancel₀ htpos.ne', one_smul]
      abel
    rw [hv']
    exact AffineMap.lineMap_mem _ huA (hsub hxA)
  · subst htz
    simp only [zero_smul, add_zero] at hxA
    exact hu hxA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_segment_of_notMem_affineSpan then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.disjoint_segment_of_notMem_affineSpan"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_segment_of_notMem_affineSpan ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.disjoint_segment_of_notMem_affineSpan

theorem card_le_three_of_interior_eq_empty (L : Geometry.SimplicialComplex ℝ E3)
    (hint : interior L.space = ∅) {σ : Finset E3} (hσ : σ ∈ L.faces) : σ.card ≤ 3 := by
  have hind := L.indep hσ
  have hle := hind.card_le_finrank_succ
  have hle2 := (vectorSpan ℝ (_root_.Set.range ((↑) : σ → E3))).finrank_le
  rw [Fintype.card_coe] at hle
  rw [finrank_euclideanSpace_fin] at hle2
  by_contra hgt
  have h4 : σ.card = Module.finrank ℝ E3 + 1 := by
    rw [finrank_euclideanSpace_fin]
    omega
  have hne : σ.Nonempty := Finset.card_pos.mp (by omega)
  have hopen := interior_convexHull_eq_openSimplex hind h4
  have hmem : σ.centroid ℝ id ∈ interior L.space :=
    interior_mono (L.convexHull_subset_space hσ) (hopen ▸ centroid_mem_openSimplex hne)
  rw [hint] at hmem
  exact hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.card_le_three_of_interior_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.card_le_three_of_interior_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.card_le_three_of_interior_eq_empty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.card_le_three_of_interior_eq_empty

theorem exists_card_eq_three_inter_ball_subset (L : Geometry.SimplicialComplex ℝ E3)
    [Finite L.faces] (hint : interior L.space = ∅) {p q x : E3} (hx : x ∈ L.space)
    (hxs : x ∈ segment ℝ p q)
    (hedge : ∀ σ ∈ L.faces, σ.card ≤ 2 → Disjoint (segment ℝ p q) (convexHull ℝ (σ : Set E3))) :
    ∃ τ ∈ L.faces, τ.card = 3 ∧ x ∈ convexHull ℝ (τ : Set E3) ∧
      ∃ ρ > 0, L.space ∩ _root_.Metric.ball x ρ ⊆ convexHull ℝ (τ : Set E3) := by
  classical
  obtain ⟨τ, hτ, hxτ⟩ := exists_face_mem_openSimplex L hx
  have hxτc : x ∈ convexHull ℝ (τ : Set E3) := openSimplex_subset_convexHull τ hxτ
  have hτ3 : τ.card = 3 := by
    have hle := card_le_three_of_interior_eq_empty L hint hτ
    by_contra hne
    exact Set.disjoint_left.mp (hedge τ hτ (by omega)) hxs hxτc
  set far := ⋃ σ ∈ {σ ∈ L.faces | x ∉ convexHull ℝ (σ : Set E3)}, convexHull ℝ (σ : Set E3)
    with hfar
  have hfarc : IsClosed far := by
    have hfin : {σ ∈ L.faces | x ∉ convexHull ℝ (σ : Set E3)}.Finite :=
      (Set.toFinite L.faces).subset fun σ hσ => hσ.1
    exact hfin.isClosed_biUnion fun σ _ =>
      (σ.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed
  have hxfar : x ∉ far := by
    intro h
    obtain ⟨σ, hσ, hxσ⟩ := mem_iUnion₂.mp h
    exact hσ.2 hxσ
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hfarc.isOpen_compl x hxfar
  refine ⟨τ, hτ, hτ3, hxτc, ρ, hρ, ?_⟩
  rintro y ⟨hyL, hyb⟩
  obtain ⟨σ, hσ, hyσ⟩ := L.mem_space_iff.mp hyL
  have hxσ : x ∈ convexHull ℝ (σ : Set E3) := by
    by_contra hxσ
    exact hρsub hyb (mem_iUnion₂.mpr ⟨σ, ⟨hσ, hxσ⟩, hyσ⟩)
  have hτσ := face_subset_of_mem_openSimplex_of_mem_convexHull L hτ hσ hxτ hxσ
  have hσ3 := card_le_three_of_interior_eq_empty L hint hσ
  have heq : τ = σ := Finset.eq_of_subset_of_card_le hτσ (by omega)
  rw [heq]
  exact hyσ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_card_eq_three_inter_ball_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_card_eq_three_inter_ball_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_card_eq_three_inter_ball_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_card_eq_three_inter_ball_subset

theorem inter_ball_eq_of_frontier_subset_plane {X : Set E3} {a n q : E3} {ρ : ℝ}
    (hXc : IsClosed X) (hXcl : closure (interior X) = X) (ha : a ∈ frontier X) (hn : n ≠ 0)
    (hfr : frontier X ∩ _root_.Metric.ball a ρ ⊆ {x | _root_.Inner.inner ℝ n (x - a) = 0}) (hq : q ∈ _root_.Metric.ball a ρ)
    (hqn : 0 < _root_.Inner.inner ℝ n (q - a)) (hqX : q ∉ X) :
    X ∩ _root_.Metric.ball a ρ = {x | _root_.Inner.inner ℝ n (x - a) ≤ 0} ∩ _root_.Metric.ball a ρ := by
  have hcont : Continuous fun x : E3 => _root_.Inner.inner ℝ n (x - a) :=
    continuous_const.inner (continuous_id.sub continuous_const)
  set Hp := {x : E3 | 0 < _root_.Inner.inner ℝ n (x - a)} ∩ _root_.Metric.ball a ρ with hHp
  set Hm := {x : E3 | _root_.Inner.inner ℝ n (x - a) < 0} ∩ _root_.Metric.ball a ρ with hHm
  have hHpc : IsPreconnected Hp := by
    have h1 : {x : E3 | 0 < _root_.Inner.inner ℝ n (x - a)} = {x | _root_.Inner.inner ℝ n a < innerₗ E3 n x} := by
      ext x
      simp only [_root_.Set.mem_ofPred_eq, innerₗ_apply_apply, inner_sub_right, sub_pos]
    rw [hHp, h1]
    exact ((convex_halfSpace_gt (innerₗ E3 n).isLinear _).inter (convex_ball a ρ)).isPreconnected
  have hHmc : IsPreconnected Hm := by
    have h1 : {x : E3 | _root_.Inner.inner ℝ n (x - a) < 0} = {x | innerₗ E3 n x < _root_.Inner.inner ℝ n a} := by
      ext x
      simp only [_root_.Set.mem_ofPred_eq, innerₗ_apply_apply, inner_sub_right, sub_neg]
    rw [hHm, h1]
    exact ((convex_halfSpace_lt (innerₗ E3 n).isLinear _).inter (convex_ball a ρ)).isPreconnected
  have hdisj : ∀ H ⊆ _root_.Metric.ball a ρ, H ⊆ {x | _root_.Inner.inner ℝ n (x - a) ≠ 0} → Disjoint H (frontier X) :=
    fun H hHb hH0 => Set.disjoint_left.mpr fun x hxH hxF =>
      hH0 hxH (hfr ⟨hxF, hHb hxH⟩)
  have hHpX : Hp ⊆ Xᶜ := by
    rcases subset_interior_or_subset_compl_of_disjoint_frontier hXc hHpc
      (hdisj Hp _root_.Set.inter_subset_right fun x hx => hx.1.ne') with h | h
    · exact absurd (interior_subset (h ⟨hqn, hq⟩)) hqX
    · exact h
  have hHmX : Hm ⊆ interior X := by
    rcases subset_interior_or_subset_compl_of_disjoint_frontier hXc hHmc
      (hdisj Hm _root_.Set.inter_subset_right fun x hx => hx.1.ne) with h | h
    · exact h
    · exfalso
      have haint : a ∈ closure (interior X) := by rw [hXcl]; exact hXc.frontier_subset ha
      obtain ⟨y, hyb, hyint⟩ := mem_closure_iff.mp haint (_root_.Metric.ball a ρ) _root_.Metric.isOpen_ball
        (_root_.Metric.mem_ball_self (_root_.Metric.pos_of_mem_ball hq))
      have hy0 : _root_.Inner.inner ℝ n (y - a) = 0 := by
        rcases lt_trichotomy (_root_.Inner.inner ℝ n (y - a)) 0 with h' | h' | h'
        · exact absurd (interior_subset hyint) (h ⟨h', hyb⟩)
        · exact h'
        · exact absurd (interior_subset hyint) (hHpX ⟨h', hyb⟩)
      obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp (isOpen_interior.inter _root_.Metric.isOpen_ball) y
        ⟨hyint, hyb⟩
      have hnn : 0 < _root_.Inner.inner ℝ n n := real_inner_self_pos.mpr hn
      set t := r / (2 * (‖n‖ + 1)) with ht
      have ht0 : 0 < t := div_pos hr (by positivity)
      have hmem : y - t • n ∈ _root_.Metric.ball y r := by
        rw [_root_.Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_pos ht0, ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg n]
      obtain ⟨hmint, hmb⟩ := hrsub hmem
      have hneg : _root_.Inner.inner ℝ n (y - t • n - a) < 0 := by
        have : y - t • n - a = (y - a) - t • n := by abel
        rw [this, inner_sub_right, hy0, real_inner_smul_right]
        nlinarith
      exact h ⟨hneg, hmb⟩ (interior_subset hmint)
  ext x
  constructor
  · rintro ⟨hxX, hxb⟩
    refine ⟨?_, hxb⟩
    change _root_.Inner.inner ℝ n (x - a) ≤ 0
    by_contra hpos
    push Not at hpos
    exact hHpX ⟨hpos, hxb⟩ hxX
  · rintro ⟨hle, hxb⟩
    change _root_.Inner.inner ℝ n (x - a) ≤ 0 at hle
    refine ⟨?_, hxb⟩
    rcases hle.lt_or_eq with hlt | heq
    · exact interior_subset (hHmX ⟨hlt, hxb⟩)
    · rw [← hXc.closure_eq]
      have hnn : 0 < _root_.Inner.inner ℝ n n := real_inner_self_pos.mpr hn
      have hdx : 0 < ρ - _root_.Dist.dist x a := sub_pos.mpr (mem_ball.mp hxb)
      refine mem_closure_iff.mpr fun U hU hxU => ?_
      obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hxU
      set t := _root_.Min.min r (ρ - _root_.Dist.dist x a) / (2 * (‖n‖ + 1)) with ht
      have ht0 : 0 < t := div_pos (lt_min hr hdx) (by positivity)
      have hdist : _root_.Dist.dist (x - t • n) x < _root_.Min.min r (ρ - _root_.Dist.dist x a) := by
        rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_pos ht0, ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg n, lt_min hr hdx]
      have hmb : x - t • n ∈ _root_.Metric.ball a ρ := by
        rw [_root_.Metric.mem_ball]
        have := dist_triangle (x - t • n) x a
        have := min_le_right r (ρ - _root_.Dist.dist x a)
        linarith
      have hneg : _root_.Inner.inner ℝ n (x - t • n - a) < 0 := by
        have : x - t • n - a = (x - a) - t • n := by abel
        rw [this, inner_sub_right, heq, real_inner_smul_right]
        nlinarith
      exact ⟨x - t • n, hrU (lt_of_lt_of_le hdist (min_le_left _ _)),
        interior_subset (hHmX ⟨hneg, hmb⟩)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.inter_ball_eq_of_frontier_subset_plane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.inter_ball_eq_of_frontier_subset_plane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.inter_ball_eq_of_frontier_subset_plane ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.inter_ball_eq_of_frontier_subset_plane

end DifferentialGeometry.Topology.PiecewiseLinear
