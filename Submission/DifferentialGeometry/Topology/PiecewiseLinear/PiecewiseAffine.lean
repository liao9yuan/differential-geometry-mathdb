/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Polytope
import Mathlib.Topology.OpenPartialHomeomorph.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology _root_.Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

def IsPiecewiseAffineWithinAt (f : E → F) (s : Set E) (x : E) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (C : ι → Set E) (A : ι → E →ᵃ[ℝ] F),
    (∀ i, IsHPolytope (C i) ∧ C i ⊆ s ∧ _root_.Set.EqOn f (A i) (C i)) ∧ (⋃ i, C i) ∈ 𝓝[s] x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt

def IsPiecewiseAffineOn (f : E → F) (s : Set E) : Prop :=
  ∀ x ∈ s, IsPiecewiseAffineWithinAt f s x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn

theorem interior_iUnion_eq_empty_of_finite {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {C : ι → Set X} (hC : ∀ i, IsClosed (C i)) (h : ∀ i, interior (C i) = ∅) :
    interior (⋃ i, C i) = ∅ := by
  classical
  cases nonempty_fintype ι
  have key : ∀ s : Finset ι, interior (⋃ i ∈ s, C i) = ∅ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s _ ih =>
      rw [Finset.set_biUnion_insert, interior_union_isClosed_of_interior_empty (hC a) ih, h a]
  simpa using key Finset.univ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.interior_iUnion_eq_empty_of_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.interior_iUnion_eq_empty_of_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.interior_iUnion_eq_empty_of_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.interior_iUnion_eq_empty_of_finite

theorem iUnion_interior_nonempty_mem_nhds {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {C : ι → Set X} (hC : ∀ i, IsClosed (C i)) {x : X} (hx : (⋃ i, C i) ∈ 𝓝 x) :
    (⋃ i : {i // (interior (C i)).Nonempty}, C i) ∈ 𝓝 x := by
  have hK : IsClosed (⋃ i : {i // (interior (C i)).Nonempty}, C i) :=
    isClosed_iUnion_of_finite fun i => hC i
  have hD : interior (⋃ i : {i // ¬ (interior (C i)).Nonempty}, C i) = ∅ :=
    interior_iUnion_eq_empty_of_finite (fun i => hC i)
      fun i => Set.not_nonempty_iff_eq_empty.mp i.2
  obtain ⟨N, hNsub, hNopen, hxN⟩ := mem_nhds_iff.mp hx
  refine mem_nhds_iff.mpr ⟨N, ?_, hNopen, hxN⟩
  intro y hy
  by_contra hyK
  have hW : IsOpen (N \ ⋃ i : {i // (interior (C i)).Nonempty}, C i) := hNopen.sdiff hK
  have hWsub : N \ (⋃ i : {i // (interior (C i)).Nonempty}, C i) ⊆
      ⋃ i : {i // ¬ (interior (C i)).Nonempty}, C i := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hNsub hz.1)
    by_cases hint : (interior (C i)).Nonempty
    · exact absurd (mem_iUnion.mpr ⟨⟨i, hint⟩, hi⟩) hz.2
    · exact mem_iUnion.mpr ⟨⟨i, hint⟩, hi⟩
  have hmem : y ∈ interior (⋃ i : {i // ¬ (interior (C i)).Nonempty}, C i) :=
    interior_maximal hWsub hW ⟨hy, hyK⟩
  rw [hD] at hmem
  exact hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.iUnion_interior_nonempty_mem_nhds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.iUnion_interior_nonempty_mem_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.iUnion_interior_nonempty_mem_nhds ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.iUnion_interior_nonempty_mem_nhds

theorem linear_injective_of_injOn_of_interior_nonempty {A : E →ᵃ[ℝ] F} {C : Set E}
    (hA : _root_.Set.InjOn A C) (hC : (interior C).Nonempty) : Function.Injective A.linear := by
  obtain ⟨x₀, hx₀⟩ := hC
  intro v w hvw
  have hker : A.linear (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  by_contra hne
  have hne' : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hcont : ContinuousAt (fun t : ℝ => x₀ + t • (v - w)) 0 := by fun_prop
  have hmem : {t : ℝ | x₀ + t • (v - w) ∈ interior C} ∈ 𝓝 (0 : ℝ) :=
    hcont.preimage_mem_nhds (by simpa using isOpen_interior.mem_nhds hx₀)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmem
  set t : ℝ := ε / 2 with ht_def
  have htne : t ≠ 0 := by positivity
  have ht : x₀ + t • (v - w) ∈ interior C := by
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hval : A (x₀ + t • (v - w)) = A x₀ := by
    have h := A.map_vadd x₀ (t • (v - w))
    rw [vadd_eq_add, vadd_eq_add, map_smul, hker, smul_zero, zero_add, add_comm] at h
    exact h
  have heq : x₀ + t • (v - w) = x₀ := hA (interior_subset ht) (interior_subset hx₀) hval
  have hzero : t • (v - w) = 0 := by simpa using heq
  rcases smul_eq_zero.mp hzero with h | h
  · exact htne h
  · exact hne' h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.linear_injective_of_injOn_of_interior_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.linear_injective_of_injOn_of_interior_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.linear_injective_of_injOn_of_interior_nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.linear_injective_of_injOn_of_interior_nonempty

namespace IsPiecewiseAffineWithinAt

variable {f : E → F} {s t : Set E} {x : E}

theorem congr (hf : IsPiecewiseAffineWithinAt f s x) {g : E → F} (hfg : _root_.Set.EqOn g f s) :
    IsPiecewiseAffineWithinAt g s x := by
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hf
  exact ⟨ι, hι, C, A, fun i => ⟨(hC i).1, (hC i).2.1,
    fun y hy => (hfg ((hC i).2.1 hy)).trans ((hC i).2.2 hy)⟩, hCx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.congr ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.congr

theorem inter_of_mem_nhds [FiniteDimensional ℝ E] (hf : IsPiecewiseAffineWithinAt f s x)
    (ht : t ∈ 𝓝 x) : IsPiecewiseAffineWithinAt f (s ∩ t) x := by
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hf
  have := hι
  obtain ⟨Q, hQ, hQt, hQx⟩ := exists_isHPolytope_subset_mem_nhds ht
  refine ⟨ι, inferInstance, fun i => C i ∩ Q, A, fun i => ⟨(hC i).1.inter hQ,
    _root_.Set.inter_subset_inter (hC i).2.1 hQt, (hC i).2.2.mono inter_subset_left⟩, ?_⟩
  rw [← _root_.Set.iUnion_inter]
  exact _root_.Filter.inter_mem (nhdsWithin_mono x _root_.Set.inter_subset_left hCx) (mem_nhdsWithin_of_mem_nhds hQx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.inter_of_mem_nhds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.inter_of_mem_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.inter_of_mem_nhds ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.inter_of_mem_nhds

theorem of_inter_of_mem_nhds (hf : IsPiecewiseAffineWithinAt f (s ∩ t) x) (ht : t ∈ 𝓝 x) :
    IsPiecewiseAffineWithinAt f s x := by
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hf
  refine ⟨ι, hι, C, A, fun i => ⟨(hC i).1, (hC i).2.1.trans _root_.Set.inter_subset_left, (hC i).2.2⟩, ?_⟩
  rwa [nhdsWithin_restrict' s ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.of_inter_of_mem_nhds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.of_inter_of_mem_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.of_inter_of_mem_nhds ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.of_inter_of_mem_nhds

theorem continuousWithinAt [FiniteDimensional ℝ E] (hf : IsPiecewiseAffineWithinAt f s x) :
    ContinuousWithinAt f s x := by
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hf
  have := hι
  have hsub : (⋃ i, C i) ⊆ s := _root_.Set.iUnion_subset fun i => (hC i).2.1
  have heq : 𝓝[s] x = 𝓝[⋃ i, C i] x := by
    rw [← nhdsWithin_inter_of_mem' hCx, inter_eq_right.mpr hsub]
  have hi : ∀ i, ContinuousWithinAt f (C i) x := by
    intro i
    by_cases hxi : x ∈ C i
    · exact ((A i).continuous_of_finiteDimensional.continuousWithinAt).congr
        (fun y hy => (hC i).2.2 hy) ((hC i).2.2 hxi)
    · exact continuousWithinAt_of_notMem_closure (by rwa [(hC i).1.isClosed.closure_eq])
  change _root_.Filter.Tendsto f (𝓝[s] x) (𝓝 (f x))
  rw [heq, nhdsWithin_iUnion, _root_.Filter.tendsto_iSup]
  exact hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.continuousWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.continuousWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.continuousWithinAt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.continuousWithinAt

theorem continuousAt [FiniteDimensional ℝ E] (hf : IsPiecewiseAffineWithinAt f s x)
    (hs : s ∈ 𝓝 x) : ContinuousAt f x :=
  (continuousWithinAt_iff_continuousAt hs).mp hf.continuousWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.continuousAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.continuousAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.continuousAt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.continuousAt

theorem comp [FiniteDimensional ℝ E] {g : F → G} {t : Set F}
    (hg : IsPiecewiseAffineWithinAt g t (f x)) (hf : IsPiecewiseAffineWithinAt f s x) :
    IsPiecewiseAffineWithinAt (g ∘ f) (s ∩ f ⁻¹' t) x := by
  have hcont : ContinuousWithinAt f (s ∩ f ⁻¹' t) x :=
    hf.continuousWithinAt.mono _root_.Set.inter_subset_left
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hf
  obtain ⟨κ, hκ, D, B, hD, hDx⟩ := hg
  have := hι
  have := hκ
  refine ⟨ι × κ, inferInstance, fun p => C p.1 ∩ A p.1 ⁻¹' D p.2,
    fun p => (B p.2).comp (A p.1), fun p => ⟨(hC p.1).1.inter_preimage (hD p.2).1 (A p.1), ?_, ?_⟩,
    ?_⟩
  · intro y hy
    refine ⟨(hC p.1).2.1 hy.1, ?_⟩
    change f y ∈ t
    rw [(hC p.1).2.2 hy.1]
    exact (hD p.2).2.1 hy.2
  · intro y hy
    have hfy : f y = A p.1 y := (hC p.1).2.2 hy.1
    simp only [Function.comp_apply, AffineMap.comp_apply]
    rw [hfy]
    exact (hD p.2).2.2 hy.2
  · have himg : f '' (s ∩ f ⁻¹' t) ⊆ t :=
      (_root_.Set.image_mono _root_.Set.inter_subset_right).trans (_root_.Set.image_preimage_subset f t)
    have hpre : f ⁻¹' (⋃ j, D j) ∈ 𝓝[s ∩ f ⁻¹' t] x :=
      hcont.preimage_mem_nhdsWithin' (nhdsWithin_mono _ himg hDx)
    have hC' : (⋃ i, C i) ∈ 𝓝[s ∩ f ⁻¹' t] x := nhdsWithin_mono _ _root_.Set.inter_subset_left hCx
    filter_upwards [hC', hpre] with y hy hy'
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy'
    refine mem_iUnion.mpr ⟨(i, j), hi, ?_⟩
    rw [_root_.Set.mem_preimage, ← (hC i).2.2 hi]
    exact hj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.comp ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.comp

end IsPiecewiseAffineWithinAt

theorem isPiecewiseAffineOn_of_affine_of_isHPolytope (A : E →ᵃ[ℝ] F) {P : Set E}
    (hP : IsHPolytope P) : IsPiecewiseAffineOn A P := by
  intro x _
  exact ⟨Unit, inferInstance, fun _ => P, fun _ => A, fun _ => ⟨hP, subset_rfl, fun _ _ => rfl⟩, by
    rw [_root_.Set.iUnion_const]
    exact self_mem_nhdsWithin⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_of_affine_of_isHPolytope then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_of_affine_of_isHPolytope"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_of_affine_of_isHPolytope ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_of_affine_of_isHPolytope

theorem isPiecewiseAffineOn_of_affine [FiniteDimensional ℝ E] (A : E →ᵃ[ℝ] F) {u : Set E}
    (hu : IsOpen u) : IsPiecewiseAffineOn A u := by
  intro x hx
  obtain ⟨C, hC, hCu, hCx⟩ := exists_isHPolytope_subset_mem_nhds (hu.mem_nhds hx)
  exact ⟨Unit, inferInstance, fun _ => C, fun _ => A, fun _ => ⟨hC, hCu, fun _ _ => rfl⟩, by
    rw [_root_.Set.iUnion_const]
    exact mem_nhdsWithin_of_mem_nhds hCx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_of_affine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_of_affine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_of_affine ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_of_affine

theorem isPiecewiseAffineOn_id [FiniteDimensional ℝ E] {u : Set E} (hu : IsOpen u) :
    IsPiecewiseAffineOn (id : E → E) u :=
  isPiecewiseAffineOn_of_affine (AffineMap.id ℝ E) hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_id ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_id

theorem isPiecewiseAffineOn_of_subsingleton [Subsingleton E] (f : E → F) (u : Set E) :
    IsPiecewiseAffineOn f u := by
  intro x _
  refine ⟨Unit, inferInstance, fun _ => _root_.Set.univ, fun _ => AffineMap.const ℝ E (f x),
    fun _ => ⟨IsHPolytope.univ_of_subsingleton, fun y _ => ?_, fun y _ => ?_⟩, by
      rw [_root_.Set.iUnion_const]
      exact univ_mem⟩
  · rw [Subsingleton.elim y x]
    assumption
  · rw [Subsingleton.elim y x]
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_of_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_of_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_of_subsingleton ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_of_subsingleton

theorem isPiecewiseAffineOn_of_locally {f : E → F} {u : Set E}
    (h : ∀ x ∈ u, ∃ v, IsOpen v ∧ x ∈ v ∧ IsPiecewiseAffineOn f (u ∩ v)) :
    IsPiecewiseAffineOn f u := by
  intro x hx
  obtain ⟨v, hv, hxv, hfv⟩ := h x hx
  exact (hfv x ⟨hx, hxv⟩).of_inter_of_mem_nhds (hv.mem_nhds hxv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_of_locally then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_of_locally"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_of_locally ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_of_locally

namespace IsPiecewiseAffineOn

variable {f : E → F} {u : Set E}

theorem mono [FiniteDimensional ℝ E] (hf : IsPiecewiseAffineOn f u) {v : Set E} (hv : IsOpen v)
    (hvu : v ⊆ u) : IsPiecewiseAffineOn f v := by
  intro x hx
  have h := (hf x (hvu hx)).inter_of_mem_nhds (hv.mem_nhds hx)
  rwa [inter_eq_right.mpr hvu] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.mono ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.mono

theorem congr {g : E → F} (hf : IsPiecewiseAffineOn f u) (hfg : _root_.Set.EqOn g f u) :
    IsPiecewiseAffineOn g u :=
  fun x hx => (hf x hx).congr hfg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.congr ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.congr

theorem continuousOn [FiniteDimensional ℝ E] (hf : IsPiecewiseAffineOn f u) :
    ContinuousOn f u :=
  fun x hx => (hf x hx).continuousWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.continuousOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.continuousOn

theorem continuousAt [FiniteDimensional ℝ E] (hf : IsPiecewiseAffineOn f u) (hu : IsOpen u)
    {x : E} (hx : x ∈ u) : ContinuousAt f x :=
  (hf x hx).continuousAt (hu.mem_nhds hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.continuousAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.continuousAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.continuousAt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.continuousAt

theorem comp [FiniteDimensional ℝ E] {g : F → G} {v : Set F} (hg : IsPiecewiseAffineOn g v)
    (hf : IsPiecewiseAffineOn f u) : IsPiecewiseAffineOn (g ∘ f) (u ∩ f ⁻¹' v) :=
  fun x hx => (hg (f x) hx.2).comp (hf x hx.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.comp ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.comp

theorem symm [FiniteDimensional ℝ E] {e : OpenPartialHomeomorph E E}
    (he : IsPiecewiseAffineOn e e.source) : IsPiecewiseAffineOn e.symm e.target := by
  intro y hy
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := he (e.symm y) (e.map_target hy)
  have := hι
  rw [nhdsWithin_eq_nhds.mpr (e.open_source.mem_nhds (e.map_target hy))] at hCx
  have hlin : ∀ i, (interior (C i)).Nonempty → Function.Injective (A i).linear := by
    intro i hi
    refine linear_injective_of_injOn_of_interior_nonempty ?_ hi
    intro a ha b hb hab
    apply e.injOn ((hC i).2.1 ha) ((hC i).2.1 hb)
    rw [(hC i).2.2 ha, (hC i).2.2 hb]
    exact hab
  have hdec : ∀ i, ∀ p, A i p = (A i).linear p + A i 0 := fun i p => by
    simpa using (A i).map_vadd 0 p
  let T : {i // (interior (C i)).Nonempty} → E ≃ᵃ[ℝ] E := fun i =>
    AffineEquiv.mk' (A i) (LinearEquiv.ofInjectiveEndo (A i).linear (hlin i i.2)) 0 fun p => by
      change A i p = (A i).linear (p - 0) + A i 0
      rw [sub_zero]
      exact hdec i p
  have hT : ∀ i p, T i p = A i p := fun i p => rfl
  refine ⟨{i // (interior (C i)).Nonempty}, inferInstance, fun i => e '' C i,
    fun i => (T i).symm.toAffineMap, fun i => ⟨?_, ?_, ?_⟩, ?_⟩
  · have himg : e '' C i = T i '' C i := _root_.Set.image_congr fun a ha => by rw [hT, ← (hC i).2.2 ha]
    change IsHPolytope (e '' C i)
    rw [himg]
    exact (hC i).1.image_affineEquiv (T i)
  · change e '' C i ⊆ e.target
    rw [← e.image_source_eq_target]
    exact _root_.Set.image_mono (hC i).2.1
  · change _root_.Set.EqOn e.symm (T i).symm.toAffineMap (e '' C i)
    rintro _ ⟨a, ha, rfl⟩
    rw [e.left_inv ((hC i).2.1 ha), AffineEquiv.coe_toAffineMap]
    have hea : e a = T i a := by rw [hT, ← (hC i).2.2 ha]
    rw [hea, AffineEquiv.symm_apply_apply]
  · change (⋃ i : {i // (interior (C i)).Nonempty}, e '' C i) ∈ 𝓝[e.target] y
    refine mem_nhdsWithin_of_mem_nhds ?_
    rw [← _root_.Set.image_iUnion, ← e.right_inv hy, ← e.map_nhds_eq (e.map_target hy)]
    exact _root_.Filter.image_mem_map (iUnion_interior_nonempty_mem_nhds (fun i => (hC i).1.isClosed) hCx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.symm ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.symm

end IsPiecewiseAffineOn

end DifferentialGeometry.Topology.PiecewiseLinear
