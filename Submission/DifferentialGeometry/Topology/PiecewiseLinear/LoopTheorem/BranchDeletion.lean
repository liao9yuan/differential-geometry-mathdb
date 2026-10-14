/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ComponentComplex
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCarrier
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchDescent
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchPreimage

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem image_diff_of_injOn {X Y : Type*} {f : X → Y} {u s t : Set X} (hf : _root_.Set.InjOn f u)
    (hs : s ⊆ u) (ht : t ⊆ u) : f '' (s \ t) = f '' s \ f '' t := by
  apply Subset.antisymm
  · rintro _ ⟨x, ⟨hxs, hxt⟩, rfl⟩
    refine ⟨⟨x, hxs, rfl⟩, ?_⟩
    rintro ⟨z, hz, hzx⟩
    exact hxt (hf (ht hz) (hs hxs) hzx ▸ hz)
  · rintro _ ⟨⟨x, hxs, rfl⟩, hx⟩
    exact ⟨x, ⟨hxs, fun hxt => hx ⟨x, hxt, rfl⟩⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_diff_of_injOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_diff_of_injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_diff_of_injOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_diff_of_injOn

theorem subset_of_isPreconnected_of_iUnion_isClosed {X : Type*} [TopologicalSpace X]
    {β : Type*} [Finite β] {g : β → Set X} (hclosed : ∀ b, IsClosed (g b))
    (hdisjoint : Pairwise fun b b' => Disjoint (g b) (g b')) {A : Set X}
    (hA : IsPreconnected A) (hAne : A.Nonempty) (hAU : A ⊆ ⋃ b, g b) :
    ∃ b, A ⊆ g b := by
  obtain ⟨y, hy⟩ := hAne
  obtain ⟨b, hb⟩ := mem_iUnion.mp (hAU hy)
  refine ⟨b, ?_⟩
  have hrest : IsClosed (⋃ b' ∈ {b' : β | b' ≠ b}, g b') :=
    Set.Finite.isClosed_biUnion (Set.toFinite _) fun b' _ => hclosed b'
  have hcover : A ⊆ g b ∪ ⋃ b' ∈ {b' : β | b' ≠ b}, g b' := by
    intro x hx
    obtain ⟨b', hb'⟩ := mem_iUnion.mp (hAU hx)
    by_cases hbb : b' = b
    · exact Or.inl (hbb ▸ hb')
    · exact Or.inr (_root_.Set.mem_biUnion hbb hb')
  have hempty : ¬(A ∩ ⋃ b' ∈ {b' : β | b' ≠ b}, g b').Nonempty := by
    intro hne
    obtain ⟨z, -, hzb, hzrest⟩ :=
      isPreconnected_closed_iff.mp hA _ _ (hclosed b) hrest hcover ⟨y, hy, hb⟩ hne
    obtain ⟨b', hb'ne, hzb'⟩ := mem_iUnion₂.mp hzrest
    exact Set.disjoint_left.mp (hdisjoint hb'ne) hzb' hzb
  intro x hx
  rcases hcover hx with h | h
  · exact h
  · exact absurd ⟨x, hx, h⟩ hempty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subset_of_isPreconnected_of_iUnion_isClosed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subset_of_isPreconnected_of_iUnion_isClosed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subset_of_isPreconnected_of_iUnion_isClosed ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subset_of_isPreconnected_of_iUnion_isClosed

theorem exists_equiv_of_isClosed_isConnected_partition {X : Type*} [TopologicalSpace X]
    {α β : Type*} [Finite α] [Finite β] {f : α → Set X} {g : β → Set X}
    (hfconn : ∀ a, IsConnected (f a)) (hgconn : ∀ b, IsConnected (g b))
    (hfclosed : ∀ a, IsClosed (f a)) (hgclosed : ∀ b, IsClosed (g b))
    (hfdisjoint : Pairwise fun a a' => Disjoint (f a) (f a'))
    (hgdisjoint : Pairwise fun b b' => Disjoint (g b) (g b'))
    (hunion : ⋃ a, f a = ⋃ b, g b) :
    ∃ e : α ≃ β, ∀ a, f a = g (e a) := by
  have hfsub : ∀ a, f a ⊆ ⋃ b, g b := by
    intro a
    rw [← hunion]
    exact _root_.Set.subset_iUnion f a
  have hgsub : ∀ b, g b ⊆ ⋃ a, f a := by
    intro b
    rw [hunion]
    exact _root_.Set.subset_iUnion g b
  have hfg : ∀ a, ∃ b, f a ⊆ g b := fun a =>
    subset_of_isPreconnected_of_iUnion_isClosed hgclosed hgdisjoint (hfconn a).isPreconnected
      (hfconn a).nonempty (hfsub a)
  have hgf : ∀ b, ∃ a, g b ⊆ f a := fun b =>
    subset_of_isPreconnected_of_iUnion_isClosed hfclosed hfdisjoint (hgconn b).isPreconnected
      (hgconn b).nonempty (hgsub b)
  choose F hF using hfg
  choose G hG using hgf
  have hGF : ∀ a, G (F a) = a := by
    intro a
    by_contra hne
    obtain ⟨y, hy⟩ := (hfconn a).nonempty
    exact Set.disjoint_left.mp (hfdisjoint hne) (hG (F a) (hF a hy)) hy
  have hFG : ∀ b, F (G b) = b := by
    intro b
    by_contra hne
    obtain ⟨y, hy⟩ := (hgconn b).nonempty
    exact Set.disjoint_left.mp (hgdisjoint hne) (hF (G b) (hG b hy)) hy
  refine ⟨⟨F, G, hGF, hFG⟩, fun a => Subset.antisymm (hF a) ?_⟩
  have h := hG (F a)
  rw [hGF a] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_equiv_of_isClosed_isConnected_partition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_equiv_of_isClosed_isConnected_partition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_equiv_of_isClosed_isConnected_partition ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_equiv_of_isClosed_isConnected_partition

section Saturated

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem restrict_space_of_saturated (K : Geometry.SimplicialComplex ℝ E) {C : Set E}
    (hCK : C ⊆ K.space)
    (hsat : ∀ A ⊆ K.space, IsPreconnected A → (A ∩ C).Nonempty → A ⊆ C) :
    (restrict K C).space = C := by
  apply Subset.antisymm (restrict_space_subset K C)
  intro z hz
  obtain ⟨s, hs, hzs⟩ := K.mem_space_iff.mp (hCK hz)
  exact (restrict K C).convexHull_subset_space
    ⟨hs, hsat _ (K.convexHull_subset_space hs) (convex_convexHull ℝ _).isPreconnected
      ⟨z, hzs, hz⟩⟩ hzs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.restrict_space_of_saturated then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.restrict_space_of_saturated"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.restrict_space_of_saturated ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.restrict_space_of_saturated

theorem geometricLink_restrict_of_saturated [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) {C : Set E} {v : E} {s : Finset E} (hvs : v ∈ s)
    (hv : v ∈ C) (hsat : ∀ A ⊆ K.space, IsPreconnected A → (A ∩ C).Nonempty → A ⊆ C) :
    SimplicialComplex.geometricLink (restrict K C) s = SimplicialComplex.geometricLink K s := by
  ext t
  simp only [mem_geometricLink_faces_iff, mem_restrict_faces_iff]
  constructor
  · rintro ⟨hne, hdis, ht, -⟩
    exact ⟨hne, hdis, ht⟩
  · rintro ⟨hne, hdis, ht⟩
    exact ⟨hne, hdis, ht, hsat _ (K.convexHull_subset_space ht)
      (convex_convexHull ℝ _).isPreconnected
      ⟨v, subset_convexHull ℝ _ (Finset.mem_union_left t hvs), hv⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_restrict_of_saturated then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_restrict_of_saturated"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_restrict_of_saturated ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_restrict_of_saturated

open _root_.Classical in
theorem geometricLink_restrict_singleton_of_saturated (K : Geometry.SimplicialComplex ℝ E)
    {C : Set E} {v : E} (hv : v ∈ C)
    (hsat : ∀ A ⊆ K.space, IsPreconnected A → (A ∩ C).Nonempty → A ⊆ C) :
    SimplicialComplex.geometricLink (restrict K C) {v} =
      SimplicialComplex.geometricLink K {v} :=
  geometricLink_restrict_of_saturated K (Finset.mem_singleton_self v) hv hsat

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_restrict_singleton_of_saturated then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_restrict_singleton_of_saturated"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_restrict_singleton_of_saturated ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_restrict_singleton_of_saturated

theorem IsCombinatorialManifoldWithBoundary.restrict_of_saturated
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ} {C : Set E}
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hsat : ∀ A ⊆ K.space, IsPreconnected A → (A ∩ C).Nonempty → A ⊆ C) :
    IsCombinatorialManifoldWithBoundary n (restrict K C) := by
  classical
  cases n with
  | zero =>
    intro v hv
    rw [geometricLink_restrict_singleton_of_saturated K (hv.2 (by simp)) hsat]
    exact hK v hv.1
  | succ n =>
    intro v hv
    rw [geometricLink_restrict_singleton_of_saturated K (hv.2 (by simp)) hsat]
    exact hK v hv.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.restrict_of_saturated then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.restrict_of_saturated"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.restrict_of_saturated ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.restrict_of_saturated

theorem boundaryComplex_restrict_of_saturated [DecidableEq E] (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ E) {C : Set E}
    (hsat : ∀ A ⊆ K.space, IsPreconnected A → (A ∩ C).Nonempty → A ⊆ C) :
    boundaryComplex n (restrict K C) = restrict (boundaryComplex n K) C := by
  ext s
  constructor
  · rintro ⟨⟨hs, hsc⟩, t, ⟨ht, htc⟩, hst, hcard, hball⟩
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces ht
    rw [geometricLink_restrict_of_saturated K hv (htc (subset_convexHull ℝ _ hv)) hsat] at hball
    exact ⟨⟨hs, t, ht, hst, hcard, hball⟩, hsc⟩
  · rintro ⟨⟨hs, t, ht, hst, hcard, hball⟩, hsc⟩
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
    have hvc := hsc (subset_convexHull ℝ _ hv)
    have htc : convexHull ℝ (t : Set E) ⊆ C :=
      hsat _ (K.convexHull_subset_space ht) (convex_convexHull ℝ _).isPreconnected
        ⟨v, subset_convexHull ℝ _ (hst hv), hvc⟩
    refine ⟨⟨hs, hsc⟩, t, ⟨ht, htc⟩, hst, hcard, ?_⟩
    rwa [geometricLink_restrict_of_saturated K (hst hv) hvc hsat]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_restrict_of_saturated then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_restrict_of_saturated"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_restrict_of_saturated ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_restrict_of_saturated

theorem boundaryComplex_space_restrict_of_saturated [DecidableEq E] (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ E) {C : Set E}
    (hsat : ∀ A ⊆ K.space, IsPreconnected A → (A ∩ C).Nonempty → A ⊆ C) :
    (boundaryComplex n (restrict K C)).space = (boundaryComplex n K).space ∩ C := by
  rw [boundaryComplex_restrict_of_saturated n K hsat]
  apply Subset.antisymm
  · exact fun _ hx => ⟨space_mono_of_faces_subset (restrict_faces_subset _ _) hx,
      restrict_space_subset _ _ hx⟩
  · rintro x ⟨hxB, hxC⟩
    obtain ⟨s, hs, hxs⟩ := (boundaryComplex n K).mem_space_iff.mp hxB
    exact (restrict (boundaryComplex n K) C).convexHull_subset_space
      ⟨hs, hsat _ (K.convexHull_subset_space hs.1) (convex_convexHull ℝ _).isPreconnected
        ⟨x, hxs, hxC⟩⟩ hxs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_restrict_of_saturated then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_restrict_of_saturated"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_restrict_of_saturated ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_restrict_of_saturated

theorem boundaryComplex_congr_decidableEq (d d' : DecidableEq E) (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ E) :
    @boundaryComplex E _ _ d n K = @boundaryComplex E _ _ d' n K :=
  congrArg (fun e : DecidableEq E => @boundaryComplex E _ _ e n K) (Subsingleton.elim d d')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_congr_decidableEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_congr_decidableEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_congr_decidableEq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_congr_decidableEq

end Saturated

namespace NormalSingularSetTriangulation

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D D' : SingularTwoCell M} {BdM BdM' : Set M}

theorem isCompact_branchComplex_space (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) : IsCompact (T.branchComplex c).space :=
  (T.branchComplex_space_isPolyhedron c).isCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isCompact_branchComplex_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isCompact_branchComplex_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isCompact_branchComplex_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isCompact_branchComplex_space

theorem isClosed_branchComplex_space (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) : IsClosed (T.branchComplex c).space :=
  (T.isCompact_branchComplex_space c).isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isClosed_branchComplex_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isClosed_branchComplex_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isClosed_branchComplex_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isClosed_branchComplex_space

theorem exists_subset_branchComplex_space_of_isPreconnected
    (T : NormalSingularSetTriangulation D BdM)
    {A : Set (EuclideanSpace ℝ (Fin T.piece.ambientDim))} (hA : IsPreconnected A)
    (hAne : A.Nonempty) (hAK : A ⊆ T.complex.space) :
    ∃ b, A ⊆ (T.branchComplex b).space := by
  let _ : Finite T.Branch := T.finite_branch
  refine subset_of_isPreconnected_of_iUnion_isClosed (fun b => T.isClosed_branchComplex_space b)
    T.pairwise_disjoint_branchComplex_space hA hAne ?_
  rw [← T.space_eq_iUnion_branchComplex]
  exact hAK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.exists_subset_branchComplex_space_of_isPreconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.exists_subset_branchComplex_space_of_isPreconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.exists_subset_branchComplex_space_of_isPreconnected ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.exists_subset_branchComplex_space_of_isPreconnected

theorem subset_diff_branchComplex_space (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) (A : Set (EuclideanSpace ℝ (Fin T.piece.ambientDim)))
    (hAK : A ⊆ T.complex.space) (hA : IsPreconnected A)
    (hne : (A ∩ (T.complex.space \ (T.branchComplex c).space)).Nonempty) :
    A ⊆ T.complex.space \ (T.branchComplex c).space := by
  obtain ⟨y, hyA, -, hyc⟩ := hne
  obtain ⟨b, hb⟩ := T.exists_subset_branchComplex_space_of_isPreconnected hA ⟨y, hyA⟩ hAK
  have hbc : b ≠ c := fun h => hyc (h ▸ hb hyA)
  exact fun x hx => ⟨hAK hx,
    Set.disjoint_left.mp (T.pairwise_disjoint_branchComplex_space hbc) (hb hx)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.subset_diff_branchComplex_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.subset_diff_branchComplex_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.subset_diff_branchComplex_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.subset_diff_branchComplex_space

noncomputable def deletedBranchComplex (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) :
    Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin T.piece.ambientDim)) :=
  restrict T.complex (T.complex.space \ (T.branchComplex c).space)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex

theorem deletedBranchComplex_faces_subset (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) : (T.deletedBranchComplex c).faces ⊆ T.complex.faces :=
  restrict_faces_subset T.complex _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_faces_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_faces_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_faces_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_faces_subset

theorem deletedBranchComplex_faces_finite (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) : (T.deletedBranchComplex c).faces.Finite :=
  T.finite_faces.subset (T.deletedBranchComplex_faces_subset c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_faces_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_faces_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_faces_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_faces_finite

theorem deletedBranchComplex_space (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    (T.deletedBranchComplex c).space = T.complex.space \ (T.branchComplex c).space :=
  restrict_space_of_saturated T.complex Set.sdiff_subset (T.subset_diff_branchComplex_space c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_space

theorem deletedBranchComplex_space_eq_iUnion (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) :
    (T.deletedBranchComplex c).space =
      ⋃ b ∈ {b : T.Branch | b ≠ c}, (T.branchComplex b).space := by
  rw [T.deletedBranchComplex_space]
  apply Subset.antisymm
  · rintro x ⟨hxK, hxc⟩
    rw [T.space_eq_iUnion_branchComplex] at hxK
    obtain ⟨b, hb⟩ := mem_iUnion.mp hxK
    exact _root_.Set.mem_biUnion (show b ≠ c from fun h => hxc (h ▸ hb)) hb
  · intro x hx
    obtain ⟨b, hbc, hb⟩ := mem_iUnion₂.mp hx
    exact ⟨T.branchComplex_space_subset b hb,
      Set.disjoint_left.mp (T.pairwise_disjoint_branchComplex_space hbc) hb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_space_eq_iUnion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_space_eq_iUnion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_space_eq_iUnion ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_space_eq_iUnion

theorem deletedBranchComplex_isManifoldWithBoundary (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) : IsCombinatorialManifoldWithBoundary 1 (T.deletedBranchComplex c) :=
  T.isManifoldWithBoundary.restrict_of_saturated (T.subset_diff_branchComplex_space c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_isManifoldWithBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_isManifoldWithBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_isManifoldWithBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchComplex_isManifoldWithBoundary

theorem map_complex_space_diff_branchComplex_space (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) :
    T.piece.piece.map '' (T.complex.space \ (T.branchComplex c).space) =
      doublePointSet D D.domain \ T.branchCarrier c := by
  rw [image_diff_of_injOn T.piece.piece.bijOn.injOn
    (space_mono_of_faces_subset T.faces_subset) (T.branchComplex_space_subset_piece c),
    T.map_space]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.map_complex_space_diff_branchComplex_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.map_complex_space_diff_branchComplex_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.map_complex_space_diff_branchComplex_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.map_complex_space_diff_branchComplex_space

theorem map_deletedBranchComplex_space (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) :
    T.piece.piece.map '' (T.deletedBranchComplex c).space =
      doublePointSet D D.domain \ T.branchCarrier c := by
  rw [T.deletedBranchComplex_space]
  exact T.map_complex_space_diff_branchComplex_space c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.map_deletedBranchComplex_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.map_deletedBranchComplex_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.map_deletedBranchComplex_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.map_deletedBranchComplex_space

theorem map_boundaryComplex_deletedBranchComplex_space
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch)
    (d : DecidableEq (EuclideanSpace ℝ (Fin T.piece.ambientDim))) :
    T.piece.piece.map '' (@boundaryComplex _ _ _ d 1 (T.deletedBranchComplex c)).space =
      (doublePointSet D D.domain \ T.branchCarrier c) ∩ BdM := by
  have hpiece : T.complex.space ⊆ T.piece.piece.complex.space :=
    space_mono_of_faces_subset T.faces_subset
  have hbdry : (@boundaryComplex _ _ _ d 1 (T.deletedBranchComplex c)).space =
      (@boundaryComplex _ _ _ d 1 T.complex).space ∩
        (T.complex.space \ (T.branchComplex c).space) :=
    @boundaryComplex_space_restrict_of_saturated _ _ _ d 1 T.complex _
      (T.subset_diff_branchComplex_space c)
  have hmap : T.piece.piece.map '' (@boundaryComplex _ _ _ d 1 T.complex).space =
      doublePointSet D D.domain ∩ BdM := by
    have hb := T.map_boundary
    rwa [boundaryComplex_congr_decidableEq (E := EuclideanSpace ℝ (Fin T.piece.ambientDim))
      _ d 1 T.complex] at hb
  rw [hbdry, Set.InjOn.image_inter T.piece.piece.bijOn.injOn
    ((@boundaryComplex_space_subset _ _ _ d 1 T.complex).trans hpiece)
    (Set.sdiff_subset.trans hpiece), hmap, T.map_complex_space_diff_branchComplex_space c]
  ext y
  simp only [_root_.Set.mem_inter_iff, _root_.Set.mem_sdiff]
  tauto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.map_boundaryComplex_deletedBranchComplex_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.map_boundaryComplex_deletedBranchComplex_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.map_boundaryComplex_deletedBranchComplex_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.map_boundaryComplex_deletedBranchComplex_space

noncomputable def deletedBranchTriangulation (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch)
    (hD' : doublePointSet D' D'.domain = doublePointSet D D.domain \ T.branchCarrier c) :
    NormalSingularSetTriangulation D' BdM where
  carrier := T.carrier
  piece := T.piece
  complex := T.deletedBranchComplex c
  finite_faces := T.deletedBranchComplex_faces_finite c
  faces_subset := (T.deletedBranchComplex_faces_subset c).trans T.faces_subset
  isManifoldWithBoundary := T.deletedBranchComplex_isManifoldWithBoundary c
  map_space := by
    rw [hD']
    exact T.map_deletedBranchComplex_space c
  map_boundary := by
    rw [hD']
    exact T.map_boundaryComplex_deletedBranchComplex_space c _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchTriangulation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchTriangulation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchTriangulation ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchTriangulation

theorem deletedBranchTriangulation_complex (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch)
    (hD' : doublePointSet D' D'.domain = doublePointSet D D.domain \ T.branchCarrier c) :
    (T.deletedBranchTriangulation c hD').complex = T.deletedBranchComplex c :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchTriangulation_complex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchTriangulation_complex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchTriangulation_complex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.deletedBranchTriangulation_complex

theorem nonempty_of_doublePointSet_eq_sdiff_branchCarrier
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch)
    (hD' : doublePointSet D' D'.domain = doublePointSet D D.domain \ T.branchCarrier c) :
    Nonempty (NormalSingularSetTriangulation D' BdM) :=
  ⟨T.deletedBranchTriangulation c hD'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.nonempty_of_doublePointSet_eq_sdiff_branchCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.nonempty_of_doublePointSet_eq_sdiff_branchCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.nonempty_of_doublePointSet_eq_sdiff_branchCarrier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.nonempty_of_doublePointSet_eq_sdiff_branchCarrier

theorem isCompact_branchCarrier (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    IsCompact (T.branchCarrier c) :=
  (T.isCompact_branchComplex_space c).image_of_continuousOn
    (T.piece.piece.continuousOn.mono (T.branchComplex_space_subset_piece c))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isCompact_branchCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isCompact_branchCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isCompact_branchCarrier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isCompact_branchCarrier

theorem isClosed_branchCarrier [T2Space M] (T : NormalSingularSetTriangulation D BdM)
    (c : T.Branch) : IsClosed (T.branchCarrier c) :=
  (T.isCompact_branchCarrier c).isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isClosed_branchCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isClosed_branchCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isClosed_branchCarrier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.isClosed_branchCarrier

theorem iUnion_branchCarrier_ne (T : NormalSingularSetTriangulation D BdM) (c : T.Branch) :
    ⋃ b : {b : T.Branch // b ≠ c}, T.branchCarrier b.1 =
      doublePointSet D D.domain \ T.branchCarrier c := by
  apply Subset.antisymm
  · refine _root_.Set.iUnion_subset ?_
    rintro ⟨b, hbc⟩ y hy
    exact ⟨T.branchCarrier_subset_doublePointSet b hy,
      Set.disjoint_left.mp (T.pairwise_disjoint_branchCarrier hbc) hy⟩
  · rintro y ⟨hy, hyc⟩
    rw [← T.iUnion_branchCarrier] at hy
    obtain ⟨b, hb⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨⟨b, fun h => hyc (h ▸ hb)⟩, hb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.iUnion_branchCarrier_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.iUnion_branchCarrier_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.iUnion_branchCarrier_ne ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.iUnion_branchCarrier_ne

theorem exists_branchEquiv_of_doublePointSet_eq_sdiff [T2Space M]
    (T : NormalSingularSetTriangulation D BdM) (S : NormalSingularSetTriangulation D' BdM')
    (c : T.Branch)
    (hD' : doublePointSet D' D'.domain = doublePointSet D D.domain \ T.branchCarrier c) :
    ∃ e : S.Branch ≃ {b : T.Branch // b ≠ c},
      ∀ b, S.branchCarrier b = T.branchCarrier (e b).1 := by
  let _ : Finite T.Branch := T.finite_branch
  let _ : Finite S.Branch := S.finite_branch
  refine exists_equiv_of_isClosed_isConnected_partition
    (f := S.branchCarrier) (g := fun b : {b : T.Branch // b ≠ c} => T.branchCarrier b.1)
    (fun b => S.branchCarrier_isConnected b) (fun b => T.branchCarrier_isConnected b.1)
    (fun b => S.isClosed_branchCarrier b) (fun b => T.isClosed_branchCarrier b.1)
    S.pairwise_disjoint_branchCarrier
    (fun b b' hbb => T.pairwise_disjoint_branchCarrier fun h => hbb (Subtype.ext h)) ?_
  rw [S.iUnion_branchCarrier, T.iUnion_branchCarrier_ne c]
  exact hD'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.exists_branchEquiv_of_doublePointSet_eq_sdiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.exists_branchEquiv_of_doublePointSet_eq_sdiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.exists_branchEquiv_of_doublePointSet_eq_sdiff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.exists_branchEquiv_of_doublePointSet_eq_sdiff

noncomputable def branchEquivCompl [T2Space M] (T : NormalSingularSetTriangulation D BdM)
    (S : NormalSingularSetTriangulation D' BdM') (c : T.Branch)
    (hD' : doublePointSet D' D'.domain = doublePointSet D D.domain \ T.branchCarrier c) :
    S.Branch ≃ {b : T.Branch // b ≠ c} :=
  (T.exists_branchEquiv_of_doublePointSet_eq_sdiff S c hD').choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchEquivCompl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchEquivCompl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchEquivCompl ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchEquivCompl

theorem branchCarrier_branchEquivCompl [T2Space M] (T : NormalSingularSetTriangulation D BdM)
    (S : NormalSingularSetTriangulation D' BdM') (c : T.Branch)
    (hD' : doublePointSet D' D'.domain = doublePointSet D D.domain \ T.branchCarrier c)
    (b : S.Branch) :
    S.branchCarrier b = T.branchCarrier (T.branchEquivCompl S c hD' b).1 :=
  (T.exists_branchEquiv_of_doublePointSet_eq_sdiff S c hD').choose_spec b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_branchEquivCompl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_branchEquivCompl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_branchEquivCompl ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.branchCarrier_branchEquivCompl

theorem exists_branchEquiv_deletedBranchTriangulation [T2Space M]
    (T : NormalSingularSetTriangulation D BdM) (c : T.Branch)
    (hD' : doublePointSet D' D'.domain = doublePointSet D D.domain \ T.branchCarrier c) :
    ∃ e : (T.deletedBranchTriangulation c hD').Branch ≃ {b : T.Branch // b ≠ c},
      ∀ b, (T.deletedBranchTriangulation c hD').branchCarrier b = T.branchCarrier (e b).1 :=
  T.exists_branchEquiv_of_doublePointSet_eq_sdiff (T.deletedBranchTriangulation c hD') c hD'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.exists_branchEquiv_deletedBranchTriangulation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.exists_branchEquiv_deletedBranchTriangulation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.exists_branchEquiv_deletedBranchTriangulation ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.exists_branchEquiv_deletedBranchTriangulation

end NormalSingularSetTriangulation

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D G : SingularTwoCell M} {BdM B BdM' B' : Set M}

theorem exists_singularSet_branchEquiv_of_doublePointSet_eq [T2Space M]
    (hD : NormalSingularCellData D BdM B) (hG : NormalSingularCellData G BdM' B')
    (c : hD.singularSet.Branch)
    (hdp : doublePointSet G G.domain =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c) :
    ∃ e : hG.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c},
      ∀ b, hG.singularSet.branchCarrier b = hD.singularSet.branchCarrier (e b).1 :=
  hD.singularSet.exists_branchEquiv_of_doublePointSet_eq_sdiff hG.singularSet c hdp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_singularSet_branchEquiv_of_doublePointSet_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_singularSet_branchEquiv_of_doublePointSet_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_singularSet_branchEquiv_of_doublePointSet_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_singularSet_branchEquiv_of_doublePointSet_eq

noncomputable def deletedBranchEquiv [T2Space M] (hD : NormalSingularCellData D BdM B)
    (hG : NormalSingularCellData G BdM' B') (c : hD.singularSet.Branch)
    (hdp : doublePointSet G G.domain =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c) :
    hG.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c} :=
  hD.singularSet.branchEquivCompl hG.singularSet c hdp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.deletedBranchEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.deletedBranchEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.deletedBranchEquiv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.deletedBranchEquiv

theorem branchCarrier_deletedBranchEquiv [T2Space M] (hD : NormalSingularCellData D BdM B)
    (hG : NormalSingularCellData G BdM' B') (c : hD.singularSet.Branch)
    (hdp : doublePointSet G G.domain =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c)
    (b : hG.singularSet.Branch) :
    hG.singularSet.branchCarrier b =
      hD.singularSet.branchCarrier (hD.deletedBranchEquiv hG c hdp b).1 :=
  hD.singularSet.branchCarrier_branchEquivCompl hG.singularSet c hdp b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.branchCarrier_deletedBranchEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.branchCarrier_deletedBranchEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.branchCarrier_deletedBranchEquiv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.branchCarrier_deletedBranchEquiv

theorem branchCarrier_subset_image_of_isPLHomeomorphOn (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch) {A C : Set (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)} (hg : IsPLHomeomorphOn g A C)
    (hcompat : _root_.Set.EqOn D (D ∘ g) A) (hcover : hD.branchPreimage c = A ∪ C) :
    hD.singularSet.branchCarrier c ⊆ D '' C := by
  intro y hy
  obtain ⟨x, hx, -, -, -, hxy, -⟩ := hD.singularSet.branchCarrier_subset_doublePointSet c hy
  have hxpre : x ∈ hD.branchPreimage c := ⟨hx, by rw [_root_.Set.mem_preimage, hxy]; exact hy⟩
  rw [hcover] at hxpre
  rcases hxpre with hxA | hxC
  · exact ⟨g x, hg.1.mapsTo hxA, ((hcompat hxA).symm.trans hxy : D (g x) = y)⟩
  · exact ⟨x, hxC, hxy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.branchCarrier_subset_image_of_isPLHomeomorphOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.branchCarrier_subset_image_of_isPLHomeomorphOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.branchCarrier_subset_image_of_isPLHomeomorphOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.branchCarrier_subset_image_of_isPLHomeomorphOn

theorem doublePointSet_diff_eq_sdiff_branchCarrier (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch) {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hCsub : C ⊆ hD.branchPreimage c)
    (hCcover : hD.singularSet.branchCarrier c ⊆ D '' C) :
    doublePointSet D (D.domain \ C) =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c := by
  apply Subset.antisymm
  · rintro y ⟨a, ⟨haD, haC⟩, b, ⟨hbD, hbC⟩, hab, hay, hby⟩
    refine ⟨⟨a, haD, b, hbD, hab, hay, hby⟩, ?_⟩
    intro hyc
    obtain ⟨w, hwC, hwy⟩ := hCcover hyc
    have hfiber : ({a, b} : Set (EuclideanSpace ℝ (Fin 2))) = D.domain ∩ D ⁻¹' {y} := by
      refine ((Set.finite_singleton b).insert a).eq_of_subset_of_encard_le ?_ ?_
      · rintro z (rfl | rfl)
        · exact ⟨haD, hay⟩
        · exact ⟨hbD, hby⟩
      · rw [Set.encard_pair hab]
        exact hD.fiber_le_two y
    have hw : w ∈ ({a, b} : Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [hfiber]
      exact ⟨(hCsub hwC).1, hwy⟩
    rcases hw with rfl | rfl
    · exact haC hwC
    · exact hbC hwC
  · rintro y ⟨⟨a, haD, b, hbD, hab, hay, hby⟩, hyc⟩
    have hnot : ∀ z ∈ D.domain, D z = y → z ∉ C := by
      intro z _ hzy hzC
      exact hyc (hzy ▸ (hCsub hzC).2)
    exact ⟨a, ⟨haD, hnot a haD hay⟩, b, ⟨hbD, hnot b hbD hby⟩, hab, hay, hby⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.doublePointSet_diff_eq_sdiff_branchCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.doublePointSet_diff_eq_sdiff_branchCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.doublePointSet_diff_eq_sdiff_branchCarrier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.doublePointSet_diff_eq_sdiff_branchCarrier

theorem doublePointSet_eq_image_of_pullback {D G : SingularTwoCell M}
    {pullback : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hinj : _root_.Set.InjOn pullback G.domain) (heq : _root_.Set.EqOn (D ∘ pullback) G G.domain) :
    doublePointSet G G.domain = doublePointSet D (pullback '' G.domain) := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, z, hz, hxz, hGx, hGz⟩
    exact ⟨pullback x, ⟨x, hx, rfl⟩, pullback z, ⟨z, hz, rfl⟩,
      fun h => hxz (hinj hx hz h), (heq hx).trans hGx, (heq hz).trans hGz⟩
  · rintro y ⟨-, ⟨x, hx, rfl⟩, -, ⟨z, hz, rfl⟩, hxz, hDx, hDz⟩
    exact ⟨x, hx, z, hz, fun h => hxz (congrArg pullback h),
      (heq hx).symm.trans hDx, (heq hz).symm.trans hDz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.doublePointSet_eq_image_of_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.doublePointSet_eq_image_of_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.doublePointSet_eq_image_of_pullback ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.doublePointSet_eq_image_of_pullback

theorem doublePointSet_eq_sdiff_of_boundarySurgery (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch) {A C : Set (EuclideanSpace ℝ (Fin 2))}
    {g pullback : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hg : IsPLHomeomorphOn g A C) (hcompat : _root_.Set.EqOn D (D ∘ g) A)
    (hcover : hD.branchPreimage c = A ∪ C)
    (hmaps : _root_.Set.MapsTo pullback G.domain D.domain) (hinj : _root_.Set.InjOn pullback G.domain)
    (heq : _root_.Set.EqOn (D ∘ pullback) G G.domain) (hdisj : Disjoint (pullback '' G.domain) C)
    (hsurj : D.domain \ C ⊆ pullback '' G.domain) :
    doublePointSet G G.domain =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c := by
  have hpull : pullback '' G.domain = D.domain \ C := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨hmaps hx, Set.disjoint_left.mp hdisj ⟨x, hx, rfl⟩⟩
    · exact hsurj
  rw [doublePointSet_eq_image_of_pullback hinj heq, hpull]
  refine hD.doublePointSet_diff_eq_sdiff_branchCarrier c ?_
    (hD.branchCarrier_subset_image_of_isPLHomeomorphOn c hg hcompat hcover)
  rw [hcover]
  exact _root_.Set.subset_union_right

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.doublePointSet_eq_sdiff_of_boundarySurgery then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.doublePointSet_eq_sdiff_of_boundarySurgery"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.doublePointSet_eq_sdiff_of_boundarySurgery ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.doublePointSet_eq_sdiff_of_boundarySurgery

theorem exists_branchEquiv_of_boundarySurgery [T2Space M] (hD : NormalSingularCellData D BdM B)
    (hG : NormalSingularCellData G BdM' B') (c : hD.singularSet.Branch)
    {A C : Set (EuclideanSpace ℝ (Fin 2))}
    {g pullback : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hg : IsPLHomeomorphOn g A C) (hcompat : _root_.Set.EqOn D (D ∘ g) A)
    (hcover : hD.branchPreimage c = A ∪ C)
    (hmaps : _root_.Set.MapsTo pullback G.domain D.domain) (hinj : _root_.Set.InjOn pullback G.domain)
    (heq : _root_.Set.EqOn (D ∘ pullback) G G.domain) (hdisj : Disjoint (pullback '' G.domain) C)
    (hsurj : D.domain \ C ⊆ pullback '' G.domain) :
    ∃ e : hG.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c},
      ∀ b, hG.singularSet.branchCarrier b = hD.singularSet.branchCarrier (e b).1 :=
  hD.exists_singularSet_branchEquiv_of_doublePointSet_eq hG c
    (hD.doublePointSet_eq_sdiff_of_boundarySurgery c hg hcompat hcover hmaps hinj heq hdisj hsurj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_branchEquiv_of_boundarySurgery then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_branchEquiv_of_boundarySurgery"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_branchEquiv_of_boundarySurgery ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData.exists_branchEquiv_of_boundarySurgery

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
