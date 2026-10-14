/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryOfBall
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ControlledInwardPush
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceTowerExistence
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralBallTopology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Link

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Classical in
theorem IsCombinatorialManifold.not_subsingleton_space {m : ℕ}
    {L : Geometry.SimplicialComplex ℝ E} (hL : IsCombinatorialManifold (m + 1) L)
    (hne : L.space.Nonempty) : ¬ L.space.Subsingleton := by
  intro hsub
  obtain ⟨q, hq⟩ := hne
  obtain ⟨s, hs, -⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hq
  obtain ⟨v, hv⟩ := L.nonempty_of_mem_faces hs
  have hvspace : v ∈ L.space :=
    L.convexHull_subset_space hs (subset_convexHull ℝ _ hv)
  have hvface : ({v} : Finset E) ∈ L.faces :=
    L.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  obtain ⟨z, hz⟩ := (hL v hvface).nonempty
  obtain ⟨t, ht, -⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hz
  obtain ⟨htne, hvt, htins⟩ := (SimplicialComplex.mem_geometricLink_singleton L v t).mp ht
  obtain ⟨w, hw⟩ := htne
  have hwspace : w ∈ L.space :=
    L.convexHull_subset_space htins (subset_convexHull ℝ _ (Finset.mem_insert_of_mem hw))
  exact hvt (by rw [hsub hvspace hwspace]; exact hw)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.not_subsingleton_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.not_subsingleton_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.not_subsingleton_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.not_subsingleton_space

open _root_.Classical in
theorem IsCombinatorialManifold.exists_mem_ne_of_mem_nhds {m : ℕ}
    {L : Geometry.SimplicialComplex ℝ E} (hL : IsCombinatorialManifold (m + 1) L) {z : E}
    (hz : z ∈ L.space) {U : Set E} (hU : U ∈ 𝓝 z) : ∃ y ∈ U ∩ L.space, y ≠ z := by
  obtain ⟨u, hune, hseg⟩ : ∃ u : E, u ≠ z ∧ segment ℝ z u ⊆ L.space := by
    obtain ⟨s, hs, hzs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hz
    obtain ⟨v, hv⟩ := L.nonempty_of_mem_faces hs
    by_cases hvz : v = z
    · have hvface : ({v} : Finset E) ∈ L.faces :=
        L.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
      obtain ⟨p, hp⟩ := (hL v hvface).nonempty
      obtain ⟨t, ht, -⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hp
      obtain ⟨htne, hvt, htins⟩ := (SimplicialComplex.mem_geometricLink_singleton L v t).mp ht
      obtain ⟨w, hw⟩ := htne
      have hwv : w ≠ v := fun hwv => hvt (hwv ▸ hw)
      refine ⟨w, by rw [← hvz]; exact hwv, subset_trans ?_ (L.convexHull_subset_space htins)⟩
      refine (convex_convexHull ℝ _).segment_subset ?_ (subset_convexHull ℝ _ (by simp [hw]))
      rw [← hvz]
      exact subset_convexHull ℝ _ (by simp)
    · refine ⟨v, hvz, subset_trans ?_ (L.convexHull_subset_space hs)⟩
      exact (convex_convexHull ℝ _).segment_subset hzs (subset_convexHull ℝ _ hv)
  have hcont : Continuous fun a : ℝ => z + a • (u - z) := by
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hpre : (fun a : ℝ => z + a • (u - z)) ⁻¹' U ∈ 𝓝 (0 : ℝ) := by
    refine hcont.continuousAt.preimage_mem_nhds ?_
    simpa using hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hapos : 0 < _root_.Min.min (ε / 2) 1 := lt_min (by positivity) one_pos
  have haU : z + _root_.Min.min (ε / 2) 1 • (u - z) ∈ U := by
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hapos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨z + _root_.Min.min (ε / 2) 1 • (u - z), ⟨haU, hseg ?_⟩, ?_⟩
  · rw [segment_eq_image']
    exact ⟨min (ε / 2) 1, ⟨hapos.le, min_le_right _ _⟩, rfl⟩
  · intro heq
    rcases smul_eq_zero.mp (add_eq_left.mp heq) with hzero | hzero
    · exact hapos.ne' hzero
    · exact hune (by rwa [sub_eq_zero] at hzero)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_mem_ne_of_mem_nhds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_mem_ne_of_mem_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_mem_ne_of_mem_nhds ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.exists_mem_ne_of_mem_nhds

end Link

section LocalManifold

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

theorem IsPolyhedralManifold.not_subsingleton {k : ℕ} {S : Set X}
    (hS : IsPolyhedralManifold (n := n) (k + 1) S) (hne : S.Nonempty) : ¬ S.Subsingleton := by
  intro hsub
  obtain ⟨T, hT⟩ := hS
  obtain ⟨y, hy⟩ := hne
  obtain ⟨z, hz, -⟩ := T.piece.bijOn.surjOn hy
  refine hT.not_subsingleton_space ⟨z, hz⟩ ?_
  intro u hu v hv
  exact T.piece.bijOn.injOn hu hv (hsub (T.piece.bijOn.mapsTo hu) (T.piece.bijOn.mapsTo hv))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.not_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.not_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.not_subsingleton ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.not_subsingleton

theorem IsPolyhedralManifold.exists_mem_ne_of_mem_nhds {k : ℕ} {S : Set X}
    (hS : IsPolyhedralManifold (n := n) (k + 1) S) {x : X} (hx : x ∈ S) {U : Set X}
    (hU : U ∈ 𝓝 x) : ∃ y ∈ U ∩ S, y ≠ x := by
  obtain ⟨T, hT⟩ := hS
  obtain ⟨z, hz, hzx⟩ := T.piece.bijOn.surjOn hx
  have hUz : U ∈ 𝓝 (T.piece.map z) := by rw [hzx]; exact hU
  have hpre : T.piece.map ⁻¹' U ∈ 𝓝[T.piece.complex.space] z :=
    (T.piece.continuousOn.continuousWithinAt hz).preimage_mem_nhdsWithin hUz
  obtain ⟨V, hV, hzV, hVsub⟩ := mem_nhdsWithin.mp hpre
  obtain ⟨y, hy, hyz⟩ := hT.exists_mem_ne_of_mem_nhds hz (hV.mem_nhds hzV)
  refine ⟨T.piece.map y, ⟨hVsub ⟨hy.1, hy.2⟩, T.piece.bijOn.mapsTo hy.2⟩, ?_⟩
  intro heq
  exact hyz (T.piece.bijOn.injOn hy.2 hz (heq.trans hzx.symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_mem_ne_of_mem_nhds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_mem_ne_of_mem_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_mem_ne_of_mem_nhds ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.exists_mem_ne_of_mem_nhds

def IsLocallyPolyhedralManifold (m : ℕ) (S : Set X) : Prop :=
  ∀ x ∈ S, ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∃ P : Set X,
    IsPolyhedralManifold (n := n) m P ∧ O ∩ S = O ∩ P

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedralManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedralManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedralManifold ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedralManifold

theorem IsPolyhedralManifold.isLocallyPolyhedralManifold {m : ℕ} {S : Set X}
    (hS : IsPolyhedralManifold (n := n) m S) : IsLocallyPolyhedralManifold (n := n) m S :=
  fun x _ => ⟨univ, isOpen_univ, _root_.Set.mem_univ x, S, hS, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isLocallyPolyhedralManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isLocallyPolyhedralManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isLocallyPolyhedralManifold ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifold.isLocallyPolyhedralManifold

theorem IsLocallyPolyhedralManifold.not_isolated {k : ℕ} {S : Set X}
    (hS : IsLocallyPolyhedralManifold (n := n) (k + 1) S) {x : X} (hx : x ∈ S) {U : Set X}
    (hU : U ∈ 𝓝 x) : ∃ y ∈ U ∩ S, y ≠ x := by
  obtain ⟨O, hO, hxO, P, hP, heq⟩ := hS x hx
  have hxP : x ∈ P := (heq.subset ⟨hxO, hx⟩).2
  obtain ⟨y, hy, hyx⟩ :=
    hP.exists_mem_ne_of_mem_nhds hxP (Filter.inter_mem hU (hO.mem_nhds hxO))
  exact ⟨y, ⟨hy.1.1, (heq.symm.subset ⟨hy.1.2, hy.2⟩).2⟩, hyx⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedralManifold
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedralManifold.not_isolated then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedralManifold.not_isolated"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedralManifold.not_isolated ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyPolyhedralManifold.not_isolated

end LocalManifold

section RelativeBoundary

theorem inter_frontier_eq_sdiff_interior {Y : Type*} [TopologicalSpace Y] (K : Set Y) :
    K ∩ frontier K = K \ interior K := by
  ext y
  constructor
  · rintro ⟨hy, -, hyi⟩
    exact ⟨hy, hyi⟩
  · rintro ⟨hy, hyi⟩
    exact ⟨hy, subset_closure hy, hyi⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.inter_frontier_eq_sdiff_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.inter_frontier_eq_sdiff_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.inter_frontier_eq_sdiff_interior ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.inter_frontier_eq_sdiff_interior

private theorem inter_interior_eq_of_inter_eq {Y : Type*} [TopologicalSpace Y] {O A B : Set Y}
    (hO : IsOpen O) (h : O ∩ A = O ∩ B) : O ∩ interior A = O ∩ interior B := by
  have key : ∀ C D : Set Y, O ∩ C = O ∩ D → O ∩ interior C ⊆ O ∩ interior D := by
    intro C D hCD
    refine _root_.Set.subset_inter _root_.Set.inter_subset_left (interior_maximal ?_ (hO.inter isOpen_interior))
    intro y hy
    have hyC : y ∈ O ∩ C := ⟨hy.1, interior_subset hy.2⟩
    rw [hCD] at hyC
    exact hyC.2
  exact Subset.antisymm (key A B h) (key B A h.symm)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.inter_interior_eq_of_inter_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.inter_interior_eq_of_inter_eq target :: scope.openDecls } }

end RelativeBoundary

section Frontier

variable {m : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X]

open _root_.Classical in
theorem IsPolyhedralManifoldWithBoundary.isPolyhedralManifold_frontier {P : Set X}
    (hP : IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) P) :
    IsPolyhedralManifold (n := m + 1) m (frontier P) := by
  classical
  obtain ⟨T, hT⟩ := hP
  let _ : DecidableEq (EuclideanSpace ℝ (Fin T.ambientDim)) := Classical.decEq _
  have _ : Finite T.piece.complex.faces := T.piece.finite_faces.to_subtype
  rw [T.piece.frontier_eq_image_boundaryComplex hT]
  refine isPolyhedralManifold_of_pieceIn
    (T.piece.restrict (boundaryComplex (m + 1) T.piece.complex)
      (boundaryComplex_faces_subset (m + 1) T.piece.complex)) ?_
  simpa only [PLPieceIn.restrict_complex] using
    isCombinatorialManifold_boundaryComplex T.piece.complex hT

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.isPolyhedralManifold_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.isPolyhedralManifold_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.isPolyhedralManifold_frontier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.isPolyhedralManifold_frontier

omit [T2Space X] in
theorem IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_eq {K : Set X}
    (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K) {x : X}
    (hx : x ∈ K) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∃ P : Set X,
      IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) P ∧ P ⊆ K ∧
        O ∩ K = O ∩ P := by
  obtain ⟨T, hT⟩ := hK
  have hxU : x ∈ ⋃ i, T.N i := by rw [T.iUnion_eq]; exact hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
  obtain ⟨O, hO, hxO, hOsub⟩ := mem_nhdsWithin.mp (T.subset_nhdsWithin i x hi)
  refine ⟨O, hO, hxO, T.N (i + 1), ⟨T.piece (i + 1), hT (i + 1)⟩, T.subset (i + 1), ?_⟩
  exact Subset.antisymm (fun y hy => ⟨hy.1, hOsub hy⟩)
    (fun y hy => ⟨hy.1, T.subset (i + 1) hy.2⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_eq

theorem IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_sdiff_interior_eq
    {K : Set X} (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K)
    {x : X} (hx : x ∈ K) :
    ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∃ S : Set X, IsPolyhedralManifold (n := m + 1) m S ∧
      O ∩ (K \ interior K) = O ∩ S := by
  obtain ⟨O, hO, hxO, P, hP, -, hOP⟩ := hK.exists_isOpen_inter_eq hx
  refine ⟨O, hO, hxO, frontier P, hP.isPolyhedralManifold_frontier, ?_⟩
  have hint := inter_interior_eq_of_inter_eq hO hOP
  have hKP : ∀ y ∈ O, (y ∈ K ↔ y ∈ P) := fun y hy =>
    ⟨fun hyK => (hOP.subset ⟨hy, hyK⟩).2, fun hyP => (hOP.symm.subset ⟨hy, hyP⟩).2⟩
  have hIP : ∀ y ∈ O, (y ∈ interior K ↔ y ∈ interior P) := fun y hy =>
    ⟨fun hyK => (hint.subset ⟨hy, hyK⟩).2, fun hyP => (hint.symm.subset ⟨hy, hyP⟩).2⟩
  rw [hP.isCompact.isClosed.frontier_eq]
  ext y
  simp only [_root_.Set.mem_inter_iff, _root_.Set.mem_sdiff]
  constructor
  · rintro ⟨hyO, hyK, hyni⟩
    exact ⟨hyO, (hKP y hyO).mp hyK, fun hyi => hyni ((hIP y hyO).mpr hyi)⟩
  · rintro ⟨hyO, hyP, hyni⟩
    exact ⟨hyO, (hKP y hyO).mpr hyP, fun hyi => hyni ((hIP y hyO).mp hyi)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_sdiff_interior_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_sdiff_interior_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_sdiff_interior_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyFinitePolyhedralManifoldWithBoundary.exists_isOpen_inter_sdiff_interior_eq

theorem IsLocallyFinitePolyhedralManifoldWithBoundary.isLocallyPolyhedralManifold_sdiff_interior
    {K : Set X} (hK : IsLocallyFinitePolyhedralManifoldWithBoundary (n := m + 1) (m + 1) K) :
    IsLocallyPolyhedralManifold (n := m + 1) m (K \ interior K) :=
  fun _ hx => hK.exists_isOpen_inter_sdiff_interior_eq hx.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyFinitePolyhedralManifoldWithBoundary.isLocallyPolyhedralManifold_sdiff_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyFinitePolyhedralManifoldWithBoundary.isLocallyPolyhedralManifold_sdiff_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyFinitePolyhedralManifoldWithBoundary.isLocallyPolyhedralManifold_sdiff_interior ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLocallyFinitePolyhedralManifoldWithBoundary.isLocallyPolyhedralManifold_sdiff_interior

end Frontier

section Witnesses

theorem exists_isLocallyFinitePolyhedralManifoldWithBoundary_sdiff_interior_nonempty :
    ∃ K : Set (EuclideanSpace ℝ (Fin 3)),
      IsLocallyFinitePolyhedralManifoldWithBoundary (n := 3) 3 K ∧ (frontier K).Nonempty ∧
        (K \ interior K).Nonempty ∧ frontier K = K \ interior K ∧
        IsPolyhedralManifold (n := 3) 2 (frontier K) ∧
        IsLocallyPolyhedralManifold (n := 3) 2 (K \ interior K) := by
  obtain ⟨K, hK, hfr⟩ := exists_isPolyhedralManifoldWithBoundary_frontier_nonempty
  have hcl : IsClosed K := hK.isCompact.isClosed
  have hlf := hK.isLocallyFinite
  refine ⟨K, hlf, hfr, ?_, hcl.frontier_eq, hK.isPolyhedralManifold_frontier (m := 2),
    hlf.isLocallyPolyhedralManifold_sdiff_interior (m := 2)⟩
  rw [← hcl.frontier_eq]
  exact hfr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isLocallyFinitePolyhedralManifoldWithBoundary_sdiff_interior_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isLocallyFinitePolyhedralManifoldWithBoundary_sdiff_interior_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isLocallyFinitePolyhedralManifoldWithBoundary_sdiff_interior_nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isLocallyFinitePolyhedralManifoldWithBoundary_sdiff_interior_nonempty

theorem exists_isLocallyFinitePolyhedralManifoldWithBoundary_frontier_point :
    ∃ K : Set (EuclideanSpace ℝ (Fin 3)),
      IsLocallyFinitePolyhedralManifoldWithBoundary (n := 3) 3 K ∧ (frontier K).Nonempty ∧
        Disjoint (frontier K) K ∧ K \ interior K = ∅ ∧
        ¬ IsPolyhedralManifold (n := 3) 2 (frontier K) ∧
        ¬ IsLocallyPolyhedralManifold (n := 3) 2 (frontier K) := by
  have hint : interior ({0} : Set (EuclideanSpace ℝ (Fin 3))) = ∅ := interior_singleton 0
  have hfr : frontier (({0} : Set (EuclideanSpace ℝ (Fin 3)))ᶜ) = {0} := by
    rw [frontier_compl, isClosed_singleton.frontier_eq, hint, _root_.Set.sdiff_empty]
  refine ⟨({0} : Set (EuclideanSpace ℝ (Fin 3)))ᶜ,
    isLocallyFinitePolyhedralManifoldWithBoundary_of_isOpen (m := 2) isOpen_compl_singleton,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr]
    exact _root_.Set.singleton_nonempty 0
  · rw [hfr]
    exact disjoint_compl_right
  · rw [isOpen_compl_singleton.interior_eq, _root_.Set.sdiff_self]
  · rw [hfr]
    intro h
    exact h.not_subsingleton (_root_.Set.singleton_nonempty 0) _root_.Set.subsingleton_singleton
  · rw [hfr]
    intro h
    obtain ⟨y, hy, hyne⟩ := h.not_isolated (x := 0) rfl (U := _root_.Set.univ) Filter.univ_mem
    exact hyne hy.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isLocallyFinitePolyhedralManifoldWithBoundary_frontier_point then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isLocallyFinitePolyhedralManifoldWithBoundary_frontier_point"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isLocallyFinitePolyhedralManifoldWithBoundary_frontier_point ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isLocallyFinitePolyhedralManifoldWithBoundary_frontier_point

end Witnesses

end DifferentialGeometry.Topology.PiecewiseLinear
