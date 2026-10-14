import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CylinderCut
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CylindricalMeridian
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34InnermostSubdisk
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalMeridianBarrier
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusProduct

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem frontier_inter_interior_union_subset_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) :
    frontier A ∩ interior (A ∪ B) ⊆ A ∩ B := by
  rintro x ⟨hxA, hxS⟩
  refine ⟨hA.frontier_subset hxA, ?_⟩
  by_contra hxB
  have hsub : interior (A ∪ B) \ B ⊆ A :=
    fun y hy => (interior_subset hy.1).resolve_right hy.2
  exact hxA.2 (interior_maximal hsub (isOpen_interior.sdiff hB) ⟨hxS, hxB⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.frontier_inter_interior_union_subset_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.frontier_inter_interior_union_subset_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.frontier_inter_interior_union_subset_inter ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.frontier_inter_interior_union_subset_inter

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsCylindricalDiagram.inter_cut_frontier_subset_slices
    {f : E × ℝ → F} {P : Set E} {S K : Set F}
    (hf : IsCylindricalDiagram f P S) (hP : IsPLBall 2 P) (hKS : K ⊆ interior S) :
    K ∩ frontier (f '' (P ×ˢ _root_.Set.Icc (0 : ℝ) (1 / 2))) ⊆
      f '' (P ×ˢ {(0 : ℝ)}) ∪ f '' (P ×ˢ {(1 / 2 : ℝ)}) := by
  obtain ⟨A, B, -, -, hA, hB, hAsp, -, hcover, hinter, -⟩ :=
    hf.exists_ball_pair_with_boundary hP (a := 1 / 2) (by norm_num)
  rw [← hAsp, ← hinter]
  intro x hx
  apply frontier_inter_interior_union_subset_inter hA.isPolyhedron.isClosed
    hB.isPolyhedron.isClosed
  exact ⟨hx.2, hcover.symm ▸ hKS hx.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.inter_cut_frontier_subset_slices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.inter_cut_frontier_subset_slices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.inter_cut_frontier_subset_slices ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.inter_cut_frontier_subset_slices

theorem IsCylindricalDiagram.inter_cut_frontier_nonempty_of_carrier
    {f : E × ℝ → EuclideanSpace ℝ (Fin 3)} {P : Set E}
    {S K : Set (EuclideanSpace ℝ (Fin 3))}
    (hf : IsCylindricalDiagram f P S) (hP : IsPLBall 2 P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1)) (hK : IsCompact K) (hne : K.Nonempty)
    (hgen : CarriesFundamentalGroupOnto K S) :
    (K ∩ frontier (f '' (P ×ˢ _root_.Set.Icc (0 : ℝ) (1 / 2)))).Nonempty := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨A, B, hAfin, -, hA, hB, hAsp, -, hcover, -, -, -, -, h₀A, -⟩ :=
    hf.exists_ball_pair_with_boundary hP (a := 1 / 2) (by norm_num)
  let _ : Finite A.faces := hAfin.to_subtype
  have hSpoly : IsPolyhedron S := hcover ▸ hA.isPolyhedron.union hB.isPolyhedron
  have hu := isPLHomeomorphInto_id_of_isPolyhedron hSpoly
  have htor : IsTopologicalSolidTorus (id '' S) := by
    simpa only [_root_.Set.image_id] using hf.isTopologicalSolidTorus_of_eq_ends hP hends
  have hgen' : CarriesFundamentalGroupOnto K (id '' S) := by
    simpa only [_root_.Set.image_id] using hgen
  obtain ⟨x, hxK, hxD⟩ := hu.inter_nonempty_cylindrical_meridian_of_carrier hP hf
    Subset.rfl htor hK hne hgen'
  rw [_root_.Set.image_id] at hxD
  have hbd : (boundaryComplex 3 A).space = frontier A.space :=
    (frontier_space_eq_boundaryComplex_space_of_finrank (by simp) A
      hA.isCombinatorialManifoldWithBoundary).symm
  exact ⟨x, hxK, hAsp ▸ hbd ▸ h₀A hxD⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.inter_cut_frontier_nonempty_of_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.inter_cut_frontier_nonempty_of_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.inter_cut_frontier_nonempty_of_carrier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.inter_cut_frontier_nonempty_of_carrier

open _root_.Classical in
theorem IsCylindricalDiagram.exists_innermost_cut_disk
    (D : Geometry.SimplicialComplex ℝ E) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : IsPLBall 2 D.space)
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    {f : E × ℝ → F} (hf : IsCylindricalDiagram f D.space M.space)
    (hends : ∀ x ∈ (boundaryComplex 2 D).space, f (x, 0) = f (x, 1))
    (hdim : Module.finrank ℝ F = 3) {K : Set F} (hKS : K ⊆ interior M.space)
    {ι : Type*} [Finite ι] [Nonempty ι] {J : ι → Set F}
    (hJ : ∀ i, IsPLSphere 1 (J i))
    (hdisj : Pairwise fun i j => Disjoint (J i) (J j))
    (htrace : K ∩ frontier (f '' (D.space ×ˢ _root_.Set.Icc (0 : ℝ) (1 / 2))) = ⋃ i, J i) :
    ∃ (i : ι) (Q : Set F) (q : (Fin 3 → ℝ) → F),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) Q ∧
      Q ⊆ frontier (f '' (D.space ×ˢ _root_.Set.Icc (0 : ℝ) (1 / 2))) ∩ interior M.space ∧
      q '' stdSimplexBoundary 2 = J i ∧ Q ∩ K = J i ∧
      ∀ j, j ≠ i → Disjoint Q (J j) := by
  classical
  obtain ⟨A, B, hAfin, -, hA, -, hAsp, -, -, -, hD₀, hD₁, hdis, h₀A, h₁A, -⟩ :=
    hf.exists_ball_pair_with_boundary hD (a := 1 / 2) (by norm_num)
  let _ : Finite A.faces := hAfin.to_subtype
  have hbdA : (boundaryComplex 3 A).space = frontier A.space :=
    (frontier_space_eq_boundaryComplex_space_of_finrank hdim A
      hA.isCombinatorialManifoldWithBoundary).symm
  rw [hbdA] at h₀A h₁A
  have hS : IsPLSphere 2 (frontier A.space) := by
    rw [← hbdA]
    exact isPLSphere_boundaryComplex_space_of_isPLBall A hA
  have hJS (i : ι) : J i ⊆ frontier A.space := by
    intro x hx
    rw [hAsp]
    exact (htrace.superset (mem_iUnion.mpr ⟨i, hx⟩)).2
  have hJK (i : ι) : J i ⊆ K :=
    fun _ hx => (htrace.superset (mem_iUnion.mpr ⟨i, hx⟩)).1
  have hplace (i : ι) : J i ⊆ f '' (D.space ×ˢ {(0 : ℝ)}) ∨
      J i ⊆ f '' (D.space ×ˢ {(1 / 2 : ℝ)}) := by
    have hsub := (htrace.superset.trans (hf.inter_cut_frontier_subset_slices hD hKS))
    apply isPreconnected_iff_subset_of_disjoint_closed.mp (hJ i).isConnected.isPreconnected
      _ _ hD₀.isPolyhedron.isClosed hD₁.isPolyhedron.isClosed
      ((_root_.Set.subset_iUnion J i).trans hsub)
    rw [hdis.inter_eq, _root_.Set.inter_empty]
  have hslice (t : ℝ) (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1)
      (hside : f '' (D.space ×ˢ {t}) ⊆ frontier A.space) {i : ι}
      (hi : J i ⊆ f '' (D.space ×ˢ {t})) :
      ∃ (Q : Set F) (q : (Fin 3 → ℝ) → F),
        IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) Q ∧
        Q ⊆ frontier A.space ∩ interior M.space ∧ q '' stdSimplexBoundary 2 = J i := by
    obtain ⟨r, hr, hrbd, -, -, hmeet, -, hinside, -⟩ :=
      hf.exists_essential_slice_disk D M hD hM hends hdim ht
    have hi' : J i ⊆ f '' (D.space ×ˢ {t}) \ r '' stdSimplexBoundary 2 := by
      intro x hx
      refine ⟨hi hx, ?_⟩
      rw [hrbd]
      intro hxrim
      exact (hmeet.superset hxrim).1.2 (hKS (hJK i hx))
    obtain ⟨Q, q, hq, hQD, hqJ⟩ := hS.exists_disk_in_disk_sdiff_boundary hr hside (hJ i) hi'
    have hQint : Q ⊆ interior M.space := by
      apply (hQD.trans ?_).trans hinside
      rw [hrbd]
    exact ⟨Q, q, hq, fun x hx => ⟨hside (hQD hx).1, hQint hx⟩, hqJ⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hex : ∃ (i : ι) (Q : Set F) (q : (Fin 3 → ℝ) → F),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) Q ∧
      Q ⊆ frontier A.space ∩ interior M.space ∧ q '' stdSimplexBoundary 2 = J i := by
    rcases hplace i with hi | hi
    · obtain ⟨Q, q, hq⟩ := hslice 0 (by norm_num) h₀A hi
      exact ⟨i, Q, q, hq⟩
    · obtain ⟨Q, q, hq⟩ := hslice (1 / 2) (by norm_num) h₁A hi
      exact ⟨i, Q, q, hq⟩
  obtain ⟨i, Q, q, hq, hQS, hqJ, hQother⟩ :=
    hS.exists_innermost_disk_subset _root_.Set.inter_subset_left hJ hJS hdisj hex
  have hJKQ : J i ⊆ Q := by
    rw [← hqJ, ← hq.image_eq]
    exact _root_.Set.image_mono fun _ hx => hx.1
  have hQK : Q ∩ K = J i := by
    apply Subset.antisymm
    · rintro x ⟨hxQ, hxK⟩
      have hxtrace : x ∈ ⋃ j, J j := htrace.subset ⟨hxK, hAsp ▸ (hQS hxQ).1⟩
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxtrace
      by_cases hji : j = i
      · exact hji ▸ hxj
      · exact (disjoint_left.mp (hQother j hji) hxQ hxj).elim
    · exact fun x hx => ⟨hJKQ hx, hJK i hx⟩
  exact ⟨i, Q, q, hq, hAsp ▸ hQS, hqJ, hQK, hQother⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_innermost_cut_disk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_innermost_cut_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_innermost_cut_disk ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_innermost_cut_disk

open _root_.Classical in
theorem IsCylindricalDiagram.exists_innermost_cut_disk_of_carrier
    (D : Geometry.SimplicialComplex ℝ E)
    (M : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite D.faces] [Finite M.faces] (hD : IsPLBall 2 D.space)
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    {f : E × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : IsCylindricalDiagram f D.space M.space)
    (hends : ∀ x ∈ D.space, f (x, 0) = f (x, 1))
    {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K) (hne : K.Nonempty)
    (hKS : K ⊆ interior M.space) (hgen : CarriesFundamentalGroupOnto K M.space)
    {ι : Type*} [Finite ι] {J : ι → Set (EuclideanSpace ℝ (Fin 3))}
    (hJ : ∀ i, IsPLSphere 1 (J i))
    (hdisj : Pairwise fun i j => Disjoint (J i) (J j))
    (htrace : K ∩ frontier (f '' (D.space ×ˢ _root_.Set.Icc (0 : ℝ) (1 / 2))) = ⋃ i, J i) :
    ∃ (i : ι) (Q : Set (EuclideanSpace ℝ (Fin 3)))
      (q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) Q ∧
      Q ⊆ frontier (f '' (D.space ×ˢ _root_.Set.Icc (0 : ℝ) (1 / 2))) ∩ interior M.space ∧
      q '' stdSimplexBoundary 2 = J i ∧ Q ∩ K = J i ∧
      ∀ j, j ≠ i → Disjoint Q (J j) := by
  obtain ⟨x, hx⟩ := hf.inter_cut_frontier_nonempty_of_carrier hD hends hK hne hgen
  obtain ⟨i, -⟩ := mem_iUnion.mp (htrace.subset hx)
  let _ : Nonempty ι := ⟨i⟩
  exact hf.exists_innermost_cut_disk D M hD hM
    (fun x hx => hends x (boundaryComplex_space_subset 2 D hx)) (by simp) hKS hJ hdisj htrace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_innermost_cut_disk_of_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_innermost_cut_disk_of_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_innermost_cut_disk_of_carrier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_innermost_cut_disk_of_carrier

end DifferentialGeometry.Topology.PiecewiseLinear
