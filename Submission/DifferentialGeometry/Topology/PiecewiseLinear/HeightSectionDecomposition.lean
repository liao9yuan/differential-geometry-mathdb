/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplexSection
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DiskCover
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.FiberFilling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Classical in
noncomputable def heightSectionCells (n : ℕ) (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (ℓ : E →ₗ[ℝ] ℝ) (r : ℝ) : Finset (Set E) :=
  ((Set.toFinite K.faces).toFinset.filter fun s => s.card = n + 2 ∧
    (∃ v ∈ s, ℓ v < r) ∧ ∃ w ∈ s, r < ℓ w).image
      (fun s : Finset E => convexHull ℝ (s : Set E) ∩ {x | ℓ x = r})

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.heightSectionCells then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.heightSectionCells"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.heightSectionCells ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.heightSectionCells

theorem mem_heightSectionCells_iff {n : ℕ} {K : Geometry.SimplicialComplex ℝ E}
    [Finite K.faces] {ℓ : E →ₗ[ℝ] ℝ} {r : ℝ} {C : Set E} :
    C ∈ heightSectionCells n K ℓ r ↔
      ∃ s ∈ K.faces, s.card = n + 2 ∧ (∃ v ∈ s, ℓ v < r) ∧
        (∃ w ∈ s, r < ℓ w) ∧ C = convexHull ℝ (s : Set E) ∩ {x | ℓ x = r} := by
  classical
  constructor
  · intro hC
    obtain ⟨s, hs, hC⟩ := Finset.mem_image.mp hC
    obtain ⟨hs, hcard, hbelow, habove⟩ := Finset.mem_filter.mp hs
    exact ⟨s, (Set.toFinite K.faces).mem_toFinset.mp hs, hcard, hbelow, habove, hC.symm⟩
  · rintro ⟨s, hs, hcard, hbelow, habove, rfl⟩
    exact Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr
      ⟨(Set.toFinite K.faces).mem_toFinset.mpr hs, hcard, hbelow, habove⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_heightSectionCells_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_heightSectionCells_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_heightSectionCells_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_heightSectionCells_iff

theorem subset_fiber_of_mem_heightSectionCells {n : ℕ} {K : Geometry.SimplicialComplex ℝ E}
    [Finite K.faces] {ℓ : E →ₗ[ℝ] ℝ} {r : ℝ} {C : Set E}
    (hC : C ∈ heightSectionCells n K ℓ r) : C ⊆ K.space ∩ {x | ℓ x = r} := by
  obtain ⟨s, hs, -, -, -, rfl⟩ := mem_heightSectionCells_iff.mp hC
  exact _root_.Set.inter_subset_inter_left _ (K.convexHull_subset_space hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subset_fiber_of_mem_heightSectionCells then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subset_fiber_of_mem_heightSectionCells"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subset_fiber_of_mem_heightSectionCells ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subset_fiber_of_mem_heightSectionCells

variable [FiniteDimensional ℝ E]

theorem isPLBall_of_mem_heightSectionCells {n : ℕ} {K : Geometry.SimplicialComplex ℝ E}
    [Finite K.faces] {ℓ : E →ₗ[ℝ] ℝ} {r : ℝ} {C : Set E}
    (hC : C ∈ heightSectionCells n K ℓ r) : IsPLBall n C := by
  obtain ⟨s, hs, hcard, hbelow, habove, rfl⟩ := mem_heightSectionCells_iff.mp hC
  exact isPLBall_convexHull_inter_fiber_of_affineIndependent s (K.indep hs) hcard
    ℓ.toAffineMap hbelow habove

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_of_mem_heightSectionCells then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_of_mem_heightSectionCells"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_of_mem_heightSectionCells ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_of_mem_heightSectionCells

theorem biUnion_heightSectionCells_eq_fiber
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hdim : Module.finrank ℝ E = 3) (hK : closure (interior K.space) = K.space)
    (ℓ : E →ₗ[ℝ] ℝ) (hinj : _root_.Set.InjOn ℓ K.vertices) (r : ℝ)
    (hD : IsPLBall 2 (K.space ∩ {x | ℓ x = r})) :
    (⋃ C ∈ heightSectionCells 2 K ℓ r, C) = K.space ∩ {x | ℓ x = r} := by
  have hclosed : IsClosed (⋃ C ∈ heightSectionCells 2 K ℓ r, C) :=
    (heightSectionCells 2 K ℓ r).finite_toSet.isClosed_biUnion
      (fun _ hC => (isPLBall_of_mem_heightSectionCells hC).isPolyhedron.isClosed)
  have hverts : K.vertices.Finite :=
    (Set.toFinite K.faces).preimage Finset.singleton_injective.injOn
  have hsub : (K.space ∩ {x | ℓ x = r}) \ K.vertices ⊆ ⋃ C ∈ heightSectionCells 2 K ℓ r, C := by
    rintro x ⟨⟨hx, hxr⟩, hxnot⟩
    obtain ⟨s, hs, hcard, hxs⟩ := exists_face_card_eq_finrank_succ_of_mem_closure
      K isOpen_interior interior_subset (hK.symm.subset hx)
    have hscard : s.card = 4 := by simpa only [hdim] using hcard
    have hsverts : (s : Set E) ⊆ K.vertices := fun v hv =>
      K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    rcases convexHull_inter_fiber_eq_singleton_or_exists_lt_and_gt s (K.indep hs)
      ℓ (hinj.mono hsverts) ⟨x, hxs, hxr⟩ with ⟨v, hv, heq⟩ | ⟨hbelow, habove⟩
    · have hxv : x = v := heq.subset ⟨hxs, hxr⟩
      exact (hxnot (hxv.symm ▸ hsverts hv)).elim
    · refine mem_iUnion₂.mpr ⟨convexHull ℝ (s : Set E) ∩ {x | ℓ x = r}, ?_, hxs, hxr⟩
      exact mem_heightSectionCells_iff.mpr ⟨s, hs, hscard, hbelow, habove, rfl⟩
  apply Subset.antisymm
  · exact _root_.Set.iUnion₂_subset fun _ hC => subset_fiber_of_mem_heightSectionCells hC
  · have h := closure_mono hsub
    rwa [hD.closure_sdiff_of_finite hverts, hclosed.closure_eq] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.biUnion_heightSectionCells_eq_fiber then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.biUnion_heightSectionCells_eq_fiber"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.biUnion_heightSectionCells_eq_fiber ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.biUnion_heightSectionCells_eq_fiber

theorem isPLBall_zero_or_one_inter_heightSectionCells
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (ℓ : E →ₗ[ℝ] ℝ) (hinj : _root_.Set.InjOn ℓ K.vertices) (r : ℝ) {C D : Set E}
    (hC : C ∈ heightSectionCells 2 K ℓ r) (hD : D ∈ heightSectionCells 2 K ℓ r)
    (hne : C ≠ D) (hinter : (C ∩ D).Nonempty) :
    IsPLBall 0 (C ∩ D) ∨ IsPLBall 1 (C ∩ D) := by
  obtain ⟨s, hs, hscard, -, -, rfl⟩ := mem_heightSectionCells_iff.mp hC
  obtain ⟨t, ht, htcard, -, -, rfl⟩ := mem_heightSectionCells_iff.mp hD
  exact isPLBall_zero_or_one_inter_face_fibers K hs ht hscard.le htcard.le
    (fun heq => hne (heq ▸ rfl)) ℓ hinj r hinter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_zero_or_one_inter_heightSectionCells then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_zero_or_one_inter_heightSectionCells"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_zero_or_one_inter_heightSectionCells ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_zero_or_one_inter_heightSectionCells

theorem exists_isPLDiskDecomposition_heightSectionCells
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hdim : Module.finrank ℝ E = 3) (hK : closure (interior K.space) = K.space)
    (ℓ : E →ₗ[ℝ] ℝ) (hinj : _root_.Set.InjOn ℓ K.vertices) (r : ℝ)
    (hD : IsPLBall 2 (K.space ∩ {x | ℓ x = r})) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧
      L.space = K.space ∩ {x | ℓ x = r} ∧
      IsPLDiskDecomposition L (heightSectionCells 2 K ℓ r) := by
  exact exists_isPLDiskDecomposition_of_cover hD (heightSectionCells 2 K ℓ r)
    (fun _ hC => isPLBall_of_mem_heightSectionCells hC)
    (biUnion_heightSectionCells_eq_fiber K hdim hK ℓ hinj r hD).symm
    (fun _ hC _ hD hne hnonempty =>
      isPLBall_zero_or_one_inter_heightSectionCells K ℓ hinj r hC hD hne hnonempty)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLDiskDecomposition_heightSectionCells then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLDiskDecomposition_heightSectionCells"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLDiskDecomposition_heightSectionCells ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLDiskDecomposition_heightSectionCells

open _root_.Classical in
theorem exists_isPLDiskDecomposition_fiber_of_heightIndex_eq_zero
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hS : IsPLSphere 2 (frontier K.space)) (hdim : Module.finrank ℝ E = 3)
    (hreg : closure (interior K.space) = K.space) (hconn : IsPreconnected (interior K.space))
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : _root_.Set.InjOn ℓ K.vertices)
    (hzero : heightIndex (frontier K.space) ℓ = 0) (r : ℝ)
    (hbelow : ∃ x ∈ frontier K.space, ℓ x < r) (habove : ∃ y ∈ frontier K.space, r < ℓ y) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧
      L.space = K.space ∩ {x | ℓ x = r} ∧
      IsPLDiskDecomposition L (heightSectionCells 2 K ℓ.toLinearMap r) ∧
      ∃ g : (Fin 3 → ℝ) → E,
        IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) (K.space ∩ {x | ℓ x = r}) ∧
        g '' stdSimplexBoundary 2 = frontier K.space ∩ {x | ℓ x = r} := by
  let B := boundaryComplex 3 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hBfront : frontier K.space = B.space :=
    frontier_space_eq_boundaryComplex_space_of_finrank hdim K hK
  have hB : IsPLSphere 2 B.space := hBfront ▸ hS
  have hBinj : _root_.Set.InjOn ℓ B.vertices := hinj.mono (fun _ hv => boundaryComplex_faces_subset 3 K hv)
  obtain ⟨g, hg, hgB⟩ := exists_isPLHomeomorphOn_filling_fiber_of_heightIndex_eq_zero
    B K hB hdim hBfront hreg hconn ℓ hℓ hBinj (hBfront ▸ hzero) r
      (hBfront ▸ hbelow) (hBfront ▸ habove)
  obtain ⟨L, hLfin, hLspace, hcells⟩ := exists_isPLDiskDecomposition_heightSectionCells
    K hdim hreg ℓ.toLinearMap hinj r ⟨g, hg⟩
  exact ⟨L, hLfin, hLspace, hcells, g, hg, hBfront.symm ▸ hgB⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLDiskDecomposition_fiber_of_heightIndex_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLDiskDecomposition_fiber_of_heightIndex_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLDiskDecomposition_fiber_of_heightIndex_eq_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLDiskDecomposition_fiber_of_heightIndex_eq_zero
end DifferentialGeometry.Topology.PiecewiseLinear
