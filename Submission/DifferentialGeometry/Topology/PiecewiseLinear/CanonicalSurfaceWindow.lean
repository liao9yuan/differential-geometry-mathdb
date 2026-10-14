/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceState

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def towerRemainder (T L : ℤ → Set E3) (P' : E3) (i : ℤ) : Set E3 :=
  {P'} ∪ ((⋃ j, ⋃ (_ : j ≠ i), T (2 * j)) ∪ (⋃ j, ⋃ (_ : j ≠ i - 1 ∧ j ≠ i), L j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.towerRemainder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.towerRemainder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.towerRemainder ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.towerRemainder

def replaceAdjacentSurfaces (X : ℤ → Geometry.SimplicialComplex ℝ E3) (i : ℤ)
    (Q₀ Q₁ : Geometry.SimplicialComplex ℝ E3) : ℤ → Geometry.SimplicialComplex ℝ E3 :=
  Function.update (Function.update X (i - 1) Q₀) i Q₁

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.replaceAdjacentSurfaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.replaceAdjacentSurfaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.replaceAdjacentSurfaces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.replaceAdjacentSurfaces

@[simp]
theorem replaceAdjacentSurfaces_left (X : ℤ → Geometry.SimplicialComplex ℝ E3) (i : ℤ)
    (Q₀ Q₁ : Geometry.SimplicialComplex ℝ E3) :
    replaceAdjacentSurfaces X i Q₀ Q₁ (i - 1) = Q₀ := by
  simp [replaceAdjacentSurfaces, show i - 1 ≠ i by omega]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.replaceAdjacentSurfaces_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.replaceAdjacentSurfaces_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.replaceAdjacentSurfaces_left ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.replaceAdjacentSurfaces_left

@[simp]
theorem replaceAdjacentSurfaces_right (X : ℤ → Geometry.SimplicialComplex ℝ E3) (i : ℤ)
    (Q₀ Q₁ : Geometry.SimplicialComplex ℝ E3) : replaceAdjacentSurfaces X i Q₀ Q₁ i = Q₁ := by
  simp [replaceAdjacentSurfaces]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.replaceAdjacentSurfaces_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.replaceAdjacentSurfaces_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.replaceAdjacentSurfaces_right ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.replaceAdjacentSurfaces_right

theorem replaceAdjacentSurfaces_of_ne (X : ℤ → Geometry.SimplicialComplex ℝ E3) (i : ℤ)
    (Q₀ Q₁ : Geometry.SimplicialComplex ℝ E3) {j : ℤ} (hj₀ : j ≠ i - 1) (hj₁ : j ≠ i) :
    replaceAdjacentSurfaces X i Q₀ Q₁ j = X j := by
  simp [replaceAdjacentSurfaces, hj₀, hj₁]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.replaceAdjacentSurfaces_of_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.replaceAdjacentSurfaces_of_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.replaceAdjacentSurfaces_of_ne ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.replaceAdjacentSurfaces_of_ne

theorem towerSurface_eq_remainder (T L : ℤ → Set E3) (P' : E3) (i : ℤ) :
    towerSurface T L P' = towerRemainder T L P' i ∪ (T (2 * i) ∪ (L (i - 1) ∪ L i)) := by
  ext x
  constructor
  · rintro (hx | hxP)
    · obtain ⟨j, hxT | hxL⟩ := mem_iUnion.mp hx
      · by_cases hji : j = i
        · exact Or.inr (Or.inl (hji ▸ hxT))
        · exact Or.inl (Or.inr (Or.inl (mem_iUnion₂.mpr ⟨j, hji, hxT⟩)))
      · by_cases hj₀ : j = i - 1
        · exact Or.inr (Or.inr (Or.inl (hj₀ ▸ hxL)))
        · by_cases hj₁ : j = i
          · exact Or.inr (Or.inr (Or.inr (hj₁ ▸ hxL)))
          · exact Or.inl (Or.inr (Or.inr (mem_iUnion₂.mpr ⟨j, ⟨hj₀, hj₁⟩, hxL⟩)))
    · exact Or.inl (Or.inl hxP)
  · rintro ((hxP | hxT | hxL) | hxT | hxL₀ | hxL₁)
    · exact Or.inr hxP
    · obtain ⟨j, -, hxT⟩ := mem_iUnion₂.mp hxT
      exact Or.inl (mem_iUnion.mpr ⟨j, Or.inl hxT⟩)
    · obtain ⟨j, -, hxL⟩ := mem_iUnion₂.mp hxL
      exact Or.inl (mem_iUnion.mpr ⟨j, Or.inr hxL⟩)
    · exact Or.inl (mem_iUnion.mpr ⟨i, Or.inl hxT⟩)
    · exact Or.inl (mem_iUnion.mpr ⟨i - 1, Or.inr hxL₀⟩)
    · exact Or.inl (mem_iUnion.mpr ⟨i, Or.inr hxL₁⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.towerSurface_eq_remainder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.towerSurface_eq_remainder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.towerSurface_eq_remainder ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.towerSurface_eq_remainder

theorem towerRemainder_replaceAdjacentSurfaces
    (X : ℤ → Geometry.SimplicialComplex ℝ E3) (T : ℤ → Set E3) (P' : E3) (i : ℤ)
    (Q₀ Q₁ : Geometry.SimplicialComplex ℝ E3) :
    towerRemainder T (fun j => (replaceAdjacentSurfaces X i Q₀ Q₁ j).space) P' i =
      towerRemainder T (fun j => (X j).space) P' i := by
  have hodd : (⋃ j, ⋃ (_ : j ≠ i - 1 ∧ j ≠ i),
      (replaceAdjacentSurfaces X i Q₀ Q₁ j).space) =
      ⋃ j, ⋃ (_ : j ≠ i - 1 ∧ j ≠ i), (X j).space := by
    apply _root_.Set.iUnion_congr
    intro j
    apply _root_.Set.iUnion_congr
    intro hj
    rw [replaceAdjacentSurfaces_of_ne X i Q₀ Q₁ hj.1 hj.2]
  simp only [towerRemainder, hodd]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.towerRemainder_replaceAdjacentSurfaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.towerRemainder_replaceAdjacentSurfaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.towerRemainder_replaceAdjacentSurfaces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.towerRemainder_replaceAdjacentSurfaces

theorem towerSurface_replaceAdjacentSurfaces
    (X : ℤ → Geometry.SimplicialComplex ℝ E3) (T : ℤ → Set E3) (P' : E3) (i : ℤ)
    (Q₀ Q₁ : Geometry.SimplicialComplex ℝ E3) :
    towerSurface T (fun j => (replaceAdjacentSurfaces X i Q₀ Q₁ j).space) P' =
      towerRemainder T (fun j => (X j).space) P' i ∪ (T (2 * i) ∪ (Q₀.space ∪ Q₁.space)) := by
  rw [towerSurface_eq_remainder T _ P' i, towerRemainder_replaceAdjacentSurfaces,
    replaceAdjacentSurfaces_left, replaceAdjacentSurfaces_right]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.towerSurface_replaceAdjacentSurfaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.towerSurface_replaceAdjacentSurfaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.towerSurface_replaceAdjacentSurfaces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.towerSurface_replaceAdjacentSurfaces

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' a b : E3}

theorem IsCanonicalSurface.remainder_disjoint_interior_outer [DecidableEq E3]
    {X : ℤ → Geometry.SimplicialComplex ℝ E3}
    (h : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    Disjoint (towerRemainder T'' (fun j => (X j).space) P' i) (interior (φ '' S (2 * i))) := by
  apply disjoint_left.mpr
  rintro x (hxP | hxEven | hxOdd) hxO
  · exact htw.center_notMem_interior_outer _ (hxP ▸ hxO)
  · obtain ⟨j, hji, hxT⟩ := mem_iUnion₂.mp hxEven
    exact disjoint_left.mp (htw.apart (2 * j) (2 * i) (by rw [le_abs]; omega))
      (htw.boundary_subset_outer _ hxT) (interior_subset hxO)
  · obtain ⟨j, ⟨hj₀, hj₁⟩, hxj⟩ := mem_iUnion₂.mp hxOdd
    rcases h.carrier j hxj with (hxLo | hxMid) | hxHi
    · exact disjoint_left.mp (htw.apart (2 * j) (2 * i) (by rw [le_abs]; omega))
        hxLo (interior_subset hxO)
    · exact disjoint_left.mp (htw.apart (2 * j + 1) (2 * i) (by rw [le_abs]; omega))
        hxMid (interior_subset hxO)
    · exact disjoint_left.mp (htw.apart (2 * (j + 1)) (2 * i) (by rw [le_abs]; omega))
        hxHi (interior_subset hxO)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.remainder_disjoint_interior_outer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.remainder_disjoint_interior_outer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.remainder_disjoint_interior_outer ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.remainder_disjoint_interior_outer

theorem IsCanonicalSurface.boundary_inter_interior_outer_subset [DecidableEq E3]
    {X : ℤ → Geometry.SimplicialComplex ℝ E3}
    (h : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (j i : ℤ) :
    (boundaryComplex 2 (X j)).space ∩ interior (φ '' S (2 * i)) ⊆ T'' (2 * i) := by
  have heven (k : ℤ) {x : E3} (hxT : x ∈ T'' (2 * k))
      (hxO : x ∈ interior (φ '' S (2 * i))) : x ∈ T'' (2 * i) := by
    by_cases hki : k = i
    · exact hki ▸ hxT
    · exact (disjoint_left.mp (htw.apart (2 * k) (2 * i) (by rw [le_abs]; omega))
        (htw.boundary_subset_outer _ hxT) (interior_subset hxO)).elim
  rintro x ⟨hxB, hxO⟩
  rw [h.boundary j] at hxB
  rcases hxB.2 with hxT | hxT
  · exact heven j hxT hxO
  · exact heven (j + 1) hxT hxO

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.boundary_inter_interior_outer_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.boundary_inter_interior_outer_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.boundary_inter_interior_outer_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalSurface.boundary_inter_interior_outer_subset

end DifferentialGeometry.Topology.PiecewiseLinear
