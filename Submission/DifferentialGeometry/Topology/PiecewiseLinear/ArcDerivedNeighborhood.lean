/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallChain
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodAttachments
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCells

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Faces

variable {E : Type*}

open _root_.Classical in
noncomputable def arcChainFace (v : ℕ → E) (j : ℕ) : Finset E :=
  {v (j / 2), v ((j + 1) / 2)}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace

open _root_.Classical in
theorem mem_arcChainFace_iff {v : ℕ → E} {j : ℕ} {x : E} :
    x ∈ arcChainFace v j ↔ x = v (j / 2) ∨ x = v ((j + 1) / 2) := by
  simp only [arcChainFace, Finset.mem_insert, Finset.mem_singleton]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_arcChainFace_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_arcChainFace_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_arcChainFace_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_arcChainFace_iff

open _root_.Classical in
theorem arcChainFace_two_mul (v : ℕ → E) (k : ℕ) : arcChainFace v (2 * k) = {v k} := by
  have h₁ : 2 * k / 2 = k := by omega
  have h₂ : (2 * k + 1) / 2 = k := by omega
  simp only [arcChainFace, h₁, h₂, Finset.pair_eq_singleton]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace_two_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace_two_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace_two_mul ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace_two_mul

open _root_.Classical in
theorem arcChainFace_two_mul_add_one (v : ℕ → E) (k : ℕ) :
    arcChainFace v (2 * k + 1) = {v k, v (k + 1)} := by
  have h₁ : (2 * k + 1) / 2 = k := by omega
  have h₂ : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  simp only [arcChainFace, h₁, h₂]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace_two_mul_add_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace_two_mul_add_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace_two_mul_add_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace_two_mul_add_one

theorem eq_of_subset_pair [DecidableEq E] {a b : E} {t : Finset E}
    (ht : t ⊆ ({a, b} : Finset E)) (hne : t.Nonempty) :
    t = {a} ∨ t = {b} ∨ t = ({a, b} : Finset E) := by
  have hmem : ∀ x ∈ t, x = a ∨ x = b := fun x hx => by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using ht hx
  by_cases ha : a ∈ t
  · by_cases hb : b ∈ t
    · refine Or.inr (Or.inr (Finset.Subset.antisymm ht (fun x hx => ?_)))
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · rcases Finset.mem_singleton.mp hx with rfl
        exact hb
    · refine Or.inl (Finset.Subset.antisymm (fun x hx => ?_) (Finset.singleton_subset_iff.mpr ha))
      rcases hmem x hx with rfl | rfl
      · exact Finset.mem_singleton_self _
      · exact absurd hx hb
  · by_cases hb : b ∈ t
    · refine Or.inr (Or.inl (Finset.Subset.antisymm (fun x hx => ?_)
        (Finset.singleton_subset_iff.mpr hb)))
      rcases hmem x hx with rfl | rfl
      · exact absurd hx ha
      · exact Finset.mem_singleton_self _
    · obtain ⟨y, hy⟩ := hne
      rcases hmem y hy with rfl | rfl
      · exact absurd hy ha
      · exact absurd hy hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eq_of_subset_pair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eq_of_subset_pair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eq_of_subset_pair ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eq_of_subset_pair

open _root_.Classical in
theorem exists_eq_arcChainFace_of_subset {n : ℕ} {v : ℕ → E} {j : ℕ} (hj : j ≤ 2 * n)
    {t : Finset E} (ht : t ⊆ arcChainFace v j) (hne : t.Nonempty) :
    ∃ k ≤ 2 * n, t = arcChainFace v k := by
  have ht' : t ⊆ ({v (j / 2), v ((j + 1) / 2)} : Finset E) := ht
  rcases eq_of_subset_pair ht' hne with h | h | h
  · exact ⟨2 * (j / 2), by omega, by rw [h, arcChainFace_two_mul]⟩
  · exact ⟨2 * ((j + 1) / 2), by omega, by rw [h, arcChainFace_two_mul]⟩
  · exact ⟨j, hj, h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_eq_arcChainFace_of_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_eq_arcChainFace_of_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_eq_arcChainFace_of_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_eq_arcChainFace_of_subset

open _root_.Classical in
theorem arcChainFace_subset_iff {n : ℕ} {v : ℕ → E}
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j) {i j : ℕ} (hi : i ≤ 2 * n) (hj : j ≤ 2 * n) :
    arcChainFace v i ⊆ arcChainFace v j ↔
      ((i / 2 = j / 2 ∨ i / 2 = (j + 1) / 2) ∧
        ((i + 1) / 2 = j / 2 ∨ (i + 1) / 2 = (j + 1) / 2)) := by
  constructor
  · intro h
    have h₁ := mem_arcChainFace_iff.mp (h (mem_arcChainFace_iff.mpr (Or.inl rfl)))
    have h₂ := mem_arcChainFace_iff.mp (h (mem_arcChainFace_iff.mpr (Or.inr rfl)))
    exact ⟨h₁.imp (fun hx => hinj _ (by omega) _ (by omega) hx)
        (fun hx => hinj _ (by omega) _ (by omega) hx),
      h₂.imp (fun hx => hinj _ (by omega) _ (by omega) hx)
        (fun hx => hinj _ (by omega) _ (by omega) hx)⟩
  · rintro ⟨h₁, h₂⟩ x hx
    rcases mem_arcChainFace_iff.mp hx with rfl | rfl
    · exact mem_arcChainFace_iff.mpr (h₁.imp (fun h => by rw [h]) (fun h => by rw [h]))
    · exact mem_arcChainFace_iff.mpr (h₂.imp (fun h => by rw [h]) (fun h => by rw [h]))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace_subset_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace_subset_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace_subset_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace_subset_iff

end Faces

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifoldWithBoundary.isPLBall_iUnion_derivedNeighborhoodCell_of_chain
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {m : ℕ} (F : Fin (m + 1) → Finset E)
    (hF : ∀ j, F j ∈ K.faces)
    (hne : ∀ j : Fin m, F j.castSucc ≠ F j.succ)
    (hcmp : ∀ j : Fin m, F j.castSucc ⊆ F j.succ ∨ F j.succ ⊆ F j.castSucc)
    (hfar : ∀ i j : Fin (m + 1), i.val + 1 < j.val → ¬F i ⊆ F j ∧ ¬F j ⊆ F i) :
    IsPLBall 3 (⋃ j, (derivedNeighborhoodCell K (F j)).space) :=
  hK.isPLBall_iUnion_of_chain (fun j => (derivedNeighborhoodCell K (F j)).space)
    (fun j => hK.isPLBall_derivedNeighborhoodCell (n := 2) (hF j))
    (fun j => derivedNeighborhoodCell_space_subset K (F j))
    (fun j => hK.isPLBall_derivedNeighborhoodCell_inter (n := 1) (hF _) (hF _) (hne j) (hcmp j))
    (fun i j hij => disjoint_derivedNeighborhoodCell_space K (hF i) (hF j)
      (hfar i j hij).1 (hfar i j hij).2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_iUnion_derivedNeighborhoodCell_of_chain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_iUnion_derivedNeighborhoodCell_of_chain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_iUnion_derivedNeighborhoodCell_of_chain ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_iUnion_derivedNeighborhoodCell_of_chain

omit [FiniteDimensional ℝ E] in
open _root_.Classical in
theorem arcChainFace_mem_faces {K : Geometry.SimplicialComplex ℝ E} {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    {j : ℕ} (hj : j ≤ 2 * n) : arcChainFace v j ∈ K.faces := by
  obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
  · subst hk
    rw [arcChainFace_two_mul]
    exact hvert k (by omega)
  · subst hk
    rw [arcChainFace_two_mul_add_one]
    exact hedge k (by omega)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace_mem_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace_mem_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace_mem_faces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.arcChainFace_mem_faces

open _root_.Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_iUnion_arcChainFace
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j) :
    IsPLBall 3 (⋃ j : Fin (2 * n + 1),
      (derivedNeighborhoodCell K (arcChainFace v j.val)).space) := by
  refine hK.isPLBall_iUnion_derivedNeighborhoodCell_of_chain
    (fun j : Fin (2 * n + 1) => arcChainFace v j.val)
    (fun j => arcChainFace_mem_faces hvert hedge (by omega))
    (fun j => ?_) (fun j => ?_) (fun i j hij => ?_)
  · have hlt := j.isLt
    have hc : j.castSucc.val = j.val := Fin.val_castSucc j
    have hs : j.succ.val = j.val + 1 := Fin.val_succ j
    intro heq
    have hsub₁ : arcChainFace v j.castSucc.val ⊆ arcChainFace v j.succ.val := heq ▸ subset_rfl
    have hsub₂ : arcChainFace v j.succ.val ⊆ arcChainFace v j.castSucc.val := heq ▸ subset_rfl
    rw [arcChainFace_subset_iff hinj (by omega) (by omega), hc, hs] at hsub₁
    rw [arcChainFace_subset_iff hinj (by omega) (by omega), hc, hs] at hsub₂
    omega
  · have hlt := j.isLt
    have hc : j.castSucc.val = j.val := Fin.val_castSucc j
    have hs : j.succ.val = j.val + 1 := Fin.val_succ j
    rw [arcChainFace_subset_iff hinj (by omega) (by omega),
      arcChainFace_subset_iff hinj (by omega) (by omega), hc, hs]
    omega
  · have hi := i.isLt
    have hjlt := j.isLt
    rw [arcChainFace_subset_iff hinj (by omega) (by omega),
      arcChainFace_subset_iff hinj (by omega) (by omega)]
    omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_iUnion_arcChainFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_iUnion_arcChainFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_iUnion_arcChainFace ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_iUnion_arcChainFace

open _root_.Classical in
noncomputable def arcComplexIn (K : Geometry.SimplicialComplex ℝ E) (v : ℕ → E) (n : ℕ) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s ∈ K.faces | ∃ j ≤ 2 * n, s = arcChainFace v j}
  indep hs := K.indep hs.1
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1
  isRelLowerSet_faces := by
    rintro t ⟨ht, j, hj, rfl⟩
    exact ⟨K.nonempty_of_mem_faces ht, fun t' ht't ht' =>
      ⟨K.down_closed ht ht't ht', exists_eq_arcChainFace_of_subset hj ht't ht'⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.arcComplexIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.arcComplexIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.arcComplexIn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.arcComplexIn

omit [FiniteDimensional ℝ E] in
open _root_.Classical in
theorem arcComplexIn_faces_subset (K : Geometry.SimplicialComplex ℝ E) (v : ℕ → E) (n : ℕ) :
    (arcComplexIn K v n).faces ⊆ K.faces :=
  fun _ hs => hs.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.arcComplexIn_faces_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.arcComplexIn_faces_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.arcComplexIn_faces_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.arcComplexIn_faces_subset

open _root_.Classical in
instance _root_.Submission.DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesArcComplexIn (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (v : ℕ → E) (n : ℕ) :
    Finite (arcComplexIn K v n).faces :=
  ((Set.toFinite K.faces).subset fun _ hs => hs.1).to_subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesArcComplexIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesArcComplexIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesArcComplexIn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesArcComplexIn

omit [FiniteDimensional ℝ E] in
open _root_.Classical in
theorem iUnion_derivedNeighborhoodCell_arcChainFace_eq
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces) :
    (⋃ j : Fin (2 * n + 1), (derivedNeighborhoodCell K (arcChainFace v j.val)).space) =
      (PiecewiseLinear.derivedNeighborhood K (arcComplexIn K v n)).space := by
  rw [← iUnion_derivedNeighborhoodCell_space K (arcComplexIn K v n)
    (arcComplexIn_faces_subset K v n)]
  apply Subset.antisymm
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    have hlt := j.isLt
    exact mem_iUnion₂.mpr ⟨arcChainFace v j.val,
      ⟨arcChainFace_mem_faces hvert hedge (by omega), j.val, by omega, rfl⟩, hj⟩
  · intro x hx
    obtain ⟨s, ⟨-, j, hj, rfl⟩, hxs⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨⟨j, by omega⟩, hxs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.iUnion_derivedNeighborhoodCell_arcChainFace_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.iUnion_derivedNeighborhoodCell_arcChainFace_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.iUnion_derivedNeighborhoodCell_arcChainFace_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.iUnion_derivedNeighborhoodCell_arcChainFace_eq

open _root_.Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhood_arcComplexIn
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j) :
    IsPLBall 3 (PiecewiseLinear.derivedNeighborhood K (arcComplexIn K v n)).space := by
  rw [← iUnion_derivedNeighborhoodCell_arcChainFace_eq hvert hedge]
  exact hK.isPLBall_iUnion_arcChainFace hvert hedge hinj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhood_arcComplexIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhood_arcComplexIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhood_arcComplexIn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhood_arcComplexIn

open _root_.Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLBall_containing_arcComplexIn
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j) :
    ∃ C : Set E, IsPLBall 3 C ∧ C ⊆ K.space ∧ (arcComplexIn K v n).space ⊆ C := by
  refine ⟨(PiecewiseLinear.derivedNeighborhood K (arcComplexIn K v n)).space,
    hK.isPLBall_derivedNeighborhood_arcComplexIn hvert hedge hinj,
    derivedNeighborhood_space_subset K (arcComplexIn K v n), ?_⟩
  rw [← iUnion_derivedNeighborhoodCell_space K (arcComplexIn K v n)
    (arcComplexIn_faces_subset K v n)]
  exact space_subset_iUnion_derivedNeighborhoodCell_space K (arcComplexIn K v n)
    (arcComplexIn_faces_subset K v n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isPLBall_containing_arcComplexIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isPLBall_containing_arcComplexIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isPLBall_containing_arcComplexIn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_isPLBall_containing_arcComplexIn

end DifferentialGeometry.Topology.PiecewiseLinear
