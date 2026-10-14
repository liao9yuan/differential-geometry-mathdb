/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallSphereLink
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Polyhedron

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Classical in
def IsCombinatorialManifoldWithBoundary : ℕ → Geometry.SimplicialComplex ℝ E → Prop
  | 0, K => ∀ v, {v} ∈ K.faces → (SimplicialComplex.geometricLink K {v}).faces = ∅
  | n + 1, K => ∀ v, {v} ∈ K.faces → IsPLSphere n (SimplicialComplex.geometricLink K {v}).space ∨
      IsPLBall n (SimplicialComplex.geometricLink K {v}).space

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary

theorem IsCombinatorialManifold.isCombinatorialManifoldWithBoundary {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} (h : IsCombinatorialManifold n K) :
    IsCombinatorialManifoldWithBoundary n K := by
  cases n with
  | zero => exact h
  | succ n => exact fun v hv => Or.inl (h v hv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.isCombinatorialManifoldWithBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.isCombinatorialManifoldWithBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.isCombinatorialManifoldWithBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.isCombinatorialManifoldWithBoundary

open _root_.Classical in
theorem IsGlueIso.isCombinatorialManifoldWithBoundary {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} {L : Geometry.SimplicialComplex ℝ F} [Finite K.faces]
    [Finite L.faces] {φ : E → F} {φ' : F → E} (h : IsGlueIso K L φ φ')
    (hK : IsCombinatorialManifoldWithBoundary n K) : IsCombinatorialManifoldWithBoundary n L := by
  cases n with
  | zero =>
    intro w hw
    have hv : {φ' w} ∈ K.faces := h.symm.singleton_mem hw
    have hφ : φ (φ' w) = w := h.right _ hw w (Finset.mem_singleton_self w)
    have hiso := h.geometricLink hv
    rw [hφ] at hiso
    rw [Set.eq_empty_iff_forall_notMem]
    intro t ht
    have := hiso.image₂ t ht
    rw [hK _ hv] at this
    exact this
  | succ n =>
    intro w hw
    have hv : {φ' w} ∈ K.faces := h.symm.singleton_mem hw
    have hφ : φ (φ' w) = w := h.right _ hw w (Finset.mem_singleton_self w)
    have hiso := h.geometricLink hv
    rw [hφ] at hiso
    have hpl := hiso.isPLHomeomorphOn
    rcases hK _ hv with hs | hb
    · exact Or.inl (hs.of_isPLHomeomorphOn hpl)
    · exact Or.inr (hb.of_isPLHomeomorphOn hpl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.isCombinatorialManifoldWithBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.isCombinatorialManifoldWithBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.isCombinatorialManifoldWithBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.isCombinatorialManifoldWithBoundary

open _root_.Classical in
theorem IsGlueIso.isCombinatorialManifold {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} {L : Geometry.SimplicialComplex ℝ F} [Finite K.faces]
    [Finite L.faces] {φ : E → F} {φ' : F → E} (h : IsGlueIso K L φ φ')
    (hK : IsCombinatorialManifold n K) : IsCombinatorialManifold n L := by
  cases n with
  | zero =>
    intro w hw
    have hv : {φ' w} ∈ K.faces := h.symm.singleton_mem hw
    have hφ : φ (φ' w) = w := h.right _ hw w (Finset.mem_singleton_self w)
    have hiso := h.geometricLink hv
    rw [hφ] at hiso
    rw [Set.eq_empty_iff_forall_notMem]
    intro t ht
    have := hiso.image₂ t ht
    rw [hK _ hv] at this
    exact this
  | succ n =>
    intro w hw
    have hv : {φ' w} ∈ K.faces := h.symm.singleton_mem hw
    have hφ : φ (φ' w) = w := h.right _ hw w (Finset.mem_singleton_self w)
    have hiso := h.geometricLink hv
    rw [hφ] at hiso
    exact (hK _ hv).of_isPLHomeomorphOn hiso.isPLHomeomorphOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.isCombinatorialManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.isCombinatorialManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.isCombinatorialManifold ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.isCombinatorialManifold

section Boundary

variable [DecidableEq E] (n : ℕ) (K : Geometry.SimplicialComplex ℝ E)

def boundaryFaces : Set (Finset E) :=
  {s | s ∈ K.faces ∧ ∃ t ∈ K.faces, s ⊆ t ∧ t.card ≤ n ∧
    IsPLBall (n - t.card) (SimplicialComplex.geometricLink K t).space}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryFaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryFaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryFaces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryFaces

def boundaryComplex : Geometry.SimplicialComplex ℝ E where
  faces := boundaryFaces n K
  isRelLowerSet_faces := by
    rintro s ⟨hs, t, ht, hst, htn, hball⟩
    exact ⟨K.nonempty_of_mem_faces hs, fun u hus hu =>
      ⟨K.down_closed hs hus hu, t, ht, hus.trans hst, htn, hball⟩⟩
  indep hs := K.indep hs.1
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex

theorem mem_boundaryComplex_faces_iff {s : Finset E} :
    s ∈ (boundaryComplex n K).faces ↔ s ∈ K.faces ∧ ∃ t ∈ K.faces, s ⊆ t ∧ t.card ≤ n ∧
      IsPLBall (n - t.card) (SimplicialComplex.geometricLink K t).space := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_boundaryComplex_faces_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_boundaryComplex_faces_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_boundaryComplex_faces_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_boundaryComplex_faces_iff

theorem boundaryComplex_faces_subset : (boundaryComplex n K).faces ⊆ K.faces := fun _ hs => hs.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_faces_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_faces_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_faces_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_faces_subset

theorem boundaryComplex_faces_finite [Finite K.faces] : (boundaryComplex n K).faces.Finite :=
  (Set.toFinite K.faces).subset (boundaryComplex_faces_subset n K)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_faces_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_faces_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_faces_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_faces_finite

theorem boundaryComplex_space_subset : (boundaryComplex n K).space ⊆ K.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := (boundaryComplex n K).mem_space_iff.mp hx
  exact K.convexHull_subset_space hs.1 hxs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_subset

theorem mem_boundaryComplex_faces_of_isPLBall {t : Finset E} (ht : t ∈ K.faces) (htn : t.card ≤ n)
    (hball : IsPLBall (n - t.card) (SimplicialComplex.geometricLink K t).space) :
    t ∈ (boundaryComplex n K).faces := ⟨ht, t, ht, subset_rfl, htn, hball⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_boundaryComplex_faces_of_isPLBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_boundaryComplex_faces_of_isPLBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_boundaryComplex_faces_of_isPLBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_boundaryComplex_faces_of_isPLBall

theorem geometricLink_boundaryComplex (v : E) :
    SimplicialComplex.geometricLink (boundaryComplex (n + 1) K) {v} =
      boundaryComplex n (SimplicialComplex.geometricLink K {v}) := by
  ext t
  simp only [SimplicialComplex.mem_geometricLink_singleton, mem_boundaryComplex_faces_iff]
  constructor
  · rintro ⟨htne, hvt, hins, u, hu, hsub, hun, hball⟩
    have hvu : v ∈ u := hsub (Finset.mem_insert_self v t)
    have hne : (u.erase v).Nonempty := by
      obtain ⟨w, hw⟩ := htne
      exact ⟨w, Finset.mem_erase.mpr ⟨fun h => hvt (h ▸ hw), hsub (Finset.mem_insert_of_mem hw)⟩⟩
    refine ⟨⟨htne, hvt, hins⟩, u.erase v,
      ⟨hne, Finset.notMem_erase v u, by rwa [Finset.insert_erase hvu]⟩, ?_, ?_, ?_⟩
    · intro w hw
      exact Finset.mem_erase.mpr ⟨fun h => hvt (h ▸ hw), hsub (Finset.mem_insert_of_mem hw)⟩
    · have := Finset.card_erase_of_mem hvu
      omega
    · have hcard : n - (u.erase v).card = n + 1 - u.card := by
        have := Finset.card_erase_of_mem hvu
        have := Finset.card_pos.mpr ⟨v, hvu⟩
        omega
      rw [hcard, ← geometricLink_insert K (Finset.notMem_erase v u), Finset.insert_erase hvu]
      exact hball
  · rintro ⟨⟨htne, hvt, hins⟩, u, ⟨hune, hvu, hinsu⟩, hsub, hun, hball⟩
    refine ⟨htne, hvt, hins, _root_.Insert.insert v u, hinsu, Finset.insert_subset_insert v hsub, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hvu]
      omega
    · have hcard : n + 1 - (_root_.Insert.insert v u).card = n - u.card := by
        rw [Finset.card_insert_of_notMem hvu]
        omega
      rw [hcard, geometricLink_insert K hvu]
      exact hball

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_boundaryComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_boundaryComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_boundaryComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_boundaryComplex

end Boundary

end DifferentialGeometry.Topology.PiecewiseLinear
