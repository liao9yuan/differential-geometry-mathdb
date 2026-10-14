/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPiece

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsPiecewiseAffineWithinAt.inter_of_isPolyhedron {f : E → F} {s : Set E} {x : E}
    (hf : IsPiecewiseAffineWithinAt f s x) {P : Set E} (hP : IsPolyhedron P) :
    IsPiecewiseAffineWithinAt f (s ∩ P) x := by
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hf
  obtain ⟨κ, hκ, D, hD, rfl⟩ := hP
  have := hι
  have := hκ
  refine ⟨ι × κ, inferInstance, fun q => C q.1 ∩ D q.2, fun q => A q.1,
    fun q => ⟨(hC q.1).1.inter (hD q.2), ?_, (hC q.1).2.2.mono inter_subset_left⟩, ?_⟩
  · exact _root_.Set.inter_subset_inter ((hC q.1).2.1) (_root_.Set.subset_iUnion D q.2)
  · have heq : (⋃ q : ι × κ, C q.1 ∩ D q.2) = (⋃ i, C i) ∩ ⋃ j, D j := by
      ext y
      simp only [_root_.Set.mem_iUnion, _root_.Set.mem_inter_iff, Prod.exists]
      exact ⟨fun ⟨i, j, hi, hj⟩ => ⟨⟨i, hi⟩, ⟨j, hj⟩⟩,
        fun ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ => ⟨i, j, hi, hj⟩⟩
    rw [heq]
    exact Filter.inter_mem (nhdsWithin_mono x _root_.Set.inter_subset_left hCx)
      (Filter.mem_of_superset self_mem_nhdsWithin _root_.Set.inter_subset_right)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.inter_of_isPolyhedron then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.inter_of_isPolyhedron"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.inter_of_isPolyhedron ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.inter_of_isPolyhedron

theorem IsPiecewiseAffineOn.inter_of_isPolyhedron {f : E → F} {s : Set E}
    (hf : IsPiecewiseAffineOn f s) {P : Set E} (hP : IsPolyhedron P) :
    IsPiecewiseAffineOn f (s ∩ P) :=
  fun x hx => (hf x hx.1).inter_of_isPolyhedron hP

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.inter_of_isPolyhedron then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.inter_of_isPolyhedron"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.inter_of_isPolyhedron ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.inter_of_isPolyhedron

theorem IsPiecewiseAffineWithinAt.inter_preimage_of_isPolyhedron [FiniteDimensional ℝ E]
    {f : E → F} {s : Set E} {x : E} (hf : IsPiecewiseAffineWithinAt f s x) {P : Set F}
    (hP : IsPolyhedron P) : IsPiecewiseAffineWithinAt f (s ∩ f ⁻¹' P) x := by
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hf
  obtain ⟨κ, hκ, D, hD, rfl⟩ := hP
  have := hι
  have := hκ
  refine ⟨ι × κ, inferInstance, fun q => C q.1 ∩ A q.1 ⁻¹' D q.2, fun q => A q.1,
    fun q => ⟨(hC q.1).1.inter_preimage (hD q.2) _, ?_,
      (hC q.1).2.2.mono inter_subset_left⟩, ?_⟩
  · rintro y ⟨hyC, hyD⟩
    refine ⟨(hC q.1).2.1 hyC, ?_⟩
    rw [_root_.Set.mem_preimage, (hC q.1).2.2 hyC]
    exact mem_iUnion.mpr ⟨q.2, hyD⟩
  · have heq : (⋃ q : ι × κ, C q.1 ∩ A q.1 ⁻¹' D q.2) =
        (⋃ i, C i) ∩ f ⁻¹' ⋃ j, D j := by
      ext y
      simp only [_root_.Set.mem_iUnion, _root_.Set.mem_inter_iff, _root_.Set.mem_preimage, Prod.exists]
      constructor
      · rintro ⟨i, j, hyC, hyD⟩
        refine ⟨⟨i, hyC⟩, j, ?_⟩
        rwa [(hC i).2.2 hyC]
      · rintro ⟨⟨i, hyC⟩, j, hyD⟩
        refine ⟨i, j, hyC, ?_⟩
        rwa [← (hC i).2.2 hyC]
    rw [heq]
    exact Filter.inter_mem (nhdsWithin_mono x _root_.Set.inter_subset_left hCx)
      (Filter.mem_of_superset self_mem_nhdsWithin _root_.Set.inter_subset_right)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.inter_preimage_of_isPolyhedron then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.inter_preimage_of_isPolyhedron"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.inter_preimage_of_isPolyhedron ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineWithinAt.inter_preimage_of_isPolyhedron

theorem IsPiecewiseAffineOn.inter_preimage_of_isPolyhedron [FiniteDimensional ℝ E]
    {f : E → F} {s : Set E} (hf : IsPiecewiseAffineOn f s) {P : Set F}
    (hP : IsPolyhedron P) : IsPiecewiseAffineOn f (s ∩ f ⁻¹' P) :=
  fun x hx => (hf x hx.1).inter_preimage_of_isPolyhedron hP

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.inter_preimage_of_isPolyhedron then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.inter_preimage_of_isPolyhedron"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.inter_preimage_of_isPolyhedron ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPiecewiseAffineOn.inter_preimage_of_isPolyhedron

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [FiniteDimensional ℝ E]

def PLPieceIn.restrict {Y : Set X} (T : PLPieceIn E n X Y)
    (L : Geometry.SimplicialComplex ℝ E) (hL : L.faces ⊆ T.complex.faces) :
    PLPieceIn E n X (T.map '' L.space) := by
  have hsub : L.space ⊆ T.complex.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := L.mem_space_iff.mp hx
    exact T.complex.convexHull_subset_space (hL hs) hxs
  have hfin : L.faces.Finite := T.finite_faces.subset hL
  have : Finite L.faces := hfin.to_subtype
  have hbij : _root_.Set.BijOn T.map L.space (T.map '' L.space) :=
    (T.bijOn.injOn.mono hsub).bijOn_image
  refine ⟨L, hfin, T.map, hbij, T.continuousOn.mono hsub, fun e he => ?_, fun e he => ?_⟩
  · have h := (T.isPiecewiseAffineOn_chart e he).inter_of_isPolyhedron
      (PiecewiseLinear.isPolyhedron_space L)
    have heq : (T.complex.space ∩ T.map ⁻¹' e.source) ∩ L.space =
        L.space ∩ T.map ⁻¹' e.source := by
      ext x
      exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hsub hx.1, hx.2⟩, hx.1⟩⟩
    rwa [heq] at h
  · have h := (T.isPiecewiseAffineOn_chart_symm e he).inter_preimage_of_isPolyhedron
      (PiecewiseLinear.isPolyhedron_space L)
    have heq : (e.target ∩ e.symm ⁻¹' Y) ∩
        (Function.invFunOn T.map T.complex.space ∘ e.symm) ⁻¹' L.space =
        e.target ∩ e.symm ⁻¹' (T.map '' L.space) := by
      ext y
      constructor
      · rintro ⟨⟨hy, hyY⟩, hyL⟩
        exact ⟨hy, Function.invFunOn T.map T.complex.space (e.symm y), hyL,
          T.bijOn.invOn_invFunOn.2 hyY⟩
      · rintro ⟨hy, z, hz, hzy⟩
        refine ⟨⟨hy, ?_⟩, ?_⟩
        · change e.symm y ∈ Y
          rw [← hzy]
          exact T.bijOn.mapsTo (hsub hz)
        · change Function.invFunOn T.map T.complex.space (e.symm y) ∈ L.space
          rw [← hzy, T.bijOn.invOn_invFunOn.1 (hsub hz)]
          exact hz
    rw [heq] at h
    refine h.congr fun y hy => ?_
    have hmem := hbij.surjOn.mapsTo_invFunOn hy.2
    have hY := (_root_.Set.image_mono hsub).trans T.bijOn.mapsTo.image_subset hy.2
    exact T.bijOn.injOn (hsub hmem) (T.bijOn.surjOn.mapsTo_invFunOn hY)
      ((hbij.invOn_invFunOn.2 hy.2).trans (T.bijOn.invOn_invFunOn.2 hY).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.restrict ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.restrict

theorem PLPieceIn.restrict_complex {Y : Set X} (T : PLPieceIn E n X Y)
    (L : Geometry.SimplicialComplex ℝ E) (hL : L.faces ⊆ T.complex.faces) :
    (T.restrict L hL).complex = L := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.restrict_complex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.restrict_complex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.restrict_complex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.restrict_complex

theorem PLPieceIn.restrict_map {Y : Set X} (T : PLPieceIn E n X Y)
    (L : Geometry.SimplicialComplex ℝ E) (hL : L.faces ⊆ T.complex.faces) :
    (T.restrict L hL).map = T.map := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.restrict_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.restrict_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.restrict_map ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.restrict_map

end DifferentialGeometry.Topology.PiecewiseLinear
