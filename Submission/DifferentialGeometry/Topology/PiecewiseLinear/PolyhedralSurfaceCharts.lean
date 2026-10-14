/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLSphereLocallyPlanar
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PieceParametrization
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private noncomputable def subtypePreimageHomeomorph {X : Type*} [TopologicalSpace X]
    (S W : Set X) : ((Subtype.val : S → X) ⁻¹' W) ≃ₜ ↥(W ∩ S) :=
  (IsEmbedding.subtypeVal.homeomorphImage ((Subtype.val : S → X) ⁻¹' W)).trans
    (Homeomorph.setCongr (by rw [Subtype.image_preimage_coe, _root_.Set.inter_comm]))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subtypePreimageHomeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.subtypePreimageHomeomorph target :: scope.openDecls } }

private theorem local_chart_of_homeomorph {X Y H : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace H] {S : Set X} {T : Set Y} (e : S ≃ₜ T)
    {y : Y} (hy : y ∈ T)
    (hlocal : ∃ W : Set X, IsOpen W ∧ (e.symm ⟨y, hy⟩ : X) ∈ W ∧
      ∃ V : Set H, IsOpen V ∧ Nonempty (↥(W ∩ S) ≃ₜ V)) :
    ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧ ∃ V : Set H,
      IsOpen V ∧ Nonempty (↥(W ∩ T) ≃ₜ V) := by
  obtain ⟨W, hW, hyW, V, hV, ⟨ψ⟩⟩ := hlocal
  let D := (Subtype.val : S → X) ⁻¹' W
  have hD : IsOpen D := hW.preimage continuous_subtype_val
  obtain ⟨O, hO, hOE⟩ := isOpen_induced_iff.mp (e.isOpenMap D hD)
  have hpoint : (⟨y, hy⟩ : T) ∈ e '' D :=
    ⟨e.symm ⟨y, hy⟩, hyW, e.apply_symm_apply _⟩
  refine ⟨O, hO, ?_, V, hV, ?_⟩
  · rw [← hOE] at hpoint
    exact hpoint
  · let a : ((Subtype.val : T → Y) ⁻¹' O) ≃ₜ e '' D := Homeomorph.setCongr hOE
    exact ⟨(subtypePreimageHomeomorph T O).symm.trans
      (a.trans ((e.image D).symm.trans ((subtypePreimageHomeomorph S W).trans ψ)))⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.local_chart_of_homeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.local_chart_of_homeomorph target :: scope.openDecls } }

private theorem local_chart_inter_open {X H : Type*} [TopologicalSpace X]
    [TopologicalSpace H] {S O : Set X} {x : X} (hO : IsOpen O) (hxO : x ∈ O)
    (hlocal : ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∃ V : Set H,
      IsOpen V ∧ Nonempty (↥(W ∩ S) ≃ₜ V)) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∃ V : Set H,
      IsOpen V ∧ Nonempty (↥(W ∩ (S ∩ O)) ≃ₜ V) := by
  obtain ⟨W, hW, hxW, V, hV, ⟨ψ⟩⟩ := hlocal
  let D := (Subtype.val : ↥(W ∩ S) → X) ⁻¹' O
  let V' := (Subtype.val : V → H) '' (ψ '' D)
  have hV' : IsOpen V' := hV.isOpenEmbedding_subtypeVal.isOpenMap _
    (ψ.isOpenMap D (hO.preimage continuous_subtype_val))
  have hdom : O ∩ (W ∩ S) = (W ∩ O) ∩ (S ∩ O) := by
    ext z
    simp only [_root_.Set.mem_inter_iff]
    tauto
  let a : D ≃ₜ ↥((W ∩ O) ∩ (S ∩ O)) :=
    (subtypePreimageHomeomorph (W ∩ S) O).trans (Homeomorph.setCongr hdom)
  let b : (ψ '' D) ≃ₜ V' := IsEmbedding.subtypeVal.homeomorphImage (ψ '' D)
  exact ⟨W ∩ O, hW.inter hO, ⟨hxW, hxO⟩, V', hV',
    ⟨a.symm.trans ((ψ.image D).trans b)⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.local_chart_inter_open
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.local_chart_inter_open target :: scope.openDecls } }

theorem IsPolyhedralSphere.exists_isOpen_inter_homeomorph_of_two {M : Type*}
    [TopologicalSpace M] [T2Space M] {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {P : Set M}
    (hP : IsPolyhedralSphere (n := n) 2 P) {y : M} (hy : y ∈ P) :
    ∃ W : Set M, IsOpen W ∧ y ∈ W ∧ ∃ V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen V ∧ Nonempty (↥(W ∩ P) ≃ₜ V) := by
  obtain ⟨T, hT⟩ := hP
  exact local_chart_of_homeomorph T.piece.homeomorph hy
    (hT.exists_isOpen_inter_homeomorph_of_two (T.piece.homeomorph.symm ⟨y, hy⟩).property)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralSphere.exists_isOpen_inter_homeomorph_of_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralSphere.exists_isOpen_inter_homeomorph_of_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralSphere.exists_isOpen_inter_homeomorph_of_two ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralSphere.exists_isOpen_inter_homeomorph_of_two

theorem IsPolyhedralSphere.exists_isOpen_inter_chart_image_homeomorph_of_two {M : Type*}
    [TopologicalSpace M] [T2Space M] {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {P : Set M}
    (hP : IsPolyhedralSphere (n := n) 2 P)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) {y : M}
    (hy : y ∈ P ∩ c.source) :
    ∃ W : Set (EuclideanSpace ℝ (Fin n)), IsOpen W ∧ c y ∈ W ∧
      ∃ V : Set (EuclideanSpace ℝ (Fin 2)), IsOpen V ∧
        Nonempty (↥(W ∩ c '' (P ∩ c.source)) ≃ₜ V) := by
  let e := c.homeomorphOfImageSubsetSource (s := P ∩ c.source) _root_.Set.inter_subset_right rfl
  have hcy : c y ∈ c '' (P ∩ c.source) := _root_.Set.mem_image_of_mem c hy
  have hback : (e.symm ⟨c y, hcy⟩ : M) = y := c.left_inv hy.2
  apply local_chart_of_homeomorph e hcy
  rw [hback]
  exact local_chart_inter_open c.open_source hy.2
    (hP.exists_isOpen_inter_homeomorph_of_two hy.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralSphere.exists_isOpen_inter_chart_image_homeomorph_of_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralSphere.exists_isOpen_inter_chart_image_homeomorph_of_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralSphere.exists_isOpen_inter_chart_image_homeomorph_of_two ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralSphere.exists_isOpen_inter_chart_image_homeomorph_of_two

theorem IsPLCellOn.exists_isOpen_inter_boundary_homeomorph {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B : Set M} (h : IsPLCellOn 3 S B) {y : M} (hy : y ∈ B) :
    ∃ W : Set M, IsOpen W ∧ y ∈ W ∧ ∃ V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen V ∧ Nonempty (↥(W ∩ B) ≃ₜ V) := by
  obtain ⟨P, r, u, hr, hu, -, hB⟩ := h
  have hb : IsPLBall 3 P := ⟨r, hr⟩
  have hSP : frontier P ⊆ P := hb.isPolyhedron.isClosed.frontier_subset
  rw [IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hr] at hB
  let : CompactSpace (frontier P) :=
    isCompact_iff_compactSpace.mp hb.isPLSphere_frontier.isPolyhedron.isCompact
  have hemb : _root_.Topology.IsClosedEmbedding (fun x : frontier P => u x) :=
    (hu.continuousOn.mono hSP).domRestrict.isClosedEmbedding
      (fun x z hxz => Subtype.ext (hu.injOn (hSP x.property) (hSP z.property) hxz))
  have hrange : _root_.Set.range (fun x : frontier P => u x) = B := by
    rw [hB]
    change _root_.Set.range (u ∘ (Subtype.val : frontier P → EuclideanSpace ℝ (Fin 3))) = _
    rw [_root_.Set.range_comp, Subtype.range_coe]
  let e := hemb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  exact local_chart_of_homeomorph e hy
    (hb.isPLSphere_frontier.exists_isOpen_inter_homeomorph_of_two (e.symm ⟨y, hy⟩).property)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_isOpen_inter_boundary_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_isOpen_inter_boundary_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_isOpen_inter_boundary_homeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_isOpen_inter_boundary_homeomorph

theorem IsPLCellOn.exists_isOpen_inter_boundary_chart_image_homeomorph {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B : Set M} (h : IsPLCellOn 3 S B)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))) {y : M}
    (hy : y ∈ B ∩ c.source) :
    ∃ W : Set (EuclideanSpace ℝ (Fin 3)), IsOpen W ∧ c y ∈ W ∧
      ∃ V : Set (EuclideanSpace ℝ (Fin 2)), IsOpen V ∧
        Nonempty (↥(W ∩ c '' (B ∩ c.source)) ≃ₜ V) := by
  let e := c.homeomorphOfImageSubsetSource (s := B ∩ c.source) _root_.Set.inter_subset_right rfl
  have hcy : c y ∈ c '' (B ∩ c.source) := _root_.Set.mem_image_of_mem c hy
  have hback : (e.symm ⟨c y, hcy⟩ : M) = y := c.left_inv hy.2
  apply local_chart_of_homeomorph e hcy
  rw [hback]
  exact local_chart_inter_open c.open_source hy.2
    (h.exists_isOpen_inter_boundary_homeomorph hy.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_isOpen_inter_boundary_chart_image_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_isOpen_inter_boundary_chart_image_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_isOpen_inter_boundary_chart_image_homeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.exists_isOpen_inter_boundary_chart_image_homeomorph

end DifferentialGeometry.Topology.PiecewiseLinear
