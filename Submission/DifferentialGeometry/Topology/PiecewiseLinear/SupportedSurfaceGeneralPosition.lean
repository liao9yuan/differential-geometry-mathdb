/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ChartRelativeGeneralPosition
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingSurfacePatches
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingIntersectionConfinement
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PieceMap
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPolyhedralManifoldWithBoundary.exists_chart_complex
    {n m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {S : Set X}
    (hS : IsPolyhedralManifoldWithBoundary (n := n) m S)
    (c : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ (plGroupoid n).maximalAtlas X)
    (hSc : S ⊆ c.source) :
    ∃ K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)),
      K.faces.Finite ∧ K.space = c '' S ∧
      IsCombinatorialManifoldWithBoundary m K := by
  classical
  obtain ⟨T, hT⟩ := hS
  have : Finite T.piece.complex.faces := T.piece.finite_faces.to_subtype
  have hid : IsPiecewiseAffineOn (id : EuclideanSpace ℝ (Fin T.ambientDim) → _)
      T.piece.complex.space :=
    (isPiecewiseAffineOn_id isOpen_univ).mono_of_isPolyhedron T.piece.isPolyhedron_space
      (_root_.Set.subset_univ _)
  have hmap : IsPLOn T.ambientDim n T.piece.map T.piece.complex.space := by
    simpa only [Function.comp_id] using T.piece.isPLOn_comp hid (_root_.Set.mapsTo_id _)
  obtain ⟨K, hKfin, hKspace, hKpl, -⟩ :=
    hmap.exists_isPLHomeomorphOn_chart_image T.piece.isPolyhedron_space T.piece.bijOn.injOn
      c hc (fun x hx => hSc (T.piece.bijOn.mapsTo hx))
  have : Finite K.faces := hKfin.to_subtype
  refine ⟨K, hKfin, ?_, hT.of_isPLHomeomorphOn hKpl⟩
  rw [hKspace, _root_.Set.image_comp, T.piece.bijOn.image_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.exists_chart_complex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.exists_chart_complex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.exists_chart_complex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralManifoldWithBoundary.exists_chart_complex

theorem eventually_mem_chart_image_iff_of_eventually
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A B : Set X} {x : X}
    (c : OpenPartialHomeomorph X Y) (hx : x ∈ c.source)
    (hAB : ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ B) :
    ∀ᶠ z in 𝓝 (c x), z ∈ c '' (A ∩ c.source) ↔ z ∈ c '' (B ∩ c.source) := by
  have hback : Filter.Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
    have hcont := (c.continuousAt_symm (c.map_source hx)).tendsto
    rwa [c.left_inv hx] at hcont
  filter_upwards [hback.eventually hAB, c.open_target.mem_nhds (c.map_source hx)] with z hz hzT
  have hmem (S : Set X) : z ∈ c '' (S ∩ c.source) ↔ c.symm z ∈ S := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [c.left_inv hy.2]
      exact hy.1
    · intro hy
      exact ⟨c.symm z, ⟨hy, c.map_target hzT⟩, c.right_inv hzT⟩
  exact (hmem A).trans (hz.trans (hmem B).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eventually_mem_chart_image_iff_of_eventually then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eventually_mem_chart_image_iff_of_eventually"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eventually_mem_chart_image_iff_of_eventually ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eventually_mem_chart_image_iff_of_eventually

theorem exists_small_isPL_homeomorph_surface_crossing_in_chart
    {X : Type*} [MetricSpace X] [ChartedSpace E3 X]
    {A B Ω : Set X} (hA : IsPolyhedralManifoldWithBoundary (n := 3) 2 A)
    (hB : IsPolyhedralManifoldWithBoundary (n := 3) 2 B)
    (c : OpenPartialHomeomorph X E3) (hc : c ∈ (plGroupoid 3).maximalAtlas X)
    (hΩ : IsOpen Ω) (htrace : A ∩ B ⊆ Ω ∩ c.source) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : X ≃ₜ X, IsPL 3 3 φ ∧ IsPL 3 3 φ.symm ∧
      (∀ x, _root_.Dist.dist (φ x) x < ε) ∧ _root_.Set.EqOn φ id Ωᶜ ∧ _root_.Set.MapsTo φ c.source c.source ∧
      φ '' A ∩ B ⊆ Ω ∩ c.source ∧
      ∀ y ∈ φ '' A ∩ B,
        HasPLCrossingAt (c '' ((φ '' A) ∩ c.source)) (c '' (B ∩ c.source)) (c y) := by
  classical
  have hcompact : IsCompact (A ∩ B) := hA.isCompact.inter_right hB.isCompact.isClosed
  obtain ⟨Wa, hWa, hWaSub, -, hWaN⟩ :=
    hA.exists_patch hcompact _root_.Set.inter_subset_left (hΩ.inter c.open_source) htrace
  obtain ⟨Wb, hWb, hWbSub, -, hWbN⟩ :=
    hB.exists_patch hcompact _root_.Set.inter_subset_right (hΩ.inter c.open_source) htrace
  obtain ⟨Va, Vb, δ, hVa, hVb, -, hVaWa, hVbWb, hδ, hconfine⟩ :=
    exists_intersection_confinement_of_compact hA.isCompact hB.isCompact hWaN hWbN
  have hWaC : Wa ⊆ c.source := fun x hx => (hWaSub hx).2.2
  have hWbC : Wb ⊆ c.source := fun x hx => (hWbSub hx).2.2
  obtain ⟨K, hKfin, hKspace, hK⟩ := hWa.exists_chart_complex c hc hWaC
  obtain ⟨L, hLfin, hLspace, hL⟩ := hWb.exists_chart_complex c hc hWbC
  have : Finite K.faces := hKfin.to_subtype
  have : Finite L.faces := hLfin.to_subtype
  have hKU : K.space ⊆ c '' (c.source ∩ Ω) := by
    rw [hKspace]
    exact _root_.Set.image_mono fun x hx => ⟨hWaC hx, (hWaSub hx).2.1⟩
  obtain ⟨φ, hφ, hφsymm, hclose, hfix, -, hmap, -, -, hcross⟩ :=
    exists_small_isPL_homeomorph_generalPosition_off_polyhedron_in_chart c hc K L hK hL
      IsPolyhedron.empty hΩ hKU (_root_.Set.empty_subset _) (lt_min hε hδ)
  have hconf : φ '' A ∩ B ⊆ φ '' (Va ∩ A) ∩ Vb :=
    hconfine φ fun x _ => (hclose x).trans_le (min_le_right _ _)
  have hnew : φ '' A ∩ B ⊆ Ω ∩ c.source := by
    intro y hy
    exact (hWbSub (hVbWb ⟨(hconf hy).2, hy.2⟩)).2
  have hWaImage : φ '' Wa ⊆ c.source := image_subset_iff.mpr fun x hx => hmap (hWaC hx)
  have hcoord : (c ∘ φ ∘ c.symm) '' K.space = c '' (φ '' Wa) := by
    rw [hKspace, _root_.Set.image_image, _root_.Set.image_image]
    apply _root_.Set.image_congr
    intro x hx
    simp only [Function.comp_apply, c.left_inv (hWaC hx)]
  have hpatchCross : ∀ y ∈ φ '' A ∩ B,
      HasPLCrossingAt (c '' ((φ '' Wa) ∩ c.source)) (c '' (Wb ∩ c.source)) (c y) := by
    intro y hy
    have hyWa : y ∈ φ '' Wa := (_root_.Set.image_mono hVaWa) (hconf hy).1
    have hyWb : y ∈ Wb := hVbWb ⟨(hconf hy).2, hy.2⟩
    have hcross' := hcross (c y)
    rw [hcoord, hLspace] at hcross'
    simpa only [inter_eq_left.mpr hWaImage, inter_eq_left.mpr hWbC] using
      hcross' ⟨mem_image_of_mem c hyWa, _root_.Set.mem_image_of_mem c hyWb⟩ (_root_.Set.notMem_empty _)
  refine ⟨φ, hφ, hφsymm, fun x => (hclose x).trans_le (min_le_left _ _), hfix, hmap,
    hnew, ?_⟩
  intro y hy
  have hyVa : y ∈ φ '' Va := _root_.Set.image_mono _root_.Set.inter_subset_left (hconf hy).1
  have ha : ∀ᶠ z in 𝓝 y, z ∈ φ '' Wa ↔ z ∈ φ '' A := by
    filter_upwards [(φ.isOpenMap Va hVa).mem_nhds hyVa] with z hz
    constructor
    · intro hzWa
      exact (_root_.Set.image_mono (fun x hx => (hWaSub hx).1)) hzWa
    · rintro ⟨x, hxA, rfl⟩
      obtain ⟨w, hw, heq⟩ := hz
      have hxVa : x ∈ Va := φ.injective heq ▸ hw
      exact _root_.Set.mem_image_of_mem φ (hVaWa ⟨hxVa, hxA⟩)
  have hb : ∀ᶠ z in 𝓝 y, z ∈ Wb ↔ z ∈ B := by
    filter_upwards [hVb.mem_nhds (hconf hy).2] with z hz
    exact ⟨fun hzW => (hWbSub hzW).1, fun hzB => hVbWb ⟨hz, hzB⟩⟩
  exact (hpatchCross y hy).congr
    (eventually_mem_chart_image_iff_of_eventually c (hnew hy).2 ha)
    (eventually_mem_chart_image_iff_of_eventually c (hnew hy).2 hb)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_small_isPL_homeomorph_surface_crossing_in_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_small_isPL_homeomorph_surface_crossing_in_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_small_isPL_homeomorph_surface_crossing_in_chart ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_small_isPL_homeomorph_surface_crossing_in_chart

end DifferentialGeometry.Topology.PiecewiseLinear
