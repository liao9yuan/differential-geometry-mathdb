/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
/-
Modified from PolygonalPolyhedron.lean at e3c7230fe78d7b056a415d9ecae6f77887046b32:
use local PrePolygon/inside/outside and a private canonical Mathlib adapter;
remove the duplicate upstream polygonal Jordan dependency. See MODIFICATIONS.md.
-/
import Submission.DifferentialGeometry.External.ClassificationOfSurfaces.Moise.LineSubdivision
import Submission.DifferentialGeometry.External.Schoenflies.PrePolygonSep
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! Pre Polygon Triangulation. -/

open _root_.Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise
  (Plane PlaneComplex TriangleMesh planePoint planePoint_apply_zero planePoint_apply_one
    affineIndependent_plane_triple_of_det_ne_zero mem_convexHull_range_fin3_of_weights)

private def planeComplexToAbstract (K : PlaneComplex) :
    PreAbstractSimplicialComplex K.Vertex where
  faces := K.simplexes
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨K.nonempty_of_mem s hs, ?_⟩
    intro t hts ht
    exact K.down_closed s hs t hts ht

run_cmd do
  let target := ``Submission.planeComplexToAbstract
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `planeComplexToAbstract target :: scope.openDecls } }

private noncomputable def planeComplexToSimplicialComplex (K : PlaneComplex) :
    Geometry.SimplicialComplex ℝ Plane := by
  classical
  refine
    { (planeComplexToAbstract K).map K.position with
      indep := ?_
      inter_subset_convexHull := ?_ }
  · rintro s ⟨t, ht, rfl⟩
    apply LeanEval.Topology.ClassificationOfSurfaces.Moise.affineIndependent_finset_coe
      (K.affineIndependent t ht)
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨⟨v, hv⟩, rfl⟩
  · rintro s t ⟨S, hS, rfl⟩ ⟨T, hT, rfl⟩
    have hfaces : convexHull ℝ (K.position '' (S : Set K.Vertex)) ∩
        convexHull ℝ (K.position '' (T : Set K.Vertex)) =
          convexHull ℝ (K.position '' ((S ∩ T : Finset K.Vertex) : Set K.Vertex)) :=
      K.face_inter S hS T hT
    simpa only [Finset.coe_image, Finset.coe_inter,
      Set.image_inter K.position_injective] using hfaces.le

run_cmd do
  let target := ``Submission.planeComplexToSimplicialComplex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `planeComplexToSimplicialComplex target :: scope.openDecls } }

private theorem planeComplexToSimplicialComplex_faces_finite (K : PlaneComplex) :
    (planeComplexToSimplicialComplex K).faces.Finite := by
  classical
  change ((fun s : Finset K.Vertex => s.image K.position) ''
    (K.simplexes : Set (Finset K.Vertex))).Finite
  exact K.simplexes.finite_toSet.image _

run_cmd do
  let target := ``Submission.planeComplexToSimplicialComplex_faces_finite
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `planeComplexToSimplicialComplex_faces_finite target :: scope.openDecls } }

private theorem planeComplexToSimplicialComplex_space (K : PlaneComplex) :
    (planeComplexToSimplicialComplex K).space = K.support := by
  classical
  have hcarrier (t : Finset K.Vertex) :
      convexHull ℝ (t.image K.position : Set Plane) = K.cellCarrier t := by
    rw [PlaneComplex.cellCarrier, Finset.coe_image]
  change (⋃ s ∈ ((fun t : Finset K.Vertex => t.image K.position) ''
      (K.simplexes : Set (Finset K.Vertex))), convexHull ℝ (s : Set Plane)) =
    ⋃ t ∈ K.simplexes, K.cellCarrier t
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨t, ht, rfl⟩ := hs
    exact Set.mem_iUnion₂.mpr ⟨t, ht, hcarrier t ▸ hx⟩
  · intro hx
    obtain ⟨t, ht, hx⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨t.image K.position, ⟨t, ht, rfl⟩,
      (hcarrier t).symm ▸ hx⟩

run_cmd do
  let target := ``Submission.planeComplexToSimplicialComplex_space
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `planeComplexToSimplicialComplex_space target :: scope.openDecls } }

private theorem planeComplexToSimplicialComplex_pure (K : PlaneComplex)
    (hpure : K.IsPure2) :
    ∀ s ∈ (planeComplexToSimplicialComplex K).faces,
      ∃ t ∈ (planeComplexToSimplicialComplex K).faces, s ⊆ t ∧ t.card = 3 := by
  classical
  rintro s ⟨S, hS, rfl⟩
  obtain ⟨T, hT, hST, hcard⟩ := hpure S hS
  refine ⟨T.image K.position, ⟨T, hT, rfl⟩, Finset.image_subset_image hST, ?_⟩
  rw [Finset.card_image_of_injective _ K.position_injective, hcard]

run_cmd do
  let target := ``Submission.planeComplexToSimplicialComplex_pure
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `planeComplexToSimplicialComplex_pure target :: scope.openDecls } }

namespace Schoenflies.PrePolygon

variable {m : ℕ} (P : PrePolygon m)

private theorem isCompact_closure_inside : IsCompact (closure (Schoenflies.inside P.carrier)) :=
  P.isSeparating_carrier.isBounded_inside.isCompact_closure

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.isCompact_closure_inside
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.isCompact_closure_inside target :: scope.openDecls } }

private theorem closure_inside_eq_union :
    closure (Schoenflies.inside P.carrier) = Schoenflies.inside P.carrier ∪ P.carrier :=
  (IsRegionOf.inside P.carrier).closure_eq P.isSeparating_carrier

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.closure_inside_eq_union
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.closure_inside_eq_union target :: scope.openDecls } }

private noncomputable def edgeNormalLinear (p q : Plane) : Plane →ₗ[ℝ] ℝ where
  toFun x := (q - p) 0 * x 1 - (q - p) 1 * x 0
  map_add' := by
    intro x y
    simp only [PiLp.add_apply]
    ring
  map_smul' := by
    intro c x
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.edgeNormalLinear
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.edgeNormalLinear target :: scope.openDecls } }

private noncomputable def edgeLine (i : ZMod (m + 3)) : Plane →ᵃ[ℝ] ℝ :=
  AffineMap.mk' (fun x => edgeNormalLinear (P.vertex i) (P.vertex (i + 1))
      (x - P.vertex i))
    (edgeNormalLinear (P.vertex i) (P.vertex (i + 1))) (P.vertex i) (by
      intro x
      simp)

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.edgeLine
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.edgeLine target :: scope.openDecls } }

@[simp] private theorem edgeLine_initial (i : ZMod (m + 3)) :
    P.edgeLine i (P.vertex i) = 0 := by
  simp [edgeLine]

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.edgeLine_initial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.edgeLine_initial target :: scope.openDecls } }

@[simp] private theorem edgeLine_terminal (i : ZMod (m + 3)) :
    P.edgeLine i (P.vertex (i + 1)) = 0 := by
  simp [edgeLine, edgeNormalLinear]
  ring

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.edgeLine_terminal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.edgeLine_terminal target :: scope.openDecls } }

private theorem edgeLine_eq_zero_of_mem_edge (i : ZMod (m + 3)) {x : Plane}
    (hx : x ∈ P.edge i) : P.edgeLine i x = 0 := by
  rw [edge, segment_eq_image] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  simp [edgeLine, edgeNormalLinear]
  ring

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.edgeLine_eq_zero_of_mem_edge
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.edgeLine_eq_zero_of_mem_edge target :: scope.openDecls } }

private theorem edgeLine_surjective (i : ZMod (m + 3)) : Function.Surjective (P.edgeLine i) := by
  let dx : ℝ := (P.vertex (i + 1) - P.vertex i) 0
  let dy : ℝ := (P.vertex (i + 1) - P.vertex i) 1
  have hxy : dx ≠ 0 ∨ dy ≠ 0 := by
    by_contra h
    push Not at h
    apply P.vertex_ne_succ i
    ext j
    fin_cases j
    · exact (sub_eq_zero.mp (by simpa [dx, PiLp.sub_apply] using h.1)).symm
    · exact (sub_eq_zero.mp (by simpa [dy, PiLp.sub_apply] using h.2)).symm
  have hden : dx ^ 2 + dy ^ 2 ≠ 0 := by
    rcases hxy with hx | hy
    · nlinarith [sq_pos_of_ne_zero hx]
    · nlinarith [sq_pos_of_ne_zero hy]
  intro y
  refine ⟨P.vertex i + (y / (dx ^ 2 + dy ^ 2)) • planePoint (-dy) dx, ?_⟩
  change (P.vertex (i + 1) - P.vertex i) 0 *
      (P.vertex i + (y / (dx ^ 2 + dy ^ 2)) • planePoint (-dy) dx - P.vertex i) 1 -
      (P.vertex (i + 1) - P.vertex i) 1 *
      (P.vertex i + (y / (dx ^ 2 + dy ^ 2)) • planePoint (-dy) dx - P.vertex i) 0 = y
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, planePoint_apply_zero,
    planePoint_apply_one, smul_eq_mul]
  ring_nf
  field_simp [hden]
  dsimp [dx, dy]
  ring_nf

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.edgeLine_surjective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.edgeLine_surjective target :: scope.openDecls } }

private theorem interior_edgeLine_nonneg (i : ZMod (m + 3)) :
    interior {x | 0 ≤ P.edgeLine i x} = {x | 0 < P.edgeLine i x} := by
  let f := P.edgeLine i
  change interior (f ⁻¹' Set.Ici 0) = f ⁻¹' Set.Ioi 0
  rw [← (f.isOpenMap f.continuous_of_finiteDimensional
    (P.edgeLine_surjective i)).preimage_interior_eq_interior_preimage
      f.continuous_of_finiteDimensional, interior_Ici]

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.interior_edgeLine_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.interior_edgeLine_nonneg target :: scope.openDecls } }

private theorem interior_edgeLine_nonpos (i : ZMod (m + 3)) :
    interior {x | P.edgeLine i x ≤ 0} = {x | P.edgeLine i x < 0} := by
  let f := P.edgeLine i
  change interior (f ⁻¹' Set.Iic 0) = f ⁻¹' Set.Iio 0
  rw [← (f.isOpenMap f.continuous_of_finiteDimensional
    (P.edgeLine_surjective i)).preimage_interior_eq_interior_preimage
      f.continuous_of_finiteDimensional, interior_Iic]

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.interior_edgeLine_nonpos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.interior_edgeLine_nonpos target :: scope.openDecls } }

private noncomputable def edgeLines : List (Plane →ᵃ[ℝ] ℝ) :=
  (Finset.univ : Finset (ZMod (m + 3))).toList.map P.edgeLine

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.edgeLines
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.edgeLines target :: scope.openDecls } }

private theorem edgeLine_mem_edgeLines (i : ZMod (m + 3)) : P.edgeLine i ∈ P.edgeLines := by
  simp [edgeLines]

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.edgeLine_mem_edgeLines
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.edgeLine_mem_edgeLines target :: scope.openDecls } }

private noncomputable def enclosingRadius : ℝ :=
  _root_.Max.max (P.isCompact_closure_inside.isBounded.subset_closedBall (0 : Plane)).choose 1

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.enclosingRadius
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.enclosingRadius target :: scope.openDecls } }

private theorem enclosingRadius_pos : 0 < P.enclosingRadius := by
  unfold enclosingRadius
  exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.enclosingRadius_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.enclosingRadius_pos target :: scope.openDecls } }

private theorem closedRegion_subset_enclosingBall :
    (closure (Schoenflies.inside P.carrier)) ⊆ Metric.closedBall (0 : Plane) P.enclosingRadius := by
  intro x hx
  have h := (P.isCompact_closure_inside.isBounded.subset_closedBall (0 : Plane)).choose_spec hx
  rw [Metric.mem_closedBall] at h ⊢
  exact h.trans (le_max_left _ _)

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.closedRegion_subset_enclosingBall
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.closedRegion_subset_enclosingBall target :: scope.openDecls } }

private def enclosingTriangleVertices (R : ℝ) : Fin 3 → Plane :=
  ![planePoint (-3 * R) (-2 * R), planePoint (3 * R) (-2 * R), planePoint 0 (4 * R)]

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.enclosingTriangleVertices
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.enclosingTriangleVertices target :: scope.openDecls } }

private theorem enclosingTriangleVertices_affineIndependent {R : ℝ} (hR : 0 < R) :
    AffineIndependent ℝ (enclosingTriangleVertices R) := by
  apply affineIndependent_plane_triple_of_det_ne_zero
  simp only [planePoint_apply_zero, planePoint_apply_one, PiLp.sub_apply]
  nlinarith

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.enclosingTriangleVertices_affineIndependent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.enclosingTriangleVertices_affineIndependent target :: scope.openDecls } }

private theorem closedBall_subset_enclosingTriangle {R : ℝ} (hR : 0 < R) :
    Metric.closedBall (0 : Plane) R ⊆
      convexHull ℝ (Set.range (enclosingTriangleVertices R)) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  have hx0 := PiLp.norm_apply_le (p := 2) x (0 : Fin 2)
  have hx1 := PiLp.norm_apply_le (p := 2) x (1 : Fin 2)
  simp only [Real.norm_eq_abs] at hx0 hx1
  have hx0lo : -R ≤ x 0 := by linarith [neg_abs_le (x 0)]
  have hx0hi : x 0 ≤ R := by linarith [le_abs_self (x 0)]
  have hx1lo : -R ≤ x 1 := by linarith [neg_abs_le (x 1)]
  have hx1hi : x 1 ≤ R := by linarith [le_abs_self (x 1)]
  let w : Fin 3 → ℝ :=
    ![(4 * R - x 1 - 2 * x 0) / (12 * R),
      (4 * R - x 1 + 2 * x 0) / (12 * R),
      (x 1 + 2 * R) / (6 * R)]
  apply mem_convexHull_range_fin3_of_weights _ x w
  · intro i
    fin_cases i
    · dsimp [w]
      exact div_nonneg (by linarith) (by positivity)
    · dsimp [w]
      exact div_nonneg (by linarith) (by positivity)
    · dsimp [w]
      exact div_nonneg (by linarith) (by positivity)
  · change (4 * R - x 1 - 2 * x 0) / (12 * R) +
        (4 * R - x 1 + 2 * x 0) / (12 * R) +
        (x 1 + 2 * R) / (6 * R) = 1
    field_simp [hR.ne']
    ring
  · ext i
    fin_cases i <;> simp [w, enclosingTriangleVertices, planePoint]
    all_goals field_simp [hR.ne']; ring

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.closedBall_subset_enclosingTriangle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.closedBall_subset_enclosingTriangle target :: scope.openDecls } }

private noncomputable def enclosingMesh : TriangleMesh :=
  TriangleMesh.single (enclosingTriangleVertices P.enclosingRadius)
    (enclosingTriangleVertices_affineIndependent P.enclosingRadius_pos)

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.enclosingMesh
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.enclosingMesh target :: scope.openDecls } }

private theorem closedRegion_subset_enclosingMesh_support :
    (closure (Schoenflies.inside P.carrier)) ⊆ P.enclosingMesh.toPlaneComplex.support := by
  rw [enclosingMesh, TriangleMesh.single_support]
  exact P.closedRegion_subset_enclosingBall.trans
    (closedBall_subset_enclosingTriangle P.enclosingRadius_pos)

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.closedRegion_subset_enclosingMesh_support
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.closedRegion_subset_enclosingMesh_support target :: scope.openDecls } }

private noncomputable def arrangementMesh : TriangleMesh :=
  P.enclosingMesh.refineByLines P.edgeLines

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.arrangementMesh
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.arrangementMesh target :: scope.openDecls } }

private theorem arrangementMesh_support :
    P.arrangementMesh.toPlaneComplex.support = P.enclosingMesh.toPlaneComplex.support :=
  P.enclosingMesh.refineByLines_support P.edgeLines

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.arrangementMesh_support
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.arrangementMesh_support target :: scope.openDecls } }

private theorem arrangementMesh_isMonochromatic (i : ZMod (m + 3)) :
    P.arrangementMesh.IsMonochromatic (P.edgeLine i) :=
  P.enclosingMesh.refineByLines_isMonochromatic_of_mem P.edgeLines (P.edgeLine_mem_edgeLines i)

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.arrangementMesh_isMonochromatic
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.arrangementMesh_isMonochromatic target :: scope.openDecls } }

private theorem closedRegion_subset_arrangementMesh_support :
    (closure (Schoenflies.inside P.carrier)) ⊆ P.arrangementMesh.toPlaneComplex.support := by
  rw [P.arrangementMesh_support]
  exact P.closedRegion_subset_enclosingMesh_support

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.closedRegion_subset_arrangementMesh_support
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.closedRegion_subset_arrangementMesh_support target :: scope.openDecls } }

private def arrangementTriangleCarrier (t : Finset P.arrangementMesh.Vertex) : Set Plane :=
  convexHull ℝ (P.arrangementMesh.position '' (t : Set _))

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.arrangementTriangleCarrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.arrangementTriangleCarrier target :: scope.openDecls } }

private theorem convex_arrangementTriangleCarrier (t : Finset P.arrangementMesh.Vertex) :
    Convex ℝ (P.arrangementTriangleCarrier t) :=
  convex_convexHull ℝ _

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.convex_arrangementTriangleCarrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.convex_arrangementTriangleCarrier target :: scope.openDecls } }

private theorem isClosed_arrangementTriangleCarrier (t : Finset P.arrangementMesh.Vertex) :
    IsClosed (P.arrangementTriangleCarrier t) :=
  (t.finite_toSet.image P.arrangementMesh.position).isClosed_convexHull ℝ

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.isClosed_arrangementTriangleCarrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.isClosed_arrangementTriangleCarrier target :: scope.openDecls } }

private theorem arrangementTriangleCarrier_interior_nonempty
    {t : Finset P.arrangementMesh.Vertex} (ht : t ∈ P.arrangementMesh.triangles) :
    (interior (P.arrangementTriangleCarrier t)).Nonempty := by
  apply (P.convex_arrangementTriangleCarrier t).interior_nonempty_iff_affineSpan_eq_top.mpr
  rw [arrangementTriangleCarrier, affineSpan_convexHull]
  have hrange : Set.range (fun v : t => P.arrangementMesh.position v) =
      P.arrangementMesh.position '' (t : Set _) := by
    ext x
    simp
  rw [← hrange]
  have hAI := P.arrangementMesh.affineIndependent_triangle t ht
  apply hAI.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  rw [Fintype.card_coe, P.arrangementMesh.card_triangle t ht]
  simp

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.arrangementTriangleCarrier_interior_nonempty
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.arrangementTriangleCarrier_interior_nonempty target :: scope.openDecls } }

private theorem closure_interior_arrangementTriangleCarrier
    {t : Finset P.arrangementMesh.Vertex} (ht : t ∈ P.arrangementMesh.triangles) :
    closure (interior (P.arrangementTriangleCarrier t)) = P.arrangementTriangleCarrier t := by
  calc
    closure (interior (P.arrangementTriangleCarrier t)) =
        closure (P.arrangementTriangleCarrier t) :=
      (P.convex_arrangementTriangleCarrier t).closure_interior_eq_closure_of_nonempty_interior
        (P.arrangementTriangleCarrier_interior_nonempty ht)
    _ = P.arrangementTriangleCarrier t := (P.isClosed_arrangementTriangleCarrier t).closure_eq

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.closure_interior_arrangementTriangleCarrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.closure_interior_arrangementTriangleCarrier target :: scope.openDecls } }

private theorem arrangementTriangle_interior_disjoint_carrier
    {t : Finset P.arrangementMesh.Vertex} (ht : t ∈ P.arrangementMesh.triangles) :
    Disjoint
      (interior (P.arrangementTriangleCarrier t))
      P.carrier := by
  rw [Set.disjoint_left]
  intro x hxint hxcarrier
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxcarrier
  have hxzero : P.edgeLine i x = 0 := P.edgeLine_eq_zero_of_mem_edge i hxi
  rcases P.arrangementMesh_isMonochromatic i t ht with hpos | hneg
  · have hsubset : P.arrangementTriangleCarrier t ⊆
        {y | 0 ≤ P.edgeLine i y} := by
      rw [arrangementTriangleCarrier]
      apply convexHull_min
      · rintro y ⟨v, hv, rfl⟩
        exact hpos v hv
      · exact (convex_Ici (0 : ℝ)).affine_preimage (P.edgeLine i)
    have hxstrict := interior_mono hsubset hxint
    rw [P.interior_edgeLine_nonneg i] at hxstrict
    change 0 < P.edgeLine i x at hxstrict
    linarith
  · have hsubset : P.arrangementTriangleCarrier t ⊆
        {y | P.edgeLine i y ≤ 0} := by
      rw [arrangementTriangleCarrier]
      apply convexHull_min
      · rintro y ⟨v, hv, rfl⟩
        exact hneg v hv
      · exact (convex_Iic (0 : ℝ)).affine_preimage (P.edgeLine i)
    have hxstrict := interior_mono hsubset hxint
    rw [P.interior_edgeLine_nonpos i] at hxstrict
    change P.edgeLine i x < 0 at hxstrict
    linarith

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.arrangementTriangle_interior_disjoint_carrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.arrangementTriangle_interior_disjoint_carrier target :: scope.openDecls } }

private theorem arrangementTriangle_interior_side
    {t : Finset P.arrangementMesh.Vertex} (ht : t ∈ P.arrangementMesh.triangles) :
    interior (P.arrangementTriangleCarrier t) ⊆ (Schoenflies.inside P.carrier) ∨
      interior (P.arrangementTriangleCarrier t) ⊆ (Schoenflies.outside P.carrier) := by
  let s := interior (P.arrangementTriangleCarrier t)
  have hsconn : IsPreconnected s :=
    (P.convex_arrangementTriangleCarrier t).interior.isPreconnected
  have hscarrier : s ⊆ P.carrierᶜ := by
    intro x hx
    exact Set.disjoint_left.mp (P.arrangementTriangle_interior_disjoint_carrier ht) hx
  have hsunion : s ⊆ (Schoenflies.inside P.carrier) ∪ (Schoenflies.outside P.carrier) := by
    rw [Schoenflies.inside_union_outside P.carrier]
    exact hscarrier
  obtain ⟨x, hx⟩ := P.arrangementTriangleCarrier_interior_nonempty ht
  have hxside := hsunion hx
  rcases hxside with hxin | hxout
  · exact Or.inl <| hsconn.subset_left_of_subset_union P.isSeparating_carrier.isOpen_inside
      P.isSeparating_carrier.isOpen_outside
      (Schoenflies.disjoint_inside_outside (C := P.carrier)) hsunion ⟨x, hx, hxin⟩
  · exact Or.inr <| hsconn.subset_right_of_subset_union P.isSeparating_carrier.isOpen_inside
      P.isSeparating_carrier.isOpen_outside
      (Schoenflies.disjoint_inside_outside (C := P.carrier)) hsunion ⟨x, hx, hxout⟩

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.arrangementTriangle_interior_side
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.arrangementTriangle_interior_side target :: scope.openDecls } }

private def isInteriorArrangementTriangle (t : Finset P.arrangementMesh.Vertex) : Prop :=
  interior (P.arrangementTriangleCarrier t) ⊆ (Schoenflies.inside P.carrier)

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.isInteriorArrangementTriangle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.isInteriorArrangementTriangle target :: scope.openDecls } }

private noncomputable def closedRegionMesh : TriangleMesh :=
  by
    classical
    exact P.arrangementMesh.restrictTriangles P.isInteriorArrangementTriangle

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.closedRegionMesh
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.closedRegionMesh target :: scope.openDecls } }

private theorem closedRegionMesh_triangle_mem {t : Finset P.closedRegionMesh.Vertex} :
    t ∈ P.closedRegionMesh.triangles ↔
      t ∈ P.arrangementMesh.triangles ∧ P.isInteriorArrangementTriangle t := by
  classical
  exact P.arrangementMesh.mem_restrictTriangles_triangles P.isInteriorArrangementTriangle

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.closedRegionMesh_triangle_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.closedRegionMesh_triangle_mem target :: scope.openDecls } }

private theorem arrangementTriangleCarrier_subset_closedRegion
    {t : Finset P.arrangementMesh.Vertex} (ht : t ∈ P.arrangementMesh.triangles)
    (hinside : P.isInteriorArrangementTriangle t) :
    P.arrangementTriangleCarrier t ⊆ (closure (Schoenflies.inside P.carrier)) := by
  rw [← P.closure_interior_arrangementTriangleCarrier ht]
  exact closure_mono hinside

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.arrangementTriangleCarrier_subset_closedRegion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.arrangementTriangleCarrier_subset_closedRegion target :: scope.openDecls } }

private theorem closedRegionMesh_support_subset :
    P.closedRegionMesh.toPlaneComplex.support ⊆ (closure (Schoenflies.inside P.carrier)) := by
  rw [TriangleMesh.toPlaneComplex_support]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  obtain ⟨htarr, htinside⟩ := P.closedRegionMesh_triangle_mem.mp ht
  exact P.arrangementTriangleCarrier_subset_closedRegion htarr htinside hxt

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.closedRegionMesh_support_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.closedRegionMesh_support_subset target :: scope.openDecls } }

private theorem interiorRegion_subset_closedRegionMesh_support :
    (Schoenflies.inside P.carrier) ⊆ P.closedRegionMesh.toPlaneComplex.support := by
  intro x hxinside
  have hxclosed : x ∈ (closure (Schoenflies.inside P.carrier)) := by
    rw [P.closure_inside_eq_union]
    exact Or.inl hxinside
  have hxsupport := P.closedRegion_subset_arrangementMesh_support hxclosed
  rw [TriangleMesh.toPlaneComplex_support] at hxsupport
  simp only [Set.mem_iUnion] at hxsupport
  obtain ⟨t, ht, hxt⟩ := hxsupport
  have hxclosure : x ∈ closure (interior (P.arrangementTriangleCarrier t)) := by
    rw [P.closure_interior_arrangementTriangleCarrier ht]
    exact hxt
  have hxclosureInter :
      x ∈ closure ((Schoenflies.inside P.carrier) ∩ interior (P.arrangementTriangleCarrier t)) :=
    P.isSeparating_carrier.isOpen_inside.inter_closure ⟨hxinside, hxclosure⟩
  have hmeet' :
      ((Schoenflies.inside P.carrier) ∩ interior (P.arrangementTriangleCarrier t)).Nonempty :=
    Set.Nonempty.of_closure ⟨x, hxclosureInter⟩
  have hmeet :
      (interior (P.arrangementTriangleCarrier t) ∩ (Schoenflies.inside P.carrier)).Nonempty := by
    obtain ⟨y, hyinside, hyt⟩ := hmeet'
    exact ⟨y, hyt, hyinside⟩
  have htinside : P.isInteriorArrangementTriangle t := by
    rcases P.arrangementTriangle_interior_side ht with hin | hout
    · exact hin
    · obtain ⟨y, hyt, hyinside⟩ := hmeet
      exact False.elim <| Set.disjoint_left.mp
        (Schoenflies.disjoint_inside_outside (C := P.carrier)) hyinside (hout hyt)
  rw [TriangleMesh.toPlaneComplex_support]
  simp only [Set.mem_iUnion]
  exact ⟨t, P.closedRegionMesh_triangle_mem.mpr ⟨ht, htinside⟩, hxt⟩

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.interiorRegion_subset_closedRegionMesh_support
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.interiorRegion_subset_closedRegionMesh_support target :: scope.openDecls } }

private theorem closedRegionMesh_support :
    P.closedRegionMesh.toPlaneComplex.support = (closure (Schoenflies.inside P.carrier)) := by
  apply Set.Subset.antisymm P.closedRegionMesh_support_subset
  exact closure_minimal
    P.interiorRegion_subset_closedRegionMesh_support
    P.closedRegionMesh.toPlaneComplex.isCompact_support.isClosed

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.closedRegionMesh_support
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.closedRegionMesh_support target :: scope.openDecls } }

private theorem disjoint_carrier_exteriorRegion :
    Disjoint P.carrier (Schoenflies.outside P.carrier) := by
  rw [Set.disjoint_left]
  intro x hxcarrier hxexterior
  have hxcompl : x ∈ P.carrierᶜ := by
    rw [← Schoenflies.inside_union_outside P.carrier]
    exact Or.inr hxexterior
  exact hxcompl hxcarrier

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.disjoint_carrier_exteriorRegion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.disjoint_carrier_exteriorRegion target :: scope.openDecls } }

private theorem disjoint_closedRegion_exteriorRegion :
    Disjoint (closure (Schoenflies.inside P.carrier)) (Schoenflies.outside P.carrier) := by
  rw [P.closure_inside_eq_union]
  exact (Schoenflies.disjoint_inside_outside (C := P.carrier)).sup_left
    P.disjoint_carrier_exteriorRegion

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.disjoint_closedRegion_exteriorRegion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.disjoint_closedRegion_exteriorRegion target :: scope.openDecls } }

private theorem frontier_closedRegion :
    frontier (closure (Schoenflies.inside P.carrier)) = P.carrier := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxclosed : x ∈ (closure (Schoenflies.inside P.carrier)) := by
      have hx' := frontier_subset_closure hx
      simpa [P.isCompact_closure_inside.isClosed.closure_eq] using hx'
    rw [P.closure_inside_eq_union] at hxclosed
    rcases hxclosed with hxinside | hxcarrier
    · have hxint : x ∈ interior (closure (Schoenflies.inside P.carrier)) :=
        interior_maximal (by rw [P.closure_inside_eq_union]; exact Set.subset_union_left)
          P.isSeparating_carrier.isOpen_inside hxinside
      exact False.elim <| Set.disjoint_left.mp disjoint_interior_frontier hxint hx
    · exact hxcarrier
  · intro x hxcarrier
    have hxclosed : x ∈ (closure (Schoenflies.inside P.carrier)) := by
      rw [P.closure_inside_eq_union]
      exact Or.inr hxcarrier
    rw [P.isCompact_closure_inside.isClosed.frontier_eq]
    refine ⟨hxclosed, ?_⟩
    intro hxint
    have hxclosureExterior : x ∈ closure (Schoenflies.outside P.carrier) :=
      frontier_subset_closure (P.isSeparating_carrier.frontier_outside.symm ▸ hxcarrier)
    have hxclosureInter :
        x ∈ closure (interior (closure (Schoenflies.inside P.carrier)) ∩
          Schoenflies.outside P.carrier) :=
      isOpen_interior.inter_closure ⟨hxint, hxclosureExterior⟩
    obtain ⟨y, hyint, hyexterior⟩ := Set.Nonempty.of_closure ⟨x, hxclosureInter⟩
    exact Set.disjoint_left.mp P.disjoint_closedRegion_exteriorRegion
      (interior_subset hyint) hyexterior

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.frontier_closedRegion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.frontier_closedRegion target :: scope.openDecls } }

private theorem interior_closedRegion :
    interior (closure (Schoenflies.inside P.carrier)) = Schoenflies.inside P.carrier := by
  apply Set.Subset.antisymm
  · intro p hp
    have hpClosed : p ∈ (closure (Schoenflies.inside P.carrier)) := interior_subset hp
    rw [P.closure_inside_eq_union] at hpClosed
    rcases hpClosed with hpInside | hpCarrier
    · exact hpInside
    · have hpFrontier : p ∈ frontier (closure (Schoenflies.inside P.carrier)) := by
        rw [P.frontier_closedRegion]
        exact hpCarrier
      exact (Set.disjoint_left.mp disjoint_interior_frontier hp hpFrontier).elim
  · exact interior_maximal (by rw [P.closure_inside_eq_union]; exact Set.subset_union_left)
      P.isSeparating_carrier.isOpen_inside

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.interior_closedRegion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.interior_closedRegion target :: scope.openDecls } }

private theorem isConnected_closedRegion :
    IsConnected (closure (Schoenflies.inside P.carrier)) :=
  P.isSeparating_carrier.isConnected_inside.closure

run_cmd do
  let target := ``Submission.Schoenflies.PrePolygon.isConnected_closedRegion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Schoenflies.PrePolygon.isConnected_closedRegion target :: scope.openDecls } }

theorem exists_triangle_mesh_inside :
    ∃ M : TriangleMesh,
      M.toPlaneComplex.support = closure (Schoenflies.inside P.carrier) ∧
        frontier M.toPlaneComplex.support = P.carrier := by
  refine ⟨P.closedRegionMesh, P.closedRegionMesh_support, ?_⟩
  rw [P.closedRegionMesh_support]
  exact P.frontier_closedRegion

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PrePolygon.exists_triangle_mesh_inside then
    throwError "Refusing to shadow existing declaration Schoenflies.PrePolygon.exists_triangle_mesh_inside"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PrePolygon.exists_triangle_mesh_inside ``Submission.Schoenflies.PrePolygon.exists_triangle_mesh_inside

theorem exists_simplicial_complex_inside :
    ∃ K : Geometry.SimplicialComplex ℝ Plane,
      K.faces.Finite ∧ K.space = closure (Schoenflies.inside P.carrier) ∧
        ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3 := by
  refine ⟨planeComplexToSimplicialComplex P.closedRegionMesh.toPlaneComplex,
    planeComplexToSimplicialComplex_faces_finite _, ?_,
    planeComplexToSimplicialComplex_pure _ P.closedRegionMesh.toPlaneComplex_isPure2⟩
  exact (planeComplexToSimplicialComplex_space _).trans P.closedRegionMesh_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Schoenflies.PrePolygon.exists_simplicial_complex_inside then
    throwError "Refusing to shadow existing declaration Schoenflies.PrePolygon.exists_simplicial_complex_inside"
  Lean.modifyEnv fun env => Lean.addAlias env `Schoenflies.PrePolygon.exists_simplicial_complex_inside ``Submission.Schoenflies.PrePolygon.exists_simplicial_complex_inside

end Schoenflies.PrePolygon
