/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PlanarSchoenflies
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.TriangleDeletion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open _root_.Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise (Plane TriangleMesh)

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Classical in
noncomputable def triangleMeshOfSubcomplex
    (K L : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces] : TriangleMesh :=
  (planeComplexOfSimplicialComplex K).toTriangleMesh.restrictTriangles
    fun u : Finset K.vertices => u.map ⟨Subtype.val, Subtype.val_injective⟩ ∈ L.faces

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex

open _root_.Classical in
theorem mem_triangleMeshOfSubcomplex_triangles
    {K L : Geometry.SimplicialComplex ℝ Plane} [Finite K.faces]
    (hLK : L.faces ⊆ K.faces) {u : Finset K.vertices} :
    u ∈ (triangleMeshOfSubcomplex K L).triangles ↔
      u.map ⟨Subtype.val, Subtype.val_injective⟩ ∈ L.faces ∧ u.card = 3 := by
  have hvertices : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)
  let _ : Fintype K.vertices := hvertices.fintype
  let e : K.vertices ↪ Plane := ⟨Subtype.val, Subtype.val_injective⟩
  change u ∈ ((Finset.univ.filter (fun r : Finset K.vertices => r.map e ∈ K.faces)).filter
    (fun r => r.card = 3)).filter (fun r => r.map e ∈ L.faces) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hLK h.1, h.2⟩, h.1⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_triangleMeshOfSubcomplex_triangles then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_triangleMeshOfSubcomplex_triangles"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_triangleMeshOfSubcomplex_triangles ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_triangleMeshOfSubcomplex_triangles

open _root_.Classical in
theorem triangleMeshOfSubcomplex_support
    {K L : Geometry.SimplicialComplex ℝ Plane} [Finite K.faces]
    (hLK : L.faces ⊆ K.faces)
    (hpure : ∀ s ∈ L.faces, ∃ t ∈ L.faces, s ⊆ t ∧ t.card = 3) :
    (triangleMeshOfSubcomplex K L).toPlaneComplex.support = L.space := by
  let N := triangleMeshOfSubcomplex K L
  let e : K.vertices ↪ Plane := ⟨Subtype.val, Subtype.val_injective⟩
  have hcarrier (u : Finset K.vertices) :
      convexHull ℝ (N.position '' (u : Set K.vertices)) =
        convexHull ℝ ((u.map e : Finset Plane) : Set Plane) := by
    rw [Finset.coe_map]
    rfl
  rw [N.toPlaneComplex_support]
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
    have huL := (mem_triangleMeshOfSubcomplex_triangles hLK).mp hu
    exact L.convexHull_subset_space huL.1 (hcarrier u ▸ hxu)
  · intro hx
    obtain ⟨s, hs, hxs⟩ := L.mem_space_iff.mp hx
    obtain ⟨t, ht, hst, htcard⟩ := hpure s hs
    let r := t.subtype (fun v => v ∈ K.vertices)
    have hr : r.map e = t := Finset.subtype_map_of_mem fun v hv =>
      K.down_closed (hLK ht) (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have hrmem : r ∈ N.triangles := (mem_triangleMeshOfSubcomplex_triangles hLK).mpr
      ⟨hr.symm ▸ ht, by rw [← Finset.card_map e, hr, htcard]⟩
    refine mem_iUnion₂.mpr ⟨r, hrmem, ?_⟩
    have hxr : x ∈ convexHull ℝ ((r.map e : Finset Plane) : Set Plane) := by
      rw [hr]
      exact convexHull_mono (Finset.coe_subset.mpr hst) hxs
    exact (hcarrier r).symm ▸ hxr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex_support ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex_support

open _root_.Classical in
theorem triangleMeshOfSubcomplex_eraseTriangle_support
    {K L : Geometry.SimplicialComplex ℝ Plane} [Finite K.faces]
    (hLK : L.faces ⊆ K.faces) (t : Finset K.vertices) :
    ((triangleMeshOfSubcomplex K L).eraseTriangle t).toPlaneComplex.support =
      (eraseTriangleComplex L (t.map ⟨Subtype.val, Subtype.val_injective⟩)).space := by
  let N := triangleMeshOfSubcomplex K L
  let e : K.vertices ↪ Plane := ⟨Subtype.val, Subtype.val_injective⟩
  have hcarrier (u : Finset K.vertices) :
      convexHull ℝ ((N.eraseTriangle t).position '' (u : Set K.vertices)) =
        convexHull ℝ ((u.map e : Finset Plane) : Set Plane) := by
    rw [Finset.coe_map]
    rfl
  rw [(N.eraseTriangle t).toPlaneComplex_support, eraseTriangleComplex_space]
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
    have huData : u ≠ t ∧ u ∈ N.triangles := Finset.mem_erase.mp hu
    have huL := (mem_triangleMeshOfSubcomplex_triangles hLK).mp huData.2
    refine mem_iUnion₂.mpr ⟨u.map e, ⟨huL.1, ?_, ?_⟩, hcarrier u ▸ hxu⟩
    · exact (Finset.card_map e).trans huL.2
    · exact fun heq => huData.1 (Finset.map_injective e heq)
  · intro hx
    obtain ⟨u, ⟨huL, hucard, hut⟩, hxu⟩ := mem_iUnion₂.mp hx
    let r := u.subtype (fun v => v ∈ K.vertices)
    have hr : r.map e = u := Finset.subtype_map_of_mem fun v hv =>
      K.down_closed (hLK huL) (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have hrmem : r ∈ N.triangles := (mem_triangleMeshOfSubcomplex_triangles hLK).mpr
      ⟨hr.symm ▸ huL, by rw [← Finset.card_map e, hr, hucard]⟩
    have hrne : r ≠ t := fun heq => hut (hr.symm.trans (congrArg (Finset.map e) heq))
    refine mem_iUnion₂.mpr ⟨r, Finset.mem_erase.mpr ⟨hrne, hrmem⟩, ?_⟩
    have hxr : x ∈ convexHull ℝ ((r.map e : Finset Plane) : Set Plane) := by
      rw [hr]
      exact hxu
    exact (hcarrier r).symm ▸ hxr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex_eraseTriangle_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex_eraseTriangle_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex_eraseTriangle_support ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex_eraseTriangle_support

open _root_.Classical in
theorem triangleMeshOfSubcomplex_restrict
    (K L P : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces] (hPL : P.faces ⊆ L.faces) :
    (triangleMeshOfSubcomplex K L).restrictTriangles
        (fun u : Finset K.vertices => u.map ⟨Subtype.val, Subtype.val_injective⟩ ∈ P.faces) =
      triangleMeshOfSubcomplex K P := by
  let M := (planeComplexOfSimplicialComplex K).toTriangleMesh
  let e : M.Vertex ↪ Plane := ⟨M.position, M.position_injective⟩
  let q (Q : Geometry.SimplicialComplex ℝ Plane) : Finset M.Vertex → Prop :=
    fun u => u.map e ∈ Q.faces
  have hfilter : (M.triangles.filter (q L)).filter (q P) = M.triangles.filter (q P) := by
    ext u
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hPL h.2⟩, h.2⟩⟩
  change (M.restrictTriangles (q L)).restrictTriangles (q P) = M.restrictTriangles (q P)
  unfold LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.restrictTriangles
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex_restrict ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex_restrict

open _root_.Classical in
theorem triangleMeshOfSubcomplex_restrict_eraseTriangle
    (K L P : Geometry.SimplicialComplex ℝ Plane) [Finite K.faces] (hPL : P.faces ⊆ L.faces)
    (t : Finset K.vertices) :
    ((triangleMeshOfSubcomplex K L).restrictTriangles
        (fun u : Finset K.vertices => u.map ⟨Subtype.val, Subtype.val_injective⟩ ∈
            P.faces)).eraseTriangle t =
      (triangleMeshOfSubcomplex K P).eraseTriangle t := by
  let M := (planeComplexOfSimplicialComplex K).toTriangleMesh
  let e : M.Vertex ↪ Plane := ⟨M.position, M.position_injective⟩
  let q (Q : Geometry.SimplicialComplex ℝ Plane) : Finset M.Vertex → Prop :=
    fun u => u.map e ∈ Q.faces
  have hfilter : (M.triangles.filter (q L)).filter (q P) = M.triangles.filter (q P) := by
    ext u
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hPL h.2⟩, h.2⟩⟩
  change ((M.restrictTriangles (q L)).restrictTriangles (q P)).eraseTriangle t =
    (M.restrictTriangles (q P)).eraseTriangle t
  unfold LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.eraseTriangle
    LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh.restrictTriangles
  congr 1
  exact congrArg (fun u : Finset (Finset M.Vertex) => u.erase t) hfilter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex_restrict_eraseTriangle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex_restrict_eraseTriangle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex_restrict_eraseTriangle ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangleMeshOfSubcomplex_restrict_eraseTriangle

end DifferentialGeometry.Topology.PiecewiseLinear
