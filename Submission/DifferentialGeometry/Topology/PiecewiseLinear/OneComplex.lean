import Submission.DifferentialGeometry.Topology.PiecewiseLinear.StarComplex
import Submission.DifferentialGeometry.Topology.SimplicialComplex.EdgeGraph
import Mathlib.Combinatorics.SimpleGraph.Maps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open _root_.Classical in
noncomputable def vertexMapOfEdgeGraphIso
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    (e : SimplicialComplex.edgeGraph K ≃g SimplicialComplex.edgeGraph L) (x : E) : F :=
  if hx : x ∈ K.vertices then (e ⟨x, hx⟩ : F) else 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.vertexMapOfEdgeGraphIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.vertexMapOfEdgeGraphIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.vertexMapOfEdgeGraphIso ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.vertexMapOfEdgeGraphIso

open _root_.Classical in
@[simp]
theorem vertexMapOfEdgeGraphIso_apply
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    (e : SimplicialComplex.edgeGraph K ≃g SimplicialComplex.edgeGraph L)
    (v : K.vertices) :
    vertexMapOfEdgeGraphIso K L e v = (e v : F) := by
  simp [vertexMapOfEdgeGraphIso, v.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.vertexMapOfEdgeGraphIso_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.vertexMapOfEdgeGraphIso_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.vertexMapOfEdgeGraphIso_apply ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.vertexMapOfEdgeGraphIso_apply

open _root_.Classical in
theorem image_mem_faces_of_edgeGraphIso
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    (hK : ∀ s ∈ K.faces, s.card ≤ 2)
    (e : SimplicialComplex.edgeGraph K ≃g SimplicialComplex.edgeGraph L)
    {s : Finset E} (hs : s ∈ K.faces) :
    s.image (vertexMapOfEdgeGraphIso K L e) ∈ L.faces := by
  have hsne := K.nonempty_of_mem_faces hs
  have hscard := hK s hs
  rcases Nat.lt_or_eq_of_le hscard with hlt | htwo
  · have hone : s.card = 1 := by
      have hpos := Finset.card_pos.mpr hsne
      omega
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hone
    have hx : x ∈ K.vertices := K.down_closed hs (by simp) (by simp)
    have hmap : vertexMapOfEdgeGraphIso K L e x = (e ⟨x, hx⟩ : F) :=
      vertexMapOfEdgeGraphIso_apply K L e ⟨x, hx⟩
    rw [Finset.image_singleton, hmap]
    exact (e ⟨x, hx⟩).2
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp htwo
    have hx : x ∈ K.vertices := K.down_closed hs (by simp) (by simp)
    have hy : y ∈ K.vertices := K.down_closed hs (by simp) (by simp)
    have hadj : (SimplicialComplex.edgeGraph K).Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
      exact ⟨fun h => hxy (congrArg Subtype.val h), hs⟩
    have hadj' := (e.map_rel_iff).mpr hadj
    have hmapx : vertexMapOfEdgeGraphIso K L e x = (e ⟨x, hx⟩ : F) :=
      vertexMapOfEdgeGraphIso_apply K L e ⟨x, hx⟩
    have hmapy : vertexMapOfEdgeGraphIso K L e y = (e ⟨y, hy⟩ : F) :=
      vertexMapOfEdgeGraphIso_apply K L e ⟨y, hy⟩
    rw [Finset.image_insert, Finset.image_singleton, hmapx, hmapy]
    exact hadj'.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_mem_faces_of_edgeGraphIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_mem_faces_of_edgeGraphIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_mem_faces_of_edgeGraphIso ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_mem_faces_of_edgeGraphIso

open _root_.Classical in
theorem isGlueIso_vertexMapOfEdgeGraphIso
    (K : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    (hK : ∀ s ∈ K.faces, s.card ≤ 2) (hL : ∀ t ∈ L.faces, t.card ≤ 2)
    (e : SimplicialComplex.edgeGraph K ≃g SimplicialComplex.edgeGraph L) :
    IsGlueIso K L (vertexMapOfEdgeGraphIso K L e)
      (vertexMapOfEdgeGraphIso L K e.symm) := by
  refine ⟨fun s hs => image_mem_faces_of_edgeGraphIso K L hK e hs,
    fun t ht => image_mem_faces_of_edgeGraphIso L K hL e.symm ht, ?_, ?_⟩
  · intro s hs v hv
    have hvK : v ∈ K.vertices :=
      K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    simp [vertexMapOfEdgeGraphIso, hvK]
  · intro t ht w hw
    have hwL : w ∈ L.vertices :=
      L.down_closed ht (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w)
    simp [vertexMapOfEdgeGraphIso, hwL]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isGlueIso_vertexMapOfEdgeGraphIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isGlueIso_vertexMapOfEdgeGraphIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isGlueIso_vertexMapOfEdgeGraphIso ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isGlueIso_vertexMapOfEdgeGraphIso

open _root_.Classical in
theorem isPLHomeomorphOn_of_edgeGraphIso
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    (hK : ∀ s ∈ K.faces, s.card ≤ 2) (hL : ∀ t ∈ L.faces, t.card ≤ 2)
    (e : SimplicialComplex.edgeGraph K ≃g SimplicialComplex.edgeGraph L) :
    IsPLHomeomorphOn (simplicialMap K (vertexMapOfEdgeGraphIso K L e)) K.space L.space :=
  (isGlueIso_vertexMapOfEdgeGraphIso K L hK hL e).isPLHomeomorphOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_of_edgeGraphIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_of_edgeGraphIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_of_edgeGraphIso ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_of_edgeGraphIso

end DifferentialGeometry.Topology.PiecewiseLinear
