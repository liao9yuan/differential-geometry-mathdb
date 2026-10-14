import Submission.DifferentialGeometry.Topology.SimplicialComplex.OrderedCellAttachment
import Submission.DifferentialGeometry.Topology.SimplicialComplex.GeometricRealizationMap
import Submission.DifferentialGeometry.Topology.SimplicialComplex.GeometricFaceHomeomorphism
import Submission.DifferentialGeometry.Topology.Simplex.Reindex
import Submission.DifferentialGeometry.Topology.SimplicialSet.BoundaryRealization
import Submission.DifferentialGeometry.Topology.Category.TopCat.ClosedCover

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.Simplicial _root_.Opposite

namespace DifferentialGeometry.Topology.SimplicialComplex

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
  (K : Geometry.SimplicialComplex ℝ E) (s : Finset E) (hs : s ∈ K.faces)
  {n : ℕ} (hn : s.card = n + 1)

def orderedFaceRealizationHomeomorph :
    SSet.toTop.obj (Δ[n] : SSet.{u}) ≃ₜ convexHull ℝ (s : Set E) :=
  (SimplexCategory.toTopHomeo ⦋n⦌).trans
    ((DifferentialGeometry.Simplex.reindexHomeomorph (s.orderIsoOfFin hn).toEquiv).trans
      (geometricFaceHomeomorphism K hs))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceRealizationHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedFaceRealizationHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceRealizationHomeomorph ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedFaceRealizationHomeomorph


@[simp]
theorem orderedFaceRealizationHomeomorph_apply (x : SSet.toTop.obj (Δ[n] : SSet.{u})) :
    (orderedFaceRealizationHomeomorph K s hs hn x : E) =
      ∑ i, (SimplexCategory.toTopHomeo ⦋n⦌ x).val i • (s.orderEmbOfFin hn) i := by
  exact DifferentialGeometry.Simplex.vertexMap_reindex (s.orderIsoOfFin hn).toEquiv
    (fun i : s ↦ (i : E)) (SimplexCategory.toTopHomeo ⦋n⦌ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceRealizationHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedFaceRealizationHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceRealizationHomeomorph_apply ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedFaceRealizationHomeomorph_apply

theorem orderedFaceCellMap_geometricRealizationMap_apply
    (x : SSet.toTop.obj (Δ[n] : SSet.{u})) :
    geometricRealizationMap K
        (SSet.toTop.map (orderedFaceCellMap K.toPreAbstractSimplicialComplex s hs hn) x) =
      geometricSimplexMap K
        (orderedSimplexOfFace K.toPreAbstractSimplicialComplex s hs hn).val
        (SimplexCategory.toTopHomeo ⦋n⦌ x) := by
  let a := (orderedSimplexOfFace K.toPreAbstractSimplicialComplex s hs hn).val
  have hu : (TopCat.toSSetObjEquiv _ (_root_.Opposite.op ⦋n⦌))
      ((sSetTopAdj.unit.app (orderedSimplicialSet K.toPreAbstractSimplicialComplex)).app _ a)
        (SimplexCategory.toTopHomeo ⦋n⦌ x) =
      SSet.toTop.map (orderedFaceCellMap K.toPreAbstractSimplicialComplex s hs hn) x := by
    change (((sSetTopAdj.unit.app
      (orderedSimplicialSet K.toPreAbstractSimplicialComplex)).app (_root_.Opposite.op ⦋n⦌) a).down).hom
        (ULift.up (SimplexCategory.toTopHomeo ⦋n⦌ x)) = _
    rw [sSetTopAdj_unit_app_app_down]
    change SSet.toTop.map (orderedFaceCellMap K.toPreAbstractSimplicialComplex s hs hn)
      ((SimplexCategory.toTopHomeo ⦋n⦌).symm (SimplexCategory.toTopHomeo ⦋n⦌ x)) = _
    rw [Homeomorph.symm_apply_apply]
  rw [← hu]
  exact geometricRealizationMap_unit_apply K a _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap_geometricRealizationMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap_geometricRealizationMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap_geometricRealizationMap_apply ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap_geometricRealizationMap_apply

@[reassoc]
theorem orderedFaceCellMap_geometricRealizationMap :
    SSet.toTop.map (orderedFaceCellMap K.toPreAbstractSimplicialComplex s hs hn) ≫
        geometricRealizationMap K =
      (TopCat.isoOfHomeo (orderedFaceRealizationHomeomorph K s hs hn)).hom ≫
        DifferentialGeometry.TopCat.subspaceInclusion
          (Geometry.SimplicialComplex.convexHull_subset_space hs) := by
  apply TopCat.ext
  intro x
  apply Subtype.ext
  change (geometricRealizationMap K
    (SSet.toTop.map (orderedFaceCellMap K.toPreAbstractSimplicialComplex s hs hn) x) : E) =
      (orderedFaceRealizationHomeomorph K s hs hn x : E)
  rw [orderedFaceCellMap_geometricRealizationMap_apply,
    orderedFaceRealizationHomeomorph_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap_geometricRealizationMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap_geometricRealizationMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap_geometricRealizationMap ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap_geometricRealizationMap

theorem orderedFaceRealizationHomeomorph_mem_costar_iff
    (x : SSet.toTop.obj (Δ[n] : SSet.{u})) :
    (orderedFaceRealizationHomeomorph K s hs hn x : E) ∈ (geometricFaceCostar K s).space ↔
      SimplexCategory.toTopHomeo ⦋n⦌ x ∈ DifferentialGeometry.Simplex.boundary (Fin (n + 1)) := by
  change DifferentialGeometry.Simplex.vertexMap (fun i : s ↦ (i : E))
    (DifferentialGeometry.Simplex.reindexHomeomorph (s.orderIsoOfFin hn).toEquiv
      (SimplexCategory.toTopHomeo ⦋n⦌ x)) ∈ (geometricFaceCostar K s).space ↔ _
  rw [vertexMap_mem_geometricFaceCostar_iff K hs,
    DifferentialGeometry.Simplex.reindexHomeomorph_mem_boundary]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceRealizationHomeomorph_mem_costar_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedFaceRealizationHomeomorph_mem_costar_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceRealizationHomeomorph_mem_costar_iff ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedFaceRealizationHomeomorph_mem_costar_iff

theorem orderedFaceRealizationHomeomorph_mem_costar_iff_mem_boundary_range
    (x : SSet.toTop.obj (Δ[n] : SSet.{u})) :
    (orderedFaceRealizationHomeomorph K s hs hn x : E) ∈ (geometricFaceCostar K s).space ↔
      x ∈ Set.range (SSet.toTop.map (SSet.boundary n).ι) := by
  rw [orderedFaceRealizationHomeomorph_mem_costar_iff]
  have hr := DifferentialGeometry.SSet.range_toTopHomeo_boundary.{u} n
  constructor
  · intro hx
    have hx' : SimplexCategory.toTopHomeo ⦋n⦌ x ∈ Set.range
        (fun y : SSet.toTop.obj (SSet.boundary n : SSet.{u}) ↦
          SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map (SSet.boundary n).ι y)) := by
      rw [hr]
      exact hx
    obtain ⟨y, hy⟩ := hx'
    exact ⟨y, (SimplexCategory.toTopHomeo ⦋n⦌).injective hy⟩
  · rintro ⟨y, rfl⟩
    have hx : SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map (SSet.boundary n).ι y) ∈
        Set.range (fun y : SSet.toTop.obj (SSet.boundary n : SSet.{u}) ↦
          SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map (SSet.boundary n).ι y)) := ⟨y, rfl⟩
    rwa [hr] at hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceRealizationHomeomorph_mem_costar_iff_mem_boundary_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedFaceRealizationHomeomorph_mem_costar_iff_mem_boundary_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceRealizationHomeomorph_mem_costar_iff_mem_boundary_range ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedFaceRealizationHomeomorph_mem_costar_iff_mem_boundary_range

theorem orderedFaceCellMap_geometricRealizationMap_mem_costar_iff
    (x : SSet.toTop.obj (Δ[n] : SSet.{u})) :
    (geometricRealizationMap K
      (SSet.toTop.map (orderedFaceCellMap K.toPreAbstractSimplicialComplex s hs hn) x) : E) ∈
        (geometricFaceCostar K s).space ↔
      x ∈ Set.range (SSet.toTop.map (SSet.boundary n).ι) := by
  have he := congrArg Subtype.val
    (ConcreteCategory.congr_hom (orderedFaceCellMap_geometricRealizationMap K s hs hn) x)
  change (geometricRealizationMap K
    (SSet.toTop.map (orderedFaceCellMap K.toPreAbstractSimplicialComplex s hs hn) x) : E) =
      (orderedFaceRealizationHomeomorph K s hs hn x : E) at he
  rw [he]
  exact orderedFaceRealizationHomeomorph_mem_costar_iff_mem_boundary_range K s hs hn x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap_geometricRealizationMap_mem_costar_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap_geometricRealizationMap_mem_costar_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap_geometricRealizationMap_mem_costar_iff ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedFaceCellMap_geometricRealizationMap_mem_costar_iff

end DifferentialGeometry.Topology.SimplicialComplex
