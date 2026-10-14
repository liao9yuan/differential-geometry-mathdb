import Submission.DifferentialGeometry.Topology.SimplicialSet.BoundaryHomeomorphism
import Submission.DifferentialGeometry.Topology.Simplex.ULift
import Submission.DifferentialGeometry.Topology.Simplex.AttachmentRelativeHomology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Simplicial _root_.Topology

universe u

namespace DifferentialGeometry.SSet

def nativeSimplexHomeomorph (n : ℕ) :
    _root_.SSet.toTop.obj (Δ[n] : _root_.SSet.{u}) ≃ₜ
      stdSimplex ℝ (ULift.{u} (Fin (n + 1))) :=
  (TopCat.homeoOfIso (_root_.SSet.toTopSimplex.app ⦋n⦌)).trans
    (DifferentialGeometry.Simplex.uliftHomeomorph (Fin (n + 1)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.nativeSimplexHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.nativeSimplexHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.nativeSimplexHomeomorph ``Submission.DifferentialGeometry.SSet.nativeSimplexHomeomorph

def nativeBoundaryHomeomorph (n : ℕ) :
    _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet.{u}) ≃ₜ
      DifferentialGeometry.Simplex.boundary (ULift.{u} (Fin (n + 1))) :=
  (boundaryRealizationHomeomorph n).trans
    (DifferentialGeometry.Simplex.boundaryUliftHomeomorph (Fin (n + 1)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.nativeBoundaryHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.nativeBoundaryHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.nativeBoundaryHomeomorph ``Submission.DifferentialGeometry.SSet.nativeBoundaryHomeomorph

@[reassoc]
theorem nativeBoundaryHomeomorph_inclusion (n : ℕ) :
    _root_.SSet.toTop.map (_root_.SSet.boundary n).ι ≫
        (TopCat.isoOfHomeo (nativeSimplexHomeomorph.{u} n)).hom =
      (TopCat.isoOfHomeo (nativeBoundaryHomeomorph n)).hom ≫
        DifferentialGeometry.Simplex.Attachment.boundaryι := by
  apply ConcreteCategory.hom_ext
  intro x
  change DifferentialGeometry.Simplex.uliftHomeomorph (Fin (n + 1))
      ((_root_.SSet.toTopSimplex.hom.app ⦋n⦌)
        ((_root_.SSet.toTop.map (_root_.SSet.boundary n).ι) x)) =
    DifferentialGeometry.Simplex.uliftHomeomorph (Fin (n + 1)) ((boundaryRealizationHomeomorph n x).val)
  exact congrArg (DifferentialGeometry.Simplex.uliftHomeomorph (Fin (n + 1)))
    (boundaryRealizationHomeomorph_ambient n x).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.nativeBoundaryHomeomorph_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.nativeBoundaryHomeomorph_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.nativeBoundaryHomeomorph_inclusion ``Submission.DifferentialGeometry.SSet.nativeBoundaryHomeomorph_inclusion

theorem nativeSimplexHomeomorph_mem_boundary (n : ℕ)
    (x : _root_.SSet.toTop.obj (Δ[n] : _root_.SSet.{u})) :
    x ∈ Set.range (_root_.SSet.toTop.map (_root_.SSet.boundary n).ι) ↔
      nativeSimplexHomeomorph n x ∈ DifferentialGeometry.Simplex.boundary (ULift.{u} (Fin (n + 1))) := by
  have he (a : _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet.{u})) :
      nativeSimplexHomeomorph n ((_root_.SSet.toTop.map (_root_.SSet.boundary n).ι) a) =
        (nativeBoundaryHomeomorph n a).val :=
    ConcreteCategory.congr_hom (nativeBoundaryHomeomorph_inclusion n) a
  constructor
  · rintro ⟨a, rfl⟩
    rw [he]
    exact (nativeBoundaryHomeomorph n a).property
  · intro hx
    refine ⟨(nativeBoundaryHomeomorph n).symm ⟨nativeSimplexHomeomorph n x, hx⟩, ?_⟩
    apply (nativeSimplexHomeomorph n).injective
    rw [he, Homeomorph.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.nativeSimplexHomeomorph_mem_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.nativeSimplexHomeomorph_mem_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.nativeSimplexHomeomorph_mem_boundary ``Submission.DifferentialGeometry.SSet.nativeSimplexHomeomorph_mem_boundary


theorem isClosedEmbedding_toTop_boundaryι (n : ℕ) :
    _root_.Topology.IsClosedEmbedding (_root_.SSet.toTop.map (_root_.SSet.boundary n :
      (Δ[n] : _root_.SSet.{u}).Subcomplex).ι) := by
  have heq : (fun a ↦ (nativeSimplexHomeomorph n).symm (nativeBoundaryHomeomorph n a).val) =
      (_root_.SSet.toTop.map (_root_.SSet.boundary n : (Δ[n] : _root_.SSet.{u}).Subcomplex).ι) := by
    funext a
    apply (nativeSimplexHomeomorph n).injective
    rw [Homeomorph.apply_symm_apply]
    exact (ConcreteCategory.congr_hom (nativeBoundaryHomeomorph_inclusion n) a).symm
  rw [← heq]
  exact (nativeSimplexHomeomorph n).symm.isClosedEmbedding.comp
    (DifferentialGeometry.Simplex.isClosed_boundary.isClosedEmbedding_subtypeVal.comp
      (nativeBoundaryHomeomorph n).isClosedEmbedding)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.isClosedEmbedding_toTop_boundaryι then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.isClosedEmbedding_toTop_boundaryι"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.isClosedEmbedding_toTop_boundaryι ``Submission.DifferentialGeometry.SSet.isClosedEmbedding_toTop_boundaryι

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

def nativeSimplexRelativeChainIso (n : ℕ) :
    DifferentialGeometry.Homology.relativeChainComplex (_root_.SSet.toTop.obj (Δ[n] : _root_.SSet.{u}))
        (Set.range (_root_.SSet.toTop.map (_root_.SSet.boundary n).ι)) R ≅
      DifferentialGeometry.Homology.relativeChainComplex
        (TopCat.of (stdSimplex ℝ (ULift.{u} (Fin (n + 1)))))
        (DifferentialGeometry.Simplex.boundary (ULift.{u} (Fin (n + 1)))) R :=
  DifferentialGeometry.Homology.relativeChainIso R (nativeSimplexHomeomorph n)
    (nativeSimplexHomeomorph_mem_boundary n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.nativeSimplexRelativeChainIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.nativeSimplexRelativeChainIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.nativeSimplexRelativeChainIso ``Submission.DifferentialGeometry.SSet.nativeSimplexRelativeChainIso

variable {n : ℕ} {X Y : _root_.SSet.{u}}
  (g : (_root_.SSet.boundary n : _root_.SSet.{u}) ⟶ X) (r : Δ[n] ⟶ Y)


def nativeAttachingMap :
    TopCat.of (DifferentialGeometry.Simplex.boundary (ULift.{u} (Fin (n + 1)))) ⟶ _root_.SSet.toTop.obj X :=
  (TopCat.isoOfHomeo (nativeBoundaryHomeomorph n)).inv ≫ _root_.SSet.toTop.map g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.nativeAttachingMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.nativeAttachingMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.nativeAttachingMap ``Submission.DifferentialGeometry.SSet.nativeAttachingMap


def nativeCellMap :
    TopCat.of (stdSimplex ℝ (ULift.{u} (Fin (n + 1)))) ⟶ _root_.SSet.toTop.obj Y :=
  (TopCat.isoOfHomeo (nativeSimplexHomeomorph n)).inv ≫ _root_.SSet.toTop.map r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.nativeCellMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.nativeCellMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.nativeCellMap ``Submission.DifferentialGeometry.SSet.nativeCellMap

@[reassoc]
theorem nativeSimplexHomeomorph_nativeCellMap :
    (TopCat.isoOfHomeo (nativeSimplexHomeomorph n)).hom ≫ nativeCellMap r =
      _root_.SSet.toTop.map r := by
  apply ConcreteCategory.hom_ext
  intro x
  change (_root_.SSet.toTop.map r)
    ((nativeSimplexHomeomorph n).symm (nativeSimplexHomeomorph n x)) = _
  rw [Homeomorph.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.nativeSimplexHomeomorph_nativeCellMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.nativeSimplexHomeomorph_nativeCellMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.nativeSimplexHomeomorph_nativeCellMap ``Submission.DifferentialGeometry.SSet.nativeSimplexHomeomorph_nativeCellMap

variable {g r} {b : X ⟶ Y} (h : IsPushout (_root_.SSet.boundary n).ι g r b)

include h

theorem nativeAttachment_isPushout :
    _root_.CategoryTheory.IsPushout DifferentialGeometry.Simplex.Attachment.boundaryι (nativeAttachingMap g)
      (nativeCellMap r) (_root_.SSet.toTop.map b) := by
  apply (h.map _root_.SSet.toTop).of_iso
    (TopCat.isoOfHomeo (nativeBoundaryHomeomorph n))
    (TopCat.isoOfHomeo (nativeSimplexHomeomorph n)) (Iso.refl _) (Iso.refl _)
  · exact nativeBoundaryHomeomorph_inclusion n
  · apply ConcreteCategory.hom_ext
    intro x
    change (_root_.SSet.toTop.map g) x = (_root_.SSet.toTop.map g)
      ((nativeBoundaryHomeomorph n).symm (nativeBoundaryHomeomorph n x))
    rw [Homeomorph.symm_apply_apply]
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (nativeSimplexHomeomorph_nativeCellMap r).symm
  · simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.nativeAttachment_isPushout then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.nativeAttachment_isPushout"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.nativeAttachment_isPushout ``Submission.DifferentialGeometry.SSet.nativeAttachment_isPushout

theorem isClosedEmbedding_toTop_attachment : _root_.Topology.IsClosedEmbedding (_root_.SSet.toTop.map b) :=
  DifferentialGeometry.TopCat.Pushout.isClosedEmbedding_inr (nativeAttachment_isPushout h)
    DifferentialGeometry.Simplex.Attachment.isClosedEmbedding_boundaryι

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.isClosedEmbedding_toTop_attachment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.isClosedEmbedding_toTop_attachment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.isClosedEmbedding_toTop_attachment ``Submission.DifferentialGeometry.SSet.isClosedEmbedding_toTop_attachment


theorem realizedCell_mapsTo_range :
    Set.MapsTo (_root_.SSet.toTop.map r)
      (Set.range (_root_.SSet.toTop.map (_root_.SSet.boundary n).ι))
      (Set.range (_root_.SSet.toTop.map b)) := by
  rintro x ⟨a, rfl⟩
  exact ⟨(_root_.SSet.toTop.map g) a,
    (ConcreteCategory.congr_hom (h.map _root_.SSet.toTop).w a).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.realizedCell_mapsTo_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.realizedCell_mapsTo_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.realizedCell_mapsTo_range ``Submission.DifferentialGeometry.SSet.realizedCell_mapsTo_range


def realizedCellRelativeChainMap :
    DifferentialGeometry.Homology.relativeChainComplex (_root_.SSet.toTop.obj (Δ[n] : _root_.SSet.{u}))
        (Set.range (_root_.SSet.toTop.map (_root_.SSet.boundary n).ι)) R ⟶
      DifferentialGeometry.Homology.relativeChainComplex (_root_.SSet.toTop.obj Y)
        (Set.range (_root_.SSet.toTop.map b)) R :=
  DifferentialGeometry.Homology.relativeChainMap R (_root_.SSet.toTop.map r) (realizedCell_mapsTo_range h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.realizedCellRelativeChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.realizedCellRelativeChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.realizedCellRelativeChainMap ``Submission.DifferentialGeometry.SSet.realizedCellRelativeChainMap

theorem nativeSimplexRelativeChainIso_cellMap :
    (nativeSimplexRelativeChainIso R n).hom ≫
        DifferentialGeometry.Simplex.Attachment.cellRelativeChainMap R (nativeAttachment_isPushout h) =
      realizedCellRelativeChainMap R h := by
  change DifferentialGeometry.Homology.relativeChainMap R
      (TopCat.isoOfHomeo (nativeSimplexHomeomorph n)).hom
      (fun x hx ↦ (nativeSimplexHomeomorph_mem_boundary n x).mp hx) ≫
        DifferentialGeometry.Homology.relativeChainMap R (nativeCellMap r)
          (DifferentialGeometry.Simplex.Attachment.mapsTo_boundary_range_inr (nativeAttachment_isPushout h)) =
    DifferentialGeometry.Homology.relativeChainMap R (_root_.SSet.toTop.map r) (realizedCell_mapsTo_range h)
  erw [← DifferentialGeometry.Homology.relativeChainMap_comp]
  exact DifferentialGeometry.Homology.relativeChainMap_congr R _ _ (nativeSimplexHomeomorph_nativeCellMap r)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.nativeSimplexRelativeChainIso_cellMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.nativeSimplexRelativeChainIso_cellMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.nativeSimplexRelativeChainIso_cellMap ``Submission.DifferentialGeometry.SSet.nativeSimplexRelativeChainIso_cellMap

theorem quasiIso_realizedCellRelativeChainMap : QuasiIso (realizedCellRelativeChainMap R h) := by
  rw [← nativeSimplexRelativeChainIso_cellMap]
  have : QuasiIso (DifferentialGeometry.Simplex.Attachment.cellRelativeChainMap R
      (nativeAttachment_isPushout h)) :=
    DifferentialGeometry.Simplex.Attachment.quasiIso_cellRelativeChainMap R (nativeAttachment_isPushout h)
  exact quasiIso_comp _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.quasiIso_realizedCellRelativeChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.quasiIso_realizedCellRelativeChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.quasiIso_realizedCellRelativeChainMap ``Submission.DifferentialGeometry.SSet.quasiIso_realizedCellRelativeChainMap

@[reassoc (attr := simp)]
theorem relativeProjection_realizedCellRelativeChainMap :
    DifferentialGeometry.Homology.relativeProjection (_root_.SSet.toTop.obj (Δ[n] : _root_.SSet.{u}))
        (Set.range (_root_.SSet.toTop.map (_root_.SSet.boundary n).ι)) R ≫
          realizedCellRelativeChainMap R h =
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map
          (_root_.SSet.toTop.map r) ≫
        DifferentialGeometry.Homology.relativeProjection (_root_.SSet.toTop.obj Y)
          (Set.range (_root_.SSet.toTop.map b)) R :=
  DifferentialGeometry.Homology.relativeProjection_chainMap R _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.relativeProjection_realizedCellRelativeChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.relativeProjection_realizedCellRelativeChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.relativeProjection_realizedCellRelativeChainMap ``Submission.DifferentialGeometry.SSet.relativeProjection_realizedCellRelativeChainMap

end DifferentialGeometry.SSet
