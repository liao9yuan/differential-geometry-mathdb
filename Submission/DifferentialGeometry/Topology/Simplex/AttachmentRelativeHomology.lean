import Submission.DifferentialGeometry.Topology.Simplex.Attachment
import Submission.DifferentialGeometry.Topology.Simplex.RelativeHomology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Topology _root_.AlgebraicTopology

universe u

namespace DifferentialGeometry.Simplex.Attachment

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

private def singularChainHomotopyEquiv {Y Z : TopCat.{u}}
    (e : ContinuousMap.HomotopyEquiv Y Z) :
    HomotopyEquiv
      (((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj Y)
      (((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj Z) := by
  let F := (_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R
  refine {
    hom := F.map (TopCat.ofHom e.toFun)
    inv := F.map (TopCat.ofHom e.invFun)
    homotopyHomInvId := ?_
    homotopyInvHomId := ?_ }
  · have H : TopCat.Homotopy (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 Y) :=
      e.left_inv.some
    have hh := H.singularChainComplexFunctorObjMap R
    rwa [F.map_comp, F.map_id] at hh
  · have H : TopCat.Homotopy (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 Z) :=
      e.right_inv.some
    have hh := H.singularChainComplexFunctorObjMap R
    rwa [F.map_comp, F.map_id] at hh

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.Attachment.singularChainHomotopyEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.Attachment.singularChainHomotopyEquiv target :: scope.openDecls } }

private theorem quasiIso_relativeChainMap_openEmbedding {Y Z : TopCat.{u}}
    (j : Y ⟶ Z) (hj : _root_.Topology.IsOpenEmbedding j) (s : Set Y) (t : Set Z)
    (he : ∀ x, x ∈ s ↔ j x ∈ t) (ht : IsOpen t) (hcover : Set.range j ∪ t = Set.univ) :
    QuasiIso (DifferentialGeometry.Homology.relativeChainMap R j (fun x hx ↦ (he x).mp hx)) := by
  let e := hj.isEmbedding.toHomeomorph
  let q := DifferentialGeometry.Homology.relativeChainIso (X := Y) (Y := TopCat.of (Set.range j))
    (s := s) (t := {x : Set.range j | x.val ∈ t}) R e (fun x ↦ he x)
  let i : TopCat.of (Set.range j) ⟶ Z :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let q' := DifferentialGeometry.Homology.relativeChainMap R i
    (show Set.MapsTo i {x : Set.range j | x.val ∈ t} t from fun _ hx ↦ hx)
  have : QuasiIso q' := DifferentialGeometry.Homology.quasiIso_relativeChainMap_of_openCover
    Z (Set.range j) t R hj.isOpen_range ht hcover
  have heq : DifferentialGeometry.Homology.relativeChainMap R j (fun x hx ↦ (he x).mp hx) = q.hom ≫ q' := by
    exact DifferentialGeometry.Homology.relativeChainMap_comp R
      (TopCat.ofHom (⟨e, e.continuous⟩ : C(Y, Set.range j)))
      (fun x hx ↦ (he x).mp hx) i (fun _ hx ↦ hx)
  rw [heq]
  exact quasiIso_comp _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.Attachment.quasiIso_relativeChainMap_openEmbedding
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.Attachment.quasiIso_relativeChainMap_openEmbedding target :: scope.openDecls } }

variable {I : Type u} [Fintype I] [Nonempty I]
  {X P : TopCat.{u}} {g : TopCat.of (boundary I) ⟶ X}
  {r : TopCat.of (stdSimplex ℝ I) ⟶ P} {b : X ⟶ P}
  (h : IsPushout boundaryι g r b)

include h

omit [Nonempty I] in
theorem mapsTo_boundary_range_inr : Set.MapsTo r (boundary I) (Set.range b) := by
  intro d hd
  exact ⟨g ⟨d, hd⟩, (ConcreteCategory.congr_hom h.w ⟨d, hd⟩).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.mapsTo_boundary_range_inr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.mapsTo_boundary_range_inr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.mapsTo_boundary_range_inr ``Submission.DifferentialGeometry.Simplex.Attachment.mapsTo_boundary_range_inr


def cellRelativeChainMap :
    DifferentialGeometry.Homology.relativeChainComplex (TopCat.of (stdSimplex ℝ I)) (boundary I) R ⟶
      DifferentialGeometry.Homology.relativeChainComplex P (Set.range b) R :=
  DifferentialGeometry.Homology.relativeChainMap R r (mapsTo_boundary_range_inr h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.cellRelativeChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.cellRelativeChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.cellRelativeChainMap ``Submission.DifferentialGeometry.Simplex.Attachment.cellRelativeChainMap


def openCellMap : TopCat.of (openCell I) ⟶ P :=
  TopCat.ofHom ⟨fun d ↦ r d.val, r.hom.continuous.comp continuous_subtype_val⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.openCellMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.openCellMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.openCellMap ``Submission.DifferentialGeometry.Simplex.Attachment.openCellMap

omit h [Nonempty I] in
private theorem range_boundaryι : Set.range (boundaryι (I := I)) = boundary I := by
  ext d
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro hd
    exact ⟨⟨d, hd⟩, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Simplex.Attachment.range_boundaryι
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Simplex.Attachment.range_boundaryι target :: scope.openDecls } }

omit [Nonempty I] in
theorem isOpenEmbedding_openCellMap : _root_.Topology.IsOpenEmbedding (openCellMap (r := r)) := by
  let e : openCell I ≃ₜ {d : stdSimplex ℝ I // d ∉ Set.range (boundaryι (I := I))} :=
    Homeomorph.setCongr (by rw [range_boundaryι, openCell_eq_compl_boundary]; rfl)
  exact (DifferentialGeometry.TopCat.Pushout.isOpenEmbedding_inlComplement h
    isClosedEmbedding_boundaryι).comp e.isOpenEmbedding

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.isOpenEmbedding_openCellMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.isOpenEmbedding_openCellMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.isOpenEmbedding_openCellMap ``Submission.DifferentialGeometry.Simplex.Attachment.isOpenEmbedding_openCellMap

omit h in
theorem openCellMap_range_union_neighborhood :
    Set.range (openCellMap (r := r)) ∪ puncturedNeighborhood (r := r) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  by_cases hp : p = r stdSimplex.barycenter
  · exact Or.inl ⟨⟨stdSimplex.barycenter, barycenter_mem_openCell⟩, hp.symm⟩
  · exact Or.inr hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.openCellMap_range_union_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.openCellMap_range_union_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.openCellMap_range_union_neighborhood ``Submission.DifferentialGeometry.Simplex.Attachment.openCellMap_range_union_neighborhood


theorem mapsTo_punctured_neighborhood :
    Set.MapsTo r (punctured I) (puncturedNeighborhood (r := r)) := by
  intro d hd he
  exact hd ((inl_eq_barycenter_iff h d).mp he)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.mapsTo_punctured_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.mapsTo_punctured_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.mapsTo_punctured_neighborhood ``Submission.DifferentialGeometry.Simplex.Attachment.mapsTo_punctured_neighborhood


def puncturedCellRelativeChainMap :
    DifferentialGeometry.Homology.relativeChainComplex (TopCat.of (stdSimplex ℝ I)) (punctured I) R ⟶
      DifferentialGeometry.Homology.relativeChainComplex P (puncturedNeighborhood (r := r)) R :=
  DifferentialGeometry.Homology.relativeChainMap R r (mapsTo_punctured_neighborhood h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.puncturedCellRelativeChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.puncturedCellRelativeChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.puncturedCellRelativeChainMap ``Submission.DifferentialGeometry.Simplex.Attachment.puncturedCellRelativeChainMap


theorem quasiIso_puncturedCellRelativeChainMap :
    QuasiIso (puncturedCellRelativeChainMap R h) := by
  let j : TopCat.of (openCell I) ⟶ TopCat.of (stdSimplex ℝ I) :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hlocal : ∀ d : openCell I, d.val ∈ punctured I ↔
      openCellMap (r := r) d ∈ puncturedNeighborhood (r := r) :=
    fun d ↦ (not_congr (inl_eq_barycenter_iff h d.val)).symm
  have hq := quasiIso_relativeChainMap_openEmbedding R (openCellMap (r := r))
    (isOpenEmbedding_openCellMap h) {d : openCell I | d.val ∈ punctured I}
    (puncturedNeighborhood (r := r)) hlocal (isOpen_puncturedNeighborhood h)
    openCellMap_range_union_neighborhood
  have heq : openCellExcisionChainMap (I := I) R ≫ puncturedCellRelativeChainMap R h =
      DifferentialGeometry.Homology.relativeChainMap R (openCellMap (r := r))
        (fun d hd ↦ (hlocal d).mp hd) :=
    (DifferentialGeometry.Homology.relativeChainMap_comp R j (fun _ hx ↦ hx) r
      (mapsTo_punctured_neighborhood h)).symm
  have : QuasiIso (openCellExcisionChainMap (I := I) R) := quasiIso_openCellExcisionChainMap R
  have : QuasiIso (openCellExcisionChainMap (I := I) R ≫ puncturedCellRelativeChainMap R h) := by
    rw [heq]
    exact hq
  exact quasiIso_of_comp_left (openCellExcisionChainMap R) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.quasiIso_puncturedCellRelativeChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.quasiIso_puncturedCellRelativeChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.quasiIso_puncturedCellRelativeChainMap ``Submission.DifferentialGeometry.Simplex.Attachment.quasiIso_puncturedCellRelativeChainMap


theorem mapsTo_range_inr_neighborhood :
    Set.MapsTo (𝟙 P) (Set.range b) (puncturedNeighborhood (r := r)) := by
  rintro p ⟨x, rfl⟩
  exact inr_ne_barycenter h x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.mapsTo_range_inr_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.mapsTo_range_inr_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.mapsTo_range_inr_neighborhood ``Submission.DifferentialGeometry.Simplex.Attachment.mapsTo_range_inr_neighborhood

def neighborhoodRelativeChainMap :
    DifferentialGeometry.Homology.relativeChainComplex P (Set.range b) R ⟶
      DifferentialGeometry.Homology.relativeChainComplex P (puncturedNeighborhood (r := r)) R :=
  DifferentialGeometry.Homology.relativeChainMap R (𝟙 P) (mapsTo_range_inr_neighborhood h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.neighborhoodRelativeChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.neighborhoodRelativeChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.neighborhoodRelativeChainMap ``Submission.DifferentialGeometry.Simplex.Attachment.neighborhoodRelativeChainMap

theorem quasiIso_neighborhoodRelativeChainMap :
    QuasiIso (neighborhoodRelativeChainMap R h) := by
  let F := (_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R
  let a := DifferentialGeometry.Homology.relativeSubspaceMap (𝟙 P) (mapsTo_range_inr_neighborhood h)
  let e : X ≃ₜ Set.range b :=
    (DifferentialGeometry.TopCat.Pushout.isClosedEmbedding_inr h
      isClosedEmbedding_boundaryι).isEmbedding.toHomeomorph
  let i : X ⟶ TopCat.of (Set.range b) := (TopCat.isoOfHomeo e).hom
  have hia : i ≫ a = TopCat.ofHom (oldToNeighborhood h) := by
    ext x
    rfl
  have : _root_.CategoryTheory.IsIso i := by dsimp [i]; infer_instance
  have : QuasiIso (F.map i ≫ F.map a) := by
    rw [← F.map_comp, hia]
    exact (singularChainHomotopyEquiv (Y := TopCat.of (puncturedNeighborhood (r := r)))
      (Z := X) R (neighborhoodHomotopyEquiv h)).quasiIso_inv
  have ha : QuasiIso (F.map a) := quasiIso_of_comp_left (F.map i) (F.map a)
  unfold neighborhoodRelativeChainMap DifferentialGeometry.Homology.relativeChainMap
  exact DifferentialGeometry.HomologicalComplex.quasiIso_cokernel_map _ _ _ _ _ ha (quasiIso_of_isIso _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.quasiIso_neighborhoodRelativeChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.quasiIso_neighborhoodRelativeChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.quasiIso_neighborhoodRelativeChainMap ``Submission.DifferentialGeometry.Simplex.Attachment.quasiIso_neighborhoodRelativeChainMap


theorem cellRelativeChainMap_neighborhood :
    cellRelativeChainMap R h ≫ neighborhoodRelativeChainMap R h =
      boundaryToPuncturedChainMap R ≫ puncturedCellRelativeChainMap R h := by
  unfold cellRelativeChainMap neighborhoodRelativeChainMap boundaryToPuncturedChainMap
    puncturedCellRelativeChainMap
  erw [← DifferentialGeometry.Homology.relativeChainMap_comp, ← DifferentialGeometry.Homology.relativeChainMap_comp]
  exact DifferentialGeometry.Homology.relativeChainMap_congr R _ _ (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.cellRelativeChainMap_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.cellRelativeChainMap_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.cellRelativeChainMap_neighborhood ``Submission.DifferentialGeometry.Simplex.Attachment.cellRelativeChainMap_neighborhood

theorem quasiIso_cellRelativeChainMap : QuasiIso (cellRelativeChainMap R h) := by
  have : QuasiIso (neighborhoodRelativeChainMap R h) := quasiIso_neighborhoodRelativeChainMap R h
  have : QuasiIso (cellRelativeChainMap R h ≫ neighborhoodRelativeChainMap R h) := by
    rw [cellRelativeChainMap_neighborhood]
    have : QuasiIso (boundaryToPuncturedChainMap (I := I) R) :=
      quasiIso_boundaryToPuncturedChainMap R
    have : QuasiIso (puncturedCellRelativeChainMap R h) := quasiIso_puncturedCellRelativeChainMap R h
    infer_instance
  exact quasiIso_of_comp_right (cellRelativeChainMap R h) (neighborhoodRelativeChainMap R h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.quasiIso_cellRelativeChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.quasiIso_cellRelativeChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.quasiIso_cellRelativeChainMap ``Submission.DifferentialGeometry.Simplex.Attachment.quasiIso_cellRelativeChainMap

omit [Nonempty I] in
@[reassoc (attr := simp)]
theorem relativeProjection_cellRelativeChainMap :
    DifferentialGeometry.Homology.relativeProjection (TopCat.of (stdSimplex ℝ I)) (boundary I) R ≫
        cellRelativeChainMap R h =
      ((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map r ≫
        DifferentialGeometry.Homology.relativeProjection P (Set.range b) R :=
  DifferentialGeometry.Homology.relativeProjection_chainMap R r (mapsTo_boundary_range_inr h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.relativeProjection_cellRelativeChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.relativeProjection_cellRelativeChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.relativeProjection_cellRelativeChainMap ``Submission.DifferentialGeometry.Simplex.Attachment.relativeProjection_cellRelativeChainMap

def cellRelativeHomologyIso (n : ℕ) :
    DifferentialGeometry.Homology.relativeHomology (TopCat.of (stdSimplex ℝ I)) (boundary I) R n ≅
      DifferentialGeometry.Homology.relativeHomology P (Set.range b) R n := by
  have : QuasiIso (cellRelativeChainMap R h) := quasiIso_cellRelativeChainMap R h
  exact isoOfQuasiIsoAt (cellRelativeChainMap R h) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.cellRelativeHomologyIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.cellRelativeHomologyIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.cellRelativeHomologyIso ``Submission.DifferentialGeometry.Simplex.Attachment.cellRelativeHomologyIso


@[simp]
theorem cellRelativeHomologyIso_hom (n : ℕ) :
    (cellRelativeHomologyIso R h n).hom =
      _root_.HomologicalComplex.homologyMap (cellRelativeChainMap R h) n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.Attachment.cellRelativeHomologyIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.Attachment.cellRelativeHomologyIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.Attachment.cellRelativeHomologyIso_hom ``Submission.DifferentialGeometry.Simplex.Attachment.cellRelativeHomologyIso_hom

end DifferentialGeometry.Simplex.Attachment
