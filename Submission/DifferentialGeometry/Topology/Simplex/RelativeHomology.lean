import Submission.DifferentialGeometry.Topology.Simplex.BoundaryRetraction
import Submission.DifferentialGeometry.Topology.Homology.Relative.Excision
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology

universe u

namespace DifferentialGeometry.Simplex

variable {I : Type u} [Fintype I] [Nonempty I]
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)

def boundaryInclusionChainHomotopyEquiv :
    HomotopyEquiv
      (((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj
        (TopCat.of (boundary I)))
      (((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj
        (TopCat.of (punctured I))) := by
  let F := (_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R
  let e := (radialHomotopyEquiv (I := I)).symm
  refine {
    hom := F.map (TopCat.ofHom boundaryInclusion)
    inv := F.map (TopCat.ofHom radialRetraction)
    homotopyHomInvId := ?_
    homotopyInvHomId := ?_ }
  · have H : TopCat.Homotopy
        (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 (TopCat.of (boundary I))) :=
      e.left_inv.some
    have h := H.singularChainComplexFunctorObjMap R
    rwa [F.map_comp, F.map_id] at h
  · have H : TopCat.Homotopy
        (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 (TopCat.of (punctured I))) :=
      e.right_inv.some
    have h := H.singularChainComplexFunctorObjMap R
    rwa [F.map_comp, F.map_id] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.boundaryInclusionChainHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.boundaryInclusionChainHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.boundaryInclusionChainHomotopyEquiv ``Submission.DifferentialGeometry.Simplex.boundaryInclusionChainHomotopyEquiv

def boundaryToPuncturedChainMap :
    DifferentialGeometry.Homology.relativeChainComplex (TopCat.of (stdSimplex ℝ I)) (boundary I) R ⟶
      DifferentialGeometry.Homology.relativeChainComplex (TopCat.of (stdSimplex ℝ I)) (punctured I) R :=
  DifferentialGeometry.Homology.relativeChainMap R (𝟙 (TopCat.of (stdSimplex ℝ I)))
    (fun _ hx ↦ boundary_subset_punctured hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.boundaryToPuncturedChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.boundaryToPuncturedChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.boundaryToPuncturedChainMap ``Submission.DifferentialGeometry.Simplex.boundaryToPuncturedChainMap


@[reassoc (attr := simp)]
theorem relativeProjection_boundaryToPuncturedChainMap :
    DifferentialGeometry.Homology.relativeProjection (TopCat.of (stdSimplex ℝ I)) (boundary I) R ≫
        boundaryToPuncturedChainMap R =
      DifferentialGeometry.Homology.relativeProjection (TopCat.of (stdSimplex ℝ I)) (punctured I) R := by
  have h := DifferentialGeometry.Homology.relativeProjection_chainMap R (𝟙 (TopCat.of (stdSimplex ℝ I)))
      (show Set.MapsTo (𝟙 (TopCat.of (stdSimplex ℝ I))) (boundary I) (punctured I) from
        fun _ hx ↦ boundary_subset_punctured hx)
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.relativeProjection_boundaryToPuncturedChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.relativeProjection_boundaryToPuncturedChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.relativeProjection_boundaryToPuncturedChainMap ``Submission.DifferentialGeometry.Simplex.relativeProjection_boundaryToPuncturedChainMap

theorem quasiIso_boundaryToPuncturedChainMap :
    QuasiIso (boundaryToPuncturedChainMap (I := I) R) := by
  unfold boundaryToPuncturedChainMap DifferentialGeometry.Homology.relativeChainMap
  exact DifferentialGeometry.HomologicalComplex.quasiIso_cokernel_map _ _ _ _ _
    (boundaryInclusionChainHomotopyEquiv (I := I) R).quasiIso_hom
    (quasiIso_of_isIso _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.quasiIso_boundaryToPuncturedChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.quasiIso_boundaryToPuncturedChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.quasiIso_boundaryToPuncturedChainMap ``Submission.DifferentialGeometry.Simplex.quasiIso_boundaryToPuncturedChainMap

def boundaryToPuncturedHomologyIso (n : ℕ) :
    DifferentialGeometry.Homology.relativeHomology (TopCat.of (stdSimplex ℝ I)) (boundary I) R n ≅
      DifferentialGeometry.Homology.relativeHomology (TopCat.of (stdSimplex ℝ I)) (punctured I) R n := by
  letI := quasiIso_boundaryToPuncturedChainMap (I := I) R
  exact isoOfQuasiIsoAt (boundaryToPuncturedChainMap R) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.boundaryToPuncturedHomologyIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.boundaryToPuncturedHomologyIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.boundaryToPuncturedHomologyIso ``Submission.DifferentialGeometry.Simplex.boundaryToPuncturedHomologyIso


@[simp]
theorem boundaryToPuncturedHomologyIso_hom (n : ℕ) :
    (boundaryToPuncturedHomologyIso (I := I) R n).hom =
      _root_.HomologicalComplex.homologyMap (boundaryToPuncturedChainMap R) n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.boundaryToPuncturedHomologyIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.boundaryToPuncturedHomologyIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.boundaryToPuncturedHomologyIso_hom ``Submission.DifferentialGeometry.Simplex.boundaryToPuncturedHomologyIso_hom

def openCell (I : Type*) [Fintype I] : Set (stdSimplex ℝ I) :=
  {x | ∀ i, 0 < x.val i}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.openCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.openCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.openCell ``Submission.DifferentialGeometry.Simplex.openCell

omit [Nonempty I] in
theorem isOpen_openCell : IsOpen (openCell I) := by
  change IsOpen (Set.ofPred (fun x : stdSimplex ℝ I ↦ ∀ i, 0 < x.val i))
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite (fun i ↦
    isOpen_lt continuous_const ((continuous_apply i).comp continuous_subtype_val))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.isOpen_openCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.isOpen_openCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.isOpen_openCell ``Submission.DifferentialGeometry.Simplex.isOpen_openCell

omit [Nonempty I] in
theorem openCell_eq_compl_boundary : openCell I = (boundary I)ᶜ := by
  ext x
  change (∀ i, 0 < x.val i) ↔ ¬ ∃ i, x.val i = 0
  constructor
  · rintro hx ⟨i, hi⟩
    exact (ne_of_gt (hx i)) hi
  · intro hx i
    exact lt_of_le_of_ne (x.property.1 i) (Ne.symm (fun hi ↦ hx ⟨i, hi⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.openCell_eq_compl_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.openCell_eq_compl_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.openCell_eq_compl_boundary ``Submission.DifferentialGeometry.Simplex.openCell_eq_compl_boundary


theorem barycenter_mem_openCell : stdSimplex.barycenter ∈ openCell I := by
  intro i
  exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.barycenter_mem_openCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.barycenter_mem_openCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.barycenter_mem_openCell ``Submission.DifferentialGeometry.Simplex.barycenter_mem_openCell


theorem openCell_union_punctured : openCell I ∪ punctured I = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases h : x = stdSimplex.barycenter
  · exact Or.inl (h ▸ barycenter_mem_openCell)
  · exact Or.inr h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.openCell_union_punctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.openCell_union_punctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.openCell_union_punctured ``Submission.DifferentialGeometry.Simplex.openCell_union_punctured

def openCellExcisionChainMap :
    DifferentialGeometry.Homology.relativeChainComplex (TopCat.of (openCell I))
      {x : openCell I | x.val ∈ punctured I} R ⟶
      DifferentialGeometry.Homology.relativeChainComplex (TopCat.of (stdSimplex ℝ I)) (punctured I) R :=
  DifferentialGeometry.Homology.relativeChainMap R
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(openCell I, stdSimplex ℝ I)))
    (fun _ hx ↦ hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.openCellExcisionChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.openCellExcisionChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.openCellExcisionChainMap ``Submission.DifferentialGeometry.Simplex.openCellExcisionChainMap


@[reassoc (attr := simp)]
theorem relativeProjection_openCellExcisionChainMap :
    DifferentialGeometry.Homology.relativeProjection (TopCat.of (openCell I))
        {x : openCell I | x.val ∈ punctured I} R ≫ openCellExcisionChainMap R =
      DifferentialGeometry.Homology.relativeInclusion (TopCat.of (stdSimplex ℝ I)) (openCell I) R ≫
        DifferentialGeometry.Homology.relativeProjection (TopCat.of (stdSimplex ℝ I)) (punctured I) R :=
  DifferentialGeometry.Homology.relativeProjection_chainMap R _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.relativeProjection_openCellExcisionChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.relativeProjection_openCellExcisionChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.relativeProjection_openCellExcisionChainMap ``Submission.DifferentialGeometry.Simplex.relativeProjection_openCellExcisionChainMap


theorem quasiIso_openCellExcisionChainMap :
    QuasiIso (openCellExcisionChainMap (I := I) R) :=
  DifferentialGeometry.Homology.quasiIso_relativeChainMap_of_openCover
    (TopCat.of (stdSimplex ℝ I)) (openCell I) (punctured I) R
    isOpen_openCell isOpen_punctured openCell_union_punctured

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.quasiIso_openCellExcisionChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.quasiIso_openCellExcisionChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.quasiIso_openCellExcisionChainMap ``Submission.DifferentialGeometry.Simplex.quasiIso_openCellExcisionChainMap

def openCellRelativeHomologyIso (n : ℕ) :
    DifferentialGeometry.Homology.relativeHomology (TopCat.of (openCell I))
      {x : openCell I | x.val ∈ punctured I} R n ≅
      DifferentialGeometry.Homology.relativeHomology (TopCat.of (stdSimplex ℝ I)) (boundary I) R n :=
  DifferentialGeometry.Homology.relativeExcisionIso (TopCat.of (stdSimplex ℝ I))
    (openCell I) (punctured I) R isOpen_openCell isOpen_punctured openCell_union_punctured n ≪≫
      (boundaryToPuncturedHomologyIso R n).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.openCellRelativeHomologyIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.openCellRelativeHomologyIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.openCellRelativeHomologyIso ``Submission.DifferentialGeometry.Simplex.openCellRelativeHomologyIso

@[reassoc]
theorem openCellRelativeHomologyIso_hom_boundaryToPunctured (n : ℕ) :
    (openCellRelativeHomologyIso (I := I) R n).hom ≫
        _root_.HomologicalComplex.homologyMap (boundaryToPuncturedChainMap R) n =
      _root_.HomologicalComplex.homologyMap (openCellExcisionChainMap R) n := by
  change (_ ≫ (boundaryToPuncturedHomologyIso R n).inv) ≫
    (boundaryToPuncturedHomologyIso R n).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Simplex.openCellRelativeHomologyIso_hom_boundaryToPunctured then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Simplex.openCellRelativeHomologyIso_hom_boundaryToPunctured"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Simplex.openCellRelativeHomologyIso_hom_boundaryToPunctured ``Submission.DifferentialGeometry.Simplex.openCellRelativeHomologyIso_hom_boundaryToPunctured

end DifferentialGeometry.Simplex
