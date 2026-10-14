import Submission.DifferentialGeometry.Topology.SimplicialSet.BoundaryRealization
import Submission.DifferentialGeometry.Topology.Simplex.Face
import Mathlib.Topology.LocallyFinite

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.Opposite _root_.Simplicial

universe u

namespace DifferentialGeometry.SSet


def boundaryFaceMap {n : ℕ} (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)),
      _root_.SSet.toTop.obj (_root_.SSet.boundary (n + 1) : _root_.SSet.{u})) :=
  (_root_.SSet.toTop.map (_root_.SSet.boundary.ι i)).hom.comp
    ⟨(SimplexCategory.toTopHomeo ⦋n⦌).symm,
      (SimplexCategory.toTopHomeo ⦋n⦌).symm.continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.boundaryFaceMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.boundaryFaceMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.boundaryFaceMap ``Submission.DifferentialGeometry.SSet.boundaryFaceMap


theorem boundaryFaceMap_ambient {n : ℕ} (i : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 1))) :
    boundaryRealizationMap (n + 1) (boundaryFaceMap.{u} i p) =
      ULift.up (stdSimplex.map i.succAbove p) := by
  have h := ConcreteCategory.congr_hom (boundaryRealizationMap_face.{u} i)
    ((SimplexCategory.toTopHomeo ⦋n⦌).symm p)
  change boundaryRealizationMap (n + 1) (boundaryFaceMap i p) =
    (SimplexCategory.toTop.map (SimplexCategory.δ i)).hom
      ((_root_.SSet.toTopSimplex.hom.app ⦋n⦌).hom
        ((SimplexCategory.toTopHomeo ⦋n⦌).symm p)) at h
  have hp : (_root_.SSet.toTopSimplex.hom.app ⦋n⦌).hom
      ((SimplexCategory.toTopHomeo ⦋n⦌).symm p) = ULift.up p := by
    apply ULift.ext
    exact (SimplexCategory.toTopHomeo ⦋n⦌).apply_symm_apply p
  rw [hp] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.boundaryFaceMap_ambient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.boundaryFaceMap_ambient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.boundaryFaceMap_ambient ``Submission.DifferentialGeometry.SSet.boundaryFaceMap_ambient

private theorem boundary_face_overlap_morphism {n : ℕ}
    (i : Fin (n + 3)) (j : Fin (n + 2)) :
    _root_.SSet.stdSimplex.map (SimplexCategory.δ j) ≫ _root_.SSet.boundary.ι.{u} i =
      _root_.SSet.stdSimplex.map (SimplexCategory.δ (j.predAbove i)) ≫
        _root_.SSet.boundary.ι (i.succAbove j) := by
  apply (_root_.CategoryTheory.cancel_mono (_root_.SSet.boundary (n + 2)).ι).mp
  rw [Category.assoc, Category.assoc, _root_.SSet.boundary.ι_ι, _root_.SSet.boundary.ι_ι]
  change _root_.SSet.stdSimplex.map (SimplexCategory.δ j) ≫
      _root_.SSet.stdSimplex.map (SimplexCategory.δ i) =
    _root_.SSet.stdSimplex.map (SimplexCategory.δ (j.predAbove i)) ≫
      _root_.SSet.stdSimplex.map (SimplexCategory.δ (i.succAbove j))
  have hc : SimplexCategory.δ j ≫ SimplexCategory.δ i =
      SimplexCategory.δ (j.predAbove i) ≫ SimplexCategory.δ (i.succAbove j) := by
    ext k
    exact congrArg Fin.val (Fin.succAbove_succAbove_succAbove_predAbove i j k).symm
  exact (_root_.SSet.stdSimplex.map_comp _ _).symm.trans
    ((congrArg (fun f ↦ _root_.SSet.stdSimplex.map f) hc).trans
      (_root_.SSet.stdSimplex.map_comp _ _))

run_cmd do
  let target := ``Submission.DifferentialGeometry.SSet.boundary_face_overlap_morphism
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.SSet.boundary_face_overlap_morphism target :: scope.openDecls } }


theorem boundaryFaceMap_overlap {n : ℕ} (i : Fin (n + 3)) (j : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 1))) :
    boundaryFaceMap.{u} i (stdSimplex.map j.succAbove p) =
      boundaryFaceMap (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p) := by
  change (_root_.SSet.toTop.map (_root_.SSet.boundary.ι i)).hom
      ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm (stdSimplex.map j.succAbove p)) =
    (_root_.SSet.toTop.map (_root_.SSet.boundary.ι (i.succAbove j))).hom
      ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm
        (stdSimplex.map (j.predAbove i).succAbove p))
  have hl := SimplexCategory.toTopHomeo_symm_naturality_apply.{u} (SimplexCategory.δ j) p
  have hr := SimplexCategory.toTopHomeo_symm_naturality_apply.{u}
    (SimplexCategory.δ (j.predAbove i)) p
  change (SimplexCategory.toTopHomeo ⦋n + 1⦌).symm (stdSimplex.map j.succAbove p) = _ at hl
  change (SimplexCategory.toTopHomeo ⦋n + 1⦌).symm
    (stdSimplex.map (j.predAbove i).succAbove p) = _ at hr
  rw [hl, hr]
  have h := congrArg (fun f ↦ _root_.SSet.toTop.map f) (boundary_face_overlap_morphism.{u} i j)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h ((SimplexCategory.toTopHomeo ⦋n⦌).symm p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.boundaryFaceMap_overlap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.boundaryFaceMap_overlap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.boundaryFaceMap_overlap ``Submission.DifferentialGeometry.SSet.boundaryFaceMap_overlap

private theorem coordinate_faceDelete_map {n : ℕ} (i : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 2))) (hi : p.val i = 0) :
    stdSimplex.map i.succAbove (DifferentialGeometry.Simplex.faceDelete i ⟨p, hi⟩) = p :=
  congrArg Subtype.val (DifferentialGeometry.Simplex.faceInsert_faceDelete i ⟨p, hi⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.SSet.coordinate_faceDelete_map
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.SSet.coordinate_faceDelete_map target :: scope.openDecls } }


theorem boundaryFaceMap_delete_eq {n : ℕ} (i j : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 2))) (hi : p.val i = 0) (hj : p.val j = 0) :
    boundaryFaceMap.{u} i (DifferentialGeometry.Simplex.faceDelete i ⟨p, hi⟩) =
      boundaryFaceMap j (DifferentialGeometry.Simplex.faceDelete j ⟨p, hj⟩) := by
  by_cases hji : j = i
  · subst j
    rfl
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hji
  let q := DifferentialGeometry.Simplex.faceDelete i ⟨p, hi⟩
  have hq : q.val j = 0 := hj
  cases n with
  | zero =>
    have he : q.val j = 1 := by
      have hs := q.property.2
      change (∑ k : Fin 1, q.val k) = 1 at hs
      simpa only [Fin.sum_univ_one, Subsingleton.elim (0 : Fin 1) j] using hs
    exact False.elim (zero_ne_one (hq.symm.trans he))
  | succ n =>
    let z := DifferentialGeometry.Simplex.faceDelete j ⟨q, hq⟩
    have hz : stdSimplex.map j.succAbove z = q := coordinate_faceDelete_map j q hq
    have hother : DifferentialGeometry.Simplex.faceDelete (i.succAbove j) ⟨p, hj⟩ =
        stdSimplex.map (j.predAbove i).succAbove z := by
      apply (DifferentialGeometry.Simplex.faceHomeomorph (i.succAbove j)).injective
      apply Subtype.ext
      change stdSimplex.map (i.succAbove j).succAbove
        (DifferentialGeometry.Simplex.faceDelete (i.succAbove j) ⟨p, hj⟩) =
          stdSimplex.map (i.succAbove j).succAbove (stdSimplex.map (j.predAbove i).succAbove z)
      rw [coordinate_faceDelete_map]
      calc
        p = stdSimplex.map i.succAbove q := (coordinate_faceDelete_map i p hi).symm
        _ = stdSimplex.map i.succAbove (stdSimplex.map j.succAbove z) := congrArg _ hz.symm
        _ = _ := by
          rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
          congr 1
          funext k
          exact (Fin.succAbove_succAbove_succAbove_predAbove i j k).symm
    rw [hother]
    change boundaryFaceMap i q = _
    rw [← hz]
    exact boundaryFaceMap_overlap i j z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.boundaryFaceMap_delete_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.boundaryFaceMap_delete_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.boundaryFaceMap_delete_eq ``Submission.DifferentialGeometry.SSet.boundaryFaceMap_delete_eq

instance isEmpty_simplexBoundarySet_zero : IsEmpty (simplexBoundarySet.{u} 0) :=
  ⟨fun p ↦ by
    obtain ⟨i, hi⟩ := p.property
    have hs := p.val.down.property.2
    change (∑ j : Fin 1, p.val.down.val j) = 1 at hs
    have he : p.val.down.val i = 1 := by
      simpa only [Fin.sum_univ_one, Subsingleton.elim (0 : Fin 1) i] using hs
    exact zero_ne_one (hi.symm.trans he)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.isEmpty_simplexBoundarySet_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.isEmpty_simplexBoundarySet_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.isEmpty_simplexBoundarySet_zero ``Submission.DifferentialGeometry.SSet.isEmpty_simplexBoundarySet_zero

instance isEmpty_realization_boundary_zero :
    IsEmpty (_root_.SSet.toTop.obj (_root_.SSet.boundary 0 : _root_.SSet.{u})) :=
  ⟨fun x ↦ isEmptyElim (boundaryRealizationLift 0 x)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.isEmpty_realization_boundary_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.isEmpty_realization_boundary_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.isEmpty_realization_boundary_zero ``Submission.DifferentialGeometry.SSet.isEmpty_realization_boundary_zero

private def boundaryInverseSuccPoint (n : ℕ) (p : simplexBoundarySet.{u} (n + 1)) :
    _root_.SSet.toTop.obj (_root_.SSet.boundary (n + 1) : _root_.SSet.{u}) :=
  boundaryFaceMap p.property.choose
    (DifferentialGeometry.Simplex.faceDelete p.property.choose ⟨p.val.down, p.property.choose_spec⟩)

run_cmd do
  let target := ``Submission.DifferentialGeometry.SSet.boundaryInverseSuccPoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.SSet.boundaryInverseSuccPoint target :: scope.openDecls } }

private theorem boundaryInverseSuccPoint_face (n : ℕ) (p : simplexBoundarySet.{u} (n + 1))
    (i : Fin (n + 2)) (hi : p.val.down.val i = 0) :
    boundaryInverseSuccPoint n p = boundaryFaceMap i (DifferentialGeometry.Simplex.faceDelete i ⟨p.val.down, hi⟩) :=
  boundaryFaceMap_delete_eq _ _ _ _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.SSet.boundaryInverseSuccPoint_face
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.SSet.boundaryInverseSuccPoint_face target :: scope.openDecls } }

private theorem continuous_boundaryInverseSuccPoint (n : ℕ) :
    Continuous (boundaryInverseSuccPoint.{u} n) := by
  let F (i : Fin (n + 2)) : Set (simplexBoundarySet.{u} (n + 1)) :=
    {p | p.val.down.val i = 0}
  have hcover : ⋃ i, F i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    exact Set.mem_iUnion.mpr p.property
  have hclosed (i : Fin (n + 2)) : IsClosed (F i) := by
    have hc : Continuous (fun p : simplexBoundarySet.{u} (n + 1) ↦ p.val.down.val i) := by
      have hv : Continuous (fun p : simplexBoundarySet.{u} (n + 1) ↦
          (p.val.down : stdSimplex ℝ (Fin (n + 2)))) := by fun_prop
      exact (continuous_apply i).comp (continuous_subtype_val.comp hv)
    exact isClosed_eq hc continuous_const
  apply (locallyFinite_of_finite F).continuous hcover hclosed
  intro i
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (fun p : F i ↦ boundaryInverseSuccPoint n p.val) =
      fun p : F i ↦ boundaryFaceMap i
        (DifferentialGeometry.Simplex.faceDelete i ⟨p.val.val.down, p.property⟩) := by
    funext p
    exact boundaryInverseSuccPoint_face n p.val i p.property
  change Continuous (fun p : F i ↦ boundaryInverseSuccPoint n p.val)
  rw [he]
  apply (boundaryFaceMap i).continuous.comp
  apply (DifferentialGeometry.Simplex.faceDelete i).continuous.comp
  have hv : Continuous (fun p : F i ↦ (p.val.val.down : stdSimplex ℝ (Fin (n + 2)))) := by
    fun_prop
  exact hv.subtype_mk _

run_cmd do
  let target := ``Submission.DifferentialGeometry.SSet.continuous_boundaryInverseSuccPoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.SSet.continuous_boundaryInverseSuccPoint target :: scope.openDecls } }


def boundaryRealizationInverse (n : ℕ) :
    C(simplexBoundarySet.{u} n,
      _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet.{u})) :=
  match n with
  | 0 => ⟨fun p ↦ isEmptyElim p,
      continuous_iff_continuousAt.mpr (fun p ↦ isEmptyElim p)⟩
  | n + 1 => ⟨boundaryInverseSuccPoint n, continuous_boundaryInverseSuccPoint n⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.boundaryRealizationInverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.boundaryRealizationInverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.boundaryRealizationInverse ``Submission.DifferentialGeometry.SSet.boundaryRealizationInverse


theorem boundaryRealizationInverse_face {n : ℕ} (p : simplexBoundarySet.{u} (n + 1))
    (i : Fin (n + 2)) (hi : p.val.down.val i = 0) :
    boundaryRealizationInverse (n + 1) p =
      boundaryFaceMap i (DifferentialGeometry.Simplex.faceDelete i ⟨p.val.down, hi⟩) :=
  boundaryInverseSuccPoint_face n p i hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.boundaryRealizationInverse_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.boundaryRealizationInverse_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.boundaryRealizationInverse_face ``Submission.DifferentialGeometry.SSet.boundaryRealizationInverse_face


@[simp]
theorem boundaryRealizationLift_inverse (n : ℕ) (p : simplexBoundarySet.{u} n) :
    boundaryRealizationLift n (boundaryRealizationInverse n p) = p := by
  cases n with
  | zero => exact isEmptyElim p
  | succ n =>
    obtain ⟨i, hi⟩ := p.property
    rw [boundaryRealizationInverse_face p i hi]
    apply Subtype.ext
    have h := ConcreteCategory.congr_hom (boundaryRealizationLift_inclusion (n + 1))
      (boundaryFaceMap i (DifferentialGeometry.Simplex.faceDelete i ⟨p.val.down, hi⟩))
    refine h.trans ((boundaryFaceMap_ambient i _).trans ?_)
    exact congrArg ULift.up (coordinate_faceDelete_map i p.val.down hi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.boundaryRealizationLift_inverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.boundaryRealizationLift_inverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.boundaryRealizationLift_inverse ``Submission.DifferentialGeometry.SSet.boundaryRealizationLift_inverse


theorem boundaryRealizationInverse_boundaryFaceMap {n : ℕ} (i : Fin (n + 2))
    (q : stdSimplex ℝ (Fin (n + 1))) :
    boundaryRealizationInverse (n + 1)
        (boundaryRealizationLift (n + 1) (boundaryFaceMap.{u} i q)) = boundaryFaceMap i q := by
  let p := boundaryRealizationLift (n + 1) (boundaryFaceMap.{u} i q)
  have hp : p.val.down = stdSimplex.map i.succAbove q :=
    congrArg ULift.down ((ConcreteCategory.congr_hom
      (boundaryRealizationLift_inclusion (n + 1)) (boundaryFaceMap i q)).trans
        (boundaryFaceMap_ambient i q))
  have hpi : p.val.down.val i = 0 := hp ▸ DifferentialGeometry.Simplex.map_succAbove_apply_pivot i q
  rw [boundaryRealizationInverse_face p i hpi]
  have hface : (⟨p.val.down, hpi⟩ : DifferentialGeometry.Simplex.face i) = DifferentialGeometry.Simplex.faceInsert i q :=
    Subtype.ext hp
  rw [hface, DifferentialGeometry.Simplex.faceDelete_faceInsert]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.boundaryRealizationInverse_boundaryFaceMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.boundaryRealizationInverse_boundaryFaceMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.boundaryRealizationInverse_boundaryFaceMap ``Submission.DifferentialGeometry.SSet.boundaryRealizationInverse_boundaryFaceMap

theorem boundaryRealization_hom_ext {n : ℕ} {X : TopCat.{u}}
    {f g : _root_.SSet.toTop.obj (_root_.SSet.boundary (n + 1) : _root_.SSet.{u}) ⟶ X}
    (h : ∀ i : Fin (n + 2), _root_.SSet.toTop.map (_root_.SSet.boundary.ι i) ≫ f =
      _root_.SSet.toTop.map (_root_.SSet.boundary.ι i) ≫ g) : f = g := by
  apply (sSetTopAdj.homEquiv _ _).injective
  apply _root_.SSet.boundary.hom_ext
  intro i
  have he := congrArg (sSetTopAdj.homEquiv Δ[n] X) (h i)
  simpa only [sSetTopAdj.homEquiv_naturality_left] using he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.boundaryRealization_hom_ext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.boundaryRealization_hom_ext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.boundaryRealization_hom_ext ``Submission.DifferentialGeometry.SSet.boundaryRealization_hom_ext


@[simp]
theorem boundaryRealizationInverse_lift (n : ℕ)
    (x : _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet.{u})) :
    boundaryRealizationInverse n (boundaryRealizationLift n x) = x := by
  cases n with
  | zero => exact isEmptyElim x
  | succ n =>
    have he : boundaryRealizationLift (n + 1) ≫
        TopCat.ofHom (boundaryRealizationInverse (n + 1)) = 𝟙 _ := by
      apply boundaryRealization_hom_ext
      intro i
      apply TopCat.ext
      intro y
      have h := boundaryRealizationInverse_boundaryFaceMap i
        ((SimplexCategory.toTopHomeo ⦋n⦌) y)
      change boundaryRealizationInverse (n + 1)
          (boundaryRealizationLift (n + 1)
            ((_root_.SSet.toTop.map (_root_.SSet.boundary.ι i)).hom
              ((SimplexCategory.toTopHomeo ⦋n⦌).symm ((SimplexCategory.toTopHomeo ⦋n⦌) y)))) =
        (_root_.SSet.toTop.map (_root_.SSet.boundary.ι i)).hom
          ((SimplexCategory.toTopHomeo ⦋n⦌).symm ((SimplexCategory.toTopHomeo ⦋n⦌) y)) at h
      rw [Homeomorph.symm_apply_apply] at h
      exact h
    exact ConcreteCategory.congr_hom he x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.boundaryRealizationInverse_lift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.boundaryRealizationInverse_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.boundaryRealizationInverse_lift ``Submission.DifferentialGeometry.SSet.boundaryRealizationInverse_lift


theorem injective_boundaryRealizationLift (n : ℕ) :
    Function.Injective (boundaryRealizationLift.{u} n) :=
  Function.LeftInverse.injective (boundaryRealizationInverse_lift n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.injective_boundaryRealizationLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.injective_boundaryRealizationLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.injective_boundaryRealizationLift ``Submission.DifferentialGeometry.SSet.injective_boundaryRealizationLift

def boundaryRealizationHomeomorph (n : ℕ) :
    _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet.{u}) ≃ₜ simplexBoundarySet n where
  toFun := boundaryRealizationLift n
  invFun := boundaryRealizationInverse n
  left_inv := boundaryRealizationInverse_lift n
  right_inv := boundaryRealizationLift_inverse n
  continuous_toFun := (boundaryRealizationLift n).hom.continuous
  continuous_invFun := (boundaryRealizationInverse n).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.boundaryRealizationHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.boundaryRealizationHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.boundaryRealizationHomeomorph ``Submission.DifferentialGeometry.SSet.boundaryRealizationHomeomorph


@[simp]
theorem boundaryRealizationHomeomorph_apply (n : ℕ)
    (x : _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet.{u})) :
    boundaryRealizationHomeomorph n x = boundaryRealizationLift n x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.boundaryRealizationHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.boundaryRealizationHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.boundaryRealizationHomeomorph_apply ``Submission.DifferentialGeometry.SSet.boundaryRealizationHomeomorph_apply


theorem boundaryRealizationHomeomorph_symm_face {n : ℕ} (p : simplexBoundarySet.{u} (n + 1))
    (i : Fin (n + 2)) (hi : p.val.down.val i = 0) :
    (boundaryRealizationHomeomorph (n + 1)).symm p =
      boundaryFaceMap i (DifferentialGeometry.Simplex.faceDelete i ⟨p.val.down, hi⟩) :=
  boundaryRealizationInverse_face p i hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.boundaryRealizationHomeomorph_symm_face then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.boundaryRealizationHomeomorph_symm_face"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.boundaryRealizationHomeomorph_symm_face ``Submission.DifferentialGeometry.SSet.boundaryRealizationHomeomorph_symm_face


theorem boundaryRealizationHomeomorph_ambient (n : ℕ)
    (x : _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet.{u})) :
    (boundaryRealizationHomeomorph n x).val = boundaryRealizationMap n x :=
  ConcreteCategory.congr_hom (boundaryRealizationLift_inclusion n) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.boundaryRealizationHomeomorph_ambient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.boundaryRealizationHomeomorph_ambient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.boundaryRealizationHomeomorph_ambient ``Submission.DifferentialGeometry.SSet.boundaryRealizationHomeomorph_ambient


theorem isClosedEmbedding_boundaryRealizationMap (n : ℕ) :
    Topology.IsClosedEmbedding (boundaryRealizationMap.{u} n) := by
  have h := (isClosed_simplexBoundarySet n).isClosedEmbedding_subtypeVal.comp
    (boundaryRealizationHomeomorph.{u} n).isClosedEmbedding
  simpa only [Function.comp_def, boundaryRealizationHomeomorph_ambient] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.isClosedEmbedding_boundaryRealizationMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.isClosedEmbedding_boundaryRealizationMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.isClosedEmbedding_boundaryRealizationMap ``Submission.DifferentialGeometry.SSet.isClosedEmbedding_boundaryRealizationMap

end DifferentialGeometry.SSet
