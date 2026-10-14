import Submission.DifferentialGeometry.Topology.LocalDegree.SphereMap
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Products

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.Metric _root_.Set
open scoped _root_.Topology _root_.unitInterval _root_.Simplicial

noncomputable section

namespace DifferentialGeometry.LocalDegree


abbrev ZeroSphere := _root_.Metric.sphere (0 : ℝ) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.ZeroSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.ZeroSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.ZeroSphere ``Submission.DifferentialGeometry.LocalDegree.ZeroSphere


def zeroSpherePositive : ZeroSphere := ⟨1, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSpherePositive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSpherePositive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSpherePositive ``Submission.DifferentialGeometry.LocalDegree.zeroSpherePositive


def zeroSphereNegative : ZeroSphere := ⟨-1, by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereNegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereNegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereNegative ``Submission.DifferentialGeometry.LocalDegree.zeroSphereNegative

private theorem zeroSphere_cases (v : ZeroSphere) :
    v = zeroSpherePositive ∨ v = zeroSphereNegative := by
  have hv := v.property
  change (v : ℝ) ∈ _root_.Metric.sphere (0 : ℝ) 1 at hv
  rw [Real.sphere_eq_pair 0 (by norm_num)] at hv
  simp only [zero_sub, zero_add, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff] at hv
  exact hv.symm.imp (fun h ↦ Subtype.ext h) (fun h ↦ Subtype.ext h)

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.zeroSphere_cases
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.zeroSphere_cases target :: scope.openDecls } }

private instance _root_.Submission.DifferentialGeometry.LocalDegree.instFiniteElemRealZeroSphere : Finite ZeroSphere := by
  unfold ZeroSphere
  rw [Real.sphere_eq_pair 0 (by norm_num)]
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.instFiniteElemRealZeroSphere
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.instFiniteElemRealZeroSphere target :: scope.openDecls } }

private instance _root_.Submission.DifferentialGeometry.LocalDegree.instFintypeElemRealZeroSphere : Fintype ZeroSphere := Fintype.ofFinite _

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.instFintypeElemRealZeroSphere
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.instFintypeElemRealZeroSphere target :: scope.openDecls } }

private def componentEquiv : ZerothHomotopy ZeroSphere ≃ ZeroSphere where
  toFun := ZerothHomotopy.lift id (fun _ _ p ↦ by
    simpa using TotallyDisconnectedSpace.eq_of_continuous p p.continuous 0 1)
  invFun := ZerothHomotopy.mk
  left_inv v := by induction v; rfl
  right_inv _ := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.componentEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.componentEquiv target :: scope.openDecls } }

private abbrev sphereSpace : TopCat := TopCat.of ZeroSphere

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.sphereSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.sphereSpace target :: scope.openDecls } }

private abbrev intCoefficient : ModuleCat ℤ := ModuleCat.of ℤ ℤ

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.intCoefficient
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.intCoefficient target :: scope.openDecls } }

private abbrev homologyFunctor :=
  (_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj intCoefficient

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.homologyFunctor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.homologyFunctor target :: scope.openDecls } }


abbrev ZeroSphereH0 :=
  ((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of ZeroSphere)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.ZeroSphereH0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.ZeroSphereH0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.ZeroSphereH0 ``Submission.DifferentialGeometry.LocalDegree.ZeroSphereH0

private def homologyEquiv : ZeroSphereH0 ≃ₗ[ℤ] (ZeroSphere → ℤ) :=
  ((TopCat.singularHomology₀Iso sphereSpace intCoefficient ≪≫
      (sigmaConst.obj intCoefficient).mapIso componentEquiv.toIso ≪≫
      ModuleCat.coprodIsoDirectSum (fun _ : ZeroSphere ↦ intCoefficient)).toLinearEquiv).trans
    (DirectSum.linearEquivFunOnFintype ℤ ZeroSphere (fun _ ↦ ℤ))

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.homologyEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.homologyEquiv target :: scope.openDecls } }

private def pointClassHom (X : TopCat) (x : X) :
    intCoefficient ⟶ homologyFunctor.obj X :=
  ((TopCat.toSSet.obj X).chainComplex intCoefficient).liftCycles
    ((TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm x)) 0
      (by simp) (by simp) ≫
      ((TopCat.toSSet.obj X).chainComplex intCoefficient).homologyπ 0

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.pointClassHom
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.pointClassHom target :: scope.openDecls } }

private theorem pointClassHom_eq (X : TopCat) (x : X) :
    pointClassHom X x =
      ((TopCat.toSSet.obj X).chainComplex intCoefficient).liftCycles
        ((TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm x)) 0
          (by simp) (by simp) ≫
        ((TopCat.toSSet.obj X).chainComplex intCoefficient).homologyπ 0 := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.pointClassHom_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.pointClassHom_eq target :: scope.openDecls } }

private theorem pointClassHom_map {X Y : TopCat} (f : X ⟶ Y) (x : X) :
    pointClassHom X x ≫ homologyFunctor.map f = pointClassHom Y (f x) := by
  rw [pointClassHom_eq, pointClassHom_eq]
  change _ ≫ HomologicalComplex.homologyMap
    (SSet.chainComplexMap (TopCat.toSSet.map f) intCoefficient) 0 = _
  simp only [Category.assoc, HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc, SSet.ι_chainComplexMap_f]
  congr 3

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.pointClassHom_map
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.pointClassHom_map target :: scope.openDecls } }


def zeroSphereClass (v : ZeroSphere) : ZeroSphereH0 := pointClassHom sphereSpace v 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereClass ``Submission.DifferentialGeometry.LocalDegree.zeroSphereClass

private theorem pointClassHom_iso (v : ZeroSphere) :
    pointClassHom sphereSpace v ≫
      (TopCat.singularHomology₀Iso sphereSpace intCoefficient).hom =
        Sigma.ι (fun _ : ZerothHomotopy ZeroSphere ↦ intCoefficient) (ZerothHomotopy.mk v) := by
  rw [pointClassHom_eq]
  change _ ≫ ((TopCat.toSSet.obj sphereSpace).homology₀Iso intCoefficient).hom ≫
    (sigmaConst.obj intCoefficient).map TopCat.zerothHomotopyEquiv.toIso.inv = _
  simp
  congr 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.pointClassHom_iso
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.pointClassHom_iso target :: scope.openDecls } }

private theorem homologyEquiv_class (v : ZeroSphere) :
    homologyEquiv (zeroSphereClass v) = Pi.single v 1 := by
  change DirectSum.linearEquivFunOnFintype ℤ ZeroSphere (fun _ ↦ ℤ)
    (((pointClassHom sphereSpace v ≫
      (TopCat.singularHomology₀Iso sphereSpace intCoefficient).hom ≫
      (sigmaConst.obj intCoefficient).map componentEquiv.toIso.hom ≫
      (ModuleCat.coprodIsoDirectSum (fun _ : ZeroSphere ↦ intCoefficient)).hom) 1)) = _
  rw [← Category.assoc, ← Category.assoc, pointClassHom_iso]
  simp [componentEquiv, DirectSum.linearEquivFunOnFintype_lof]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.homologyEquiv_class
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.homologyEquiv_class target :: scope.openDecls } }

private theorem positive_ne_negative : zeroSpherePositive ≠ zeroSphereNegative := by
  intro h
  have := congrArg Subtype.val h
  norm_num [zeroSpherePositive, zeroSphereNegative] at this

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.positive_ne_negative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.positive_ne_negative target :: scope.openDecls } }

private theorem augmentation_class (v : ZeroSphere) :
    TopCat.singularHomology₀ε sphereSpace intCoefficient (zeroSphereClass v) = 1 := by
  have h : pointClassHom sphereSpace v ≫
      TopCat.singularHomology₀ε sphereSpace intCoefficient = 𝟙 intCoefficient := by
    rw [pointClassHom_eq]
    exact SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε
      (TopCat.toSSet.obj sphereSpace) intCoefficient (TopCat.toSSetObj₀Equiv.symm v)
  exact congr($(h) 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.augmentation_class
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.augmentation_class target :: scope.openDecls } }

private theorem homology_decompose (c : ZeroSphereH0) :
    c = homologyEquiv c zeroSpherePositive • zeroSphereClass zeroSpherePositive +
      homologyEquiv c zeroSphereNegative • zeroSphereClass zeroSphereNegative := by
  apply homologyEquiv.injective
  ext v
  rcases zeroSphere_cases v with rfl | rfl <;>
    simp [homologyEquiv_class, positive_ne_negative, positive_ne_negative.symm]

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.homology_decompose
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.homology_decompose target :: scope.openDecls } }

private theorem augmentation_eq (c : ZeroSphereH0) :
    TopCat.singularHomology₀ε sphereSpace intCoefficient c =
      homologyEquiv c zeroSpherePositive + homologyEquiv c zeroSphereNegative := by
  conv_lhs => rw [homology_decompose c]
  rw [map_add, map_zsmul, map_zsmul, augmentation_class, augmentation_class]
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.augmentation_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.augmentation_eq target :: scope.openDecls } }


def zeroSphereReducedH0 : Submodule ℤ ZeroSphereH0 :=
  LinearMap.ker (TopCat.singularHomology₀ε (TopCat.of ZeroSphere) (ModuleCat.of ℤ ℤ)).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereReducedH0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereReducedH0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereReducedH0 ``Submission.DifferentialGeometry.LocalDegree.zeroSphereReducedH0


theorem mem_zeroSphereReducedH0_iff (c : ZeroSphereH0) :
    c ∈ zeroSphereReducedH0 ↔
      TopCat.singularHomology₀ε (TopCat.of ZeroSphere) (ModuleCat.of ℤ ℤ) c = 0 := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.mem_zeroSphereReducedH0_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.mem_zeroSphereReducedH0_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.mem_zeroSphereReducedH0_iff ``Submission.DifferentialGeometry.LocalDegree.mem_zeroSphereReducedH0_iff


def zeroSphereGenerator : zeroSphereReducedH0 :=
  ⟨zeroSphereClass zeroSpherePositive - zeroSphereClass zeroSphereNegative, by
    change TopCat.singularHomology₀ε sphereSpace intCoefficient
      (zeroSphereClass zeroSpherePositive - zeroSphereClass zeroSphereNegative) = 0
    rw [map_sub, augmentation_class, augmentation_class, sub_self]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereGenerator ``Submission.DifferentialGeometry.LocalDegree.zeroSphereGenerator


@[simp]
theorem zeroSphereGenerator_coe :
    (zeroSphereGenerator : ZeroSphereH0) =
      zeroSphereClass zeroSpherePositive - zeroSphereClass zeroSphereNegative := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereGenerator_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereGenerator_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereGenerator_coe ``Submission.DifferentialGeometry.LocalDegree.zeroSphereGenerator_coe

def zeroSphereReducedEquiv : zeroSphereReducedH0 ≃ₗ[ℤ] ℤ where
  toFun c := homologyEquiv c zeroSpherePositive
  invFun n := n • zeroSphereGenerator
  left_inv c := by
    apply Subtype.ext
    apply homologyEquiv.injective
    have hz : homologyEquiv (c : ZeroSphereH0) zeroSpherePositive +
        homologyEquiv (c : ZeroSphereH0) zeroSphereNegative = 0 :=
      (augmentation_eq c).symm.trans c.property
    ext v
    rcases zeroSphere_cases v with rfl | rfl
    · simp [homologyEquiv_class, positive_ne_negative]
    · simp [homologyEquiv_class, positive_ne_negative.symm]
      omega
  right_inv n := by
    simp [homologyEquiv_class, positive_ne_negative]
  map_add' c d := congrFun (homologyEquiv.map_add c d) zeroSpherePositive
  map_smul' n c := by simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereReducedEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereReducedEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereReducedEquiv ``Submission.DifferentialGeometry.LocalDegree.zeroSphereReducedEquiv


theorem zeroSphereReducedEquiv_smul_generator (c : zeroSphereReducedH0) :
    zeroSphereReducedEquiv c • zeroSphereGenerator = c :=
  zeroSphereReducedEquiv.symm_apply_apply c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereReducedEquiv_smul_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereReducedEquiv_smul_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereReducedEquiv_smul_generator ``Submission.DifferentialGeometry.LocalDegree.zeroSphereReducedEquiv_smul_generator


@[simp]
theorem zeroSphereReducedEquiv_generator :
    zeroSphereReducedEquiv zeroSphereGenerator = 1 := by
  change homologyEquiv (zeroSphereGenerator : ZeroSphereH0) zeroSpherePositive = 1
  simp [homologyEquiv_class, positive_ne_negative]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereReducedEquiv_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereReducedEquiv_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereReducedEquiv_generator ``Submission.DifferentialGeometry.LocalDegree.zeroSphereReducedEquiv_generator


theorem zeroSphereHomologyMap_class (f : C(ZeroSphere, ZeroSphere)) (v : ZeroSphere) :
    ((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom f) (zeroSphereClass v) = zeroSphereClass (f v) :=
  congr($(pointClassHom_map (TopCat.ofHom f) v) 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereHomologyMap_class then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereHomologyMap_class"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereHomologyMap_class ``Submission.DifferentialGeometry.LocalDegree.zeroSphereHomologyMap_class

private theorem augmentation_map (f : C(ZeroSphere, ZeroSphere)) (c : ZeroSphereH0) :
    TopCat.singularHomology₀ε sphereSpace intCoefficient
      (homologyFunctor.map (TopCat.ofHom f) c) =
        TopCat.singularHomology₀ε sphereSpace intCoefficient c := by
  rw [homology_decompose c]
  simp only [map_add, map_zsmul, zeroSphereHomologyMap_class]
  rw [augmentation_class, augmentation_class, augmentation_class, augmentation_class]

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.augmentation_map
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.augmentation_map target :: scope.openDecls } }


def zeroSphereReducedMap (f : C(ZeroSphere, ZeroSphere)) :
    zeroSphereReducedH0 →ₗ[ℤ] zeroSphereReducedH0 where
  toFun c := ⟨homologyFunctor.map (TopCat.ofHom f) c, (augmentation_map f c).trans c.property⟩
  map_add' c d := Subtype.ext (map_add (homologyFunctor.map (TopCat.ofHom f)).hom
    (c : ZeroSphereH0) (d : ZeroSphereH0))
  map_smul' n c := Subtype.ext (by
    simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereReducedMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereReducedMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereReducedMap ``Submission.DifferentialGeometry.LocalDegree.zeroSphereReducedMap


@[simp]
theorem zeroSphereReducedMap_coe (f : C(ZeroSphere, ZeroSphere)) (c : zeroSphereReducedH0) :
    (zeroSphereReducedMap f c : ZeroSphereH0) =
      ((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 0).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom f) c := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereReducedMap_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereReducedMap_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereReducedMap_coe ``Submission.DifferentialGeometry.LocalDegree.zeroSphereReducedMap_coe


theorem zeroSphereReducedMap_generator_coe (f : C(ZeroSphere, ZeroSphere)) :
    (zeroSphereReducedMap f zeroSphereGenerator : ZeroSphereH0) =
      zeroSphereClass (f zeroSpherePositive) - zeroSphereClass (f zeroSphereNegative) := by
  simp [zeroSphereReducedMap_coe, zeroSphereHomologyMap_class]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereReducedMap_generator_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereReducedMap_generator_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereReducedMap_generator_coe ``Submission.DifferentialGeometry.LocalDegree.zeroSphereReducedMap_generator_coe

def zeroSphereDegree (f : C(ZeroSphere, ZeroSphere)) : ℤ :=
  zeroSphereReducedEquiv (zeroSphereReducedMap f zeroSphereGenerator)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereDegree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereDegree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereDegree ``Submission.DifferentialGeometry.LocalDegree.zeroSphereDegree


theorem zeroSphereDegree_smul_generator (f : C(ZeroSphere, ZeroSphere)) :
    zeroSphereDegree f • zeroSphereGenerator = zeroSphereReducedMap f zeroSphereGenerator :=
  zeroSphereReducedEquiv_smul_generator _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereDegree_smul_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereDegree_smul_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereDegree_smul_generator ``Submission.DifferentialGeometry.LocalDegree.zeroSphereDegree_smul_generator


theorem zeroSphereDegree_eq_iff (f : C(ZeroSphere, ZeroSphere)) (n : ℤ) :
    zeroSphereDegree f = n ↔
      zeroSphereReducedMap f zeroSphereGenerator = n • zeroSphereGenerator := by
  rw [← zeroSphereDegree_smul_generator]
  constructor
  · rintro rfl
    rfl
  · intro h
    have := congrArg zeroSphereReducedEquiv h
    simpa using this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereDegree_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereDegree_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereDegree_eq_iff ``Submission.DifferentialGeometry.LocalDegree.zeroSphereDegree_eq_iff


theorem zeroSphereReducedMap_comp (f g : C(ZeroSphere, ZeroSphere)) :
    zeroSphereReducedMap (g.comp f) = (zeroSphereReducedMap g).comp (zeroSphereReducedMap f) := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  change homologyFunctor.map (TopCat.ofHom f ≫ TopCat.ofHom g) (c : ZeroSphereH0) =
    homologyFunctor.map (TopCat.ofHom g) (homologyFunctor.map (TopCat.ofHom f) c)
  rw [Functor.map_comp]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereReducedMap_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereReducedMap_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereReducedMap_comp ``Submission.DifferentialGeometry.LocalDegree.zeroSphereReducedMap_comp


@[simp]
theorem zeroSphereDegree_id : zeroSphereDegree (ContinuousMap.id ZeroSphere) = 1 := by
  apply (zeroSphereDegree_eq_iff _ _).mpr
  apply Subtype.ext
  simp only [one_smul, zeroSphereReducedMap_coe]
  change homologyFunctor.map (𝟙 sphereSpace) (zeroSphereGenerator : ZeroSphereH0) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereDegree_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereDegree_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereDegree_id ``Submission.DifferentialGeometry.LocalDegree.zeroSphereDegree_id


@[simp]
theorem zeroSphereDegree_const (v : ZeroSphere) :
    zeroSphereDegree (ContinuousMap.const ZeroSphere v) = 0 := by
  apply (zeroSphereDegree_eq_iff _ _).mpr
  apply Subtype.ext
  simp [zeroSphereReducedMap_coe, zeroSphereHomologyMap_class]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereDegree_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereDegree_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereDegree_const ``Submission.DifferentialGeometry.LocalDegree.zeroSphereDegree_const


def zeroSphereAntipodal : C(ZeroSphere, ZeroSphere) where
  toFun v := ⟨-(v : ℝ), by simpa only [mem_sphere_zero_iff_norm, norm_neg] using v.property⟩
  continuous_toFun := continuous_subtype_val.neg.subtype_mk (fun v ↦ by
    change -(v : ℝ) ∈ ZeroSphere
    simpa only [mem_sphere_zero_iff_norm, norm_neg] using v.property)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereAntipodal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereAntipodal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereAntipodal ``Submission.DifferentialGeometry.LocalDegree.zeroSphereAntipodal

private theorem antipodal_positive :
    zeroSphereAntipodal zeroSpherePositive = zeroSphereNegative := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.antipodal_positive
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.antipodal_positive target :: scope.openDecls } }

private theorem antipodal_negative :
    zeroSphereAntipodal zeroSphereNegative = zeroSpherePositive := by
  apply Subtype.ext
  simp [zeroSphereAntipodal, zeroSpherePositive, zeroSphereNegative]

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.antipodal_negative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.antipodal_negative target :: scope.openDecls } }


@[simp]
theorem zeroSphereDegree_antipodal : zeroSphereDegree zeroSphereAntipodal = -1 := by
  apply (zeroSphereDegree_eq_iff _ _).mpr
  apply Subtype.ext
  simp [zeroSphereReducedMap_coe, zeroSphereHomologyMap_class, antipodal_positive,
    antipodal_negative, neg_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereDegree_antipodal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereDegree_antipodal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereDegree_antipodal ``Submission.DifferentialGeometry.LocalDegree.zeroSphereDegree_antipodal


theorem zeroSphereDegree_comp (f g : C(ZeroSphere, ZeroSphere)) :
    zeroSphereDegree (g.comp f) = zeroSphereDegree g * zeroSphereDegree f := by
  apply (zeroSphereDegree_eq_iff _ _).mpr
  rw [zeroSphereReducedMap_comp, LinearMap.comp_apply, ← zeroSphereDegree_smul_generator,
    map_smul, ← zeroSphereDegree_smul_generator, smul_smul, mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereDegree_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereDegree_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereDegree_comp ``Submission.DifferentialGeometry.LocalDegree.zeroSphereDegree_comp


theorem zeroSphereDegree_eq_of_homotopy {f g : C(ZeroSphere, ZeroSphere)}
    (H : f.Homotopy g) : zeroSphereDegree f = zeroSphereDegree g := by
  have H' : TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) := H
  have h := H'.congr_homologyMap_singularChainComplexFunctor intCoefficient 0
  change homologyFunctor.map (TopCat.ofHom f) = homologyFunctor.map (TopCat.ofHom g) at h
  unfold zeroSphereDegree
  congr 1
  apply Subtype.ext
  exact congr($(h) (zeroSphereGenerator : ZeroSphereH0))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereDegree_eq_of_homotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereDegree_eq_of_homotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereDegree_eq_of_homotopy ``Submission.DifferentialGeometry.LocalDegree.zeroSphereDegree_eq_of_homotopy


theorem zeroSphereDegree_eq (f : C(ZeroSphere, ZeroSphere)) :
    zeroSphereDegree f =
      (if f zeroSpherePositive = zeroSpherePositive then 1 else 0) -
        (if f zeroSphereNegative = zeroSpherePositive then 1 else 0) := by
  change homologyEquiv (homologyFunctor.map (TopCat.ofHom f)
    (zeroSphereGenerator : ZeroSphereH0)) zeroSpherePositive = _
  simp [zeroSphereHomologyMap_class, homologyEquiv_class, Pi.single_apply, eq_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereDegree_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereDegree_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereDegree_eq ``Submission.DifferentialGeometry.LocalDegree.zeroSphereDegree_eq

theorem zeroSphereDegree_sphereMap_id (R : ℝ) (r : _root_.Set.Ioc (0 : ℝ) R) :
    zeroSphereDegree (sphereMap (fun y : ℝ ↦ y) 0 R continuousOn_id
      (fun _ _ h ↦ h) r) = 1 := by
  rw [sphereMap_id, zeroSphereDegree_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereDegree_sphereMap_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereDegree_sphereMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereDegree_sphereMap_id ``Submission.DifferentialGeometry.LocalDegree.zeroSphereDegree_sphereMap_id

theorem zeroSphereDegree_sphereMap_eq (f : ℝ → ℝ) (x R : ℝ)
    (hf : ContinuousOn f (_root_.Metric.closedBall x R))
    (hzero : ∀ y ∈ _root_.Metric.closedBall x R, y ≠ x → f y ≠ 0)
    (r₀ r₁ : _root_.Set.Ioc (0 : ℝ) R) :
    zeroSphereDegree (sphereMap f x R hf hzero r₀) =
      zeroSphereDegree (sphereMap f x R hf hzero r₁) :=
  zeroSphereDegree_eq_of_homotopy (sphereMapHomotopy f x R hf hzero r₀ r₁)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.zeroSphereDegree_sphereMap_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.zeroSphereDegree_sphereMap_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.zeroSphereDegree_sphereMap_eq ``Submission.DifferentialGeometry.LocalDegree.zeroSphereDegree_sphereMap_eq

end DifferentialGeometry.LocalDegree
