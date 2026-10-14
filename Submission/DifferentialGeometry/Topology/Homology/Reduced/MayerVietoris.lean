import Submission.DifferentialGeometry.Topology.Homology.Algebra.Augment
import Submission.DifferentialGeometry.Topology.Homology.Algebra.Biproduct
import Submission.DifferentialGeometry.Topology.Homology.Reduced
import Submission.DifferentialGeometry.Topology.Homology.SmallChains.Union
import Submission.DifferentialGeometry.Topology.Homology.SmallChains.QuasiIso
import Mathlib.Algebra.Homology.HomologySequence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology
open scoped _root_.Simplicial _root_.ContinuousMap
noncomputable section
universe u v
namespace DifferentialGeometry.Homology
variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)
  (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)


def smallChainAugmentation :
    ((smallSingularSimplices X U : SSet).chainComplex R).X 0 ⟶ R :=
  (SSet.chainComplexMap (smallSingularSimplices X U).ι R).f 0 ≫ singularAugmentation R X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallChainAugmentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallChainAugmentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallChainAugmentation ``Submission.DifferentialGeometry.Homology.smallChainAugmentation


theorem d_smallChainAugmentation :
    ((smallSingularSimplices X U : SSet).chainComplex R).d 1 0 ≫
      smallChainAugmentation R X U = 0 := by
  change _ ≫ (SSet.chainComplexMap (smallSingularSimplices X U).ι R).f 0 ≫
    singularAugmentation R X = 0
  rw [← Category.assoc,
    ← (SSet.chainComplexMap (smallSingularSimplices X U).ι R).comm 1 0,
    Category.assoc, d_singularAugmentation, _root_.CategoryTheory.Limits.comp_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.d_smallChainAugmentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.d_smallChainAugmentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.d_smallChainAugmentation ``Submission.DifferentialGeometry.Homology.d_smallChainAugmentation


def augmentedSmallChainComplex : ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.augment ((smallSingularSimplices X U : SSet).chainComplex R)
    (smallChainAugmentation R X U) (d_smallChainAugmentation R X U)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedSmallChainComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedSmallChainComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedSmallChainComplex ``Submission.DifferentialGeometry.Homology.augmentedSmallChainComplex


def augmentedSmallChainMap :
    augmentedSmallChainComplex R X U ⟶ augmentedSingularChainComplex R X :=
  DifferentialGeometry.ChainComplex.augmentMap (d_smallChainAugmentation R X U)
    (d_singularAugmentation R X) (smallChainMap X U R) (𝟙 R)
    (Category.comp_id (smallChainAugmentation R X U)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedSmallChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedSmallChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedSmallChainMap ``Submission.DifferentialGeometry.Homology.augmentedSmallChainMap


@[simp]
theorem augmentedSmallChainMap_f_zero : (augmentedSmallChainMap R X U).f 0 = 𝟙 R := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedSmallChainMap_f_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedSmallChainMap_f_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedSmallChainMap_f_zero ``Submission.DifferentialGeometry.Homology.augmentedSmallChainMap_f_zero


@[simp]
theorem augmentedSmallChainMap_f_succ (n : ℕ) :
    (augmentedSmallChainMap R X U).f (n + 1) = (smallChainMap X U R).f n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedSmallChainMap_f_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedSmallChainMap_f_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedSmallChainMap_f_succ ``Submission.DifferentialGeometry.Homology.augmentedSmallChainMap_f_succ

theorem quasiIso_augmentedSmallChainMap
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    QuasiIso (augmentedSmallChainMap R X U) := by
  have hf := quasiIso_smallChainMap X U R hopen hcover
  have hf' : QuasiIso (SSet.chainComplexMap (smallSingularSimplices X U).ι R) := hf
  exact DifferentialGeometry.ChainComplex.quasiIso_augmentMap
    (d_smallChainAugmentation R X U) (d_singularAugmentation R X)
    (SSet.chainComplexMap (smallSingularSimplices X U).ι R) (𝟙 R) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.quasiIso_augmentedSmallChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.quasiIso_augmentedSmallChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.quasiIso_augmentedSmallChainMap ``Submission.DifferentialGeometry.Homology.quasiIso_augmentedSmallChainMap

def augmentedSmallChainHomologyIso
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (augmentedSmallChainComplex R X U).homology (n + 1) ≅
      reducedSingularHomology R X n := by
  have := quasiIso_augmentedSmallChainMap R X U hopen hcover
  exact isoOfQuasiIsoAt (augmentedSmallChainMap R X U) (n + 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedSmallChainHomologyIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedSmallChainHomologyIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedSmallChainHomologyIso ``Submission.DifferentialGeometry.Homology.augmentedSmallChainHomologyIso


@[simp]
theorem augmentedSmallChainHomologyIso_hom
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i) (n : ℕ) :
    (augmentedSmallChainHomologyIso R X U hopen hcover n).hom =
      HomologicalComplex.homologyMap (augmentedSmallChainMap R X U) (n + 1) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedSmallChainHomologyIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedSmallChainHomologyIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedSmallChainHomologyIso_hom ``Submission.DifferentialGeometry.Homology.augmentedSmallChainHomologyIso_hom

variable (s t : Set X)

private theorem firstSubspace_augmentation :
    (SSet.chainComplexMap (firstSubspaceToSmall X s t) R).f 0 ≫
      smallChainAugmentation R X (twoSetFamily X s t) =
      singularAugmentation R (TopCat.of s) := by
  change (SSet.chainComplexMap (firstSubspaceToSmall X s t) R).f 0 ≫
    (SSet.chainComplexMap (smallSingularSimplices X (twoSetFamily X s t)).ι R).f 0 ≫
      singularAugmentation R X = _
  rw [← Category.assoc, ← HomologicalComplex.comp_f]
  rw [← Functor.map_comp, firstSubspaceToSmall_ι]
  exact singularAugmentation_naturality R _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.firstSubspace_augmentation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.firstSubspace_augmentation target :: scope.openDecls } }

private theorem secondSubspace_augmentation :
    (SSet.chainComplexMap (secondSubspaceToSmall X s t) R).f 0 ≫
      smallChainAugmentation R X (twoSetFamily X s t) =
      singularAugmentation R (TopCat.of t) := by
  change (SSet.chainComplexMap (secondSubspaceToSmall X s t) R).f 0 ≫
    (SSet.chainComplexMap (smallSingularSimplices X (twoSetFamily X s t)).ι R).f 0 ≫
      singularAugmentation R X = _
  rw [← Category.assoc, ← HomologicalComplex.comp_f]
  rw [← Functor.map_comp, secondSubspaceToSmall_ι]
  exact singularAugmentation_naturality R _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.secondSubspace_augmentation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.secondSubspace_augmentation target :: scope.openDecls } }


def augmentedFirstSubspaceToSmall : augmentedSingularChainComplex R (TopCat.of s) ⟶
    augmentedSmallChainComplex R X (twoSetFamily X s t) :=
  DifferentialGeometry.ChainComplex.augmentMap (d_singularAugmentation R (TopCat.of s))
    (d_smallChainAugmentation R X (twoSetFamily X s t))
    (SSet.chainComplexMap (firstSubspaceToSmall X s t) R) (𝟙 R)
    (by simpa using! firstSubspace_augmentation R X s t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedFirstSubspaceToSmall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedFirstSubspaceToSmall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedFirstSubspaceToSmall ``Submission.DifferentialGeometry.Homology.augmentedFirstSubspaceToSmall


def augmentedSecondSubspaceToSmall : augmentedSingularChainComplex R (TopCat.of t) ⟶
    augmentedSmallChainComplex R X (twoSetFamily X s t) :=
  DifferentialGeometry.ChainComplex.augmentMap (d_singularAugmentation R (TopCat.of t))
    (d_smallChainAugmentation R X (twoSetFamily X s t))
    (SSet.chainComplexMap (secondSubspaceToSmall X s t) R) (𝟙 R)
    (by simpa using! secondSubspace_augmentation R X s t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedSecondSubspaceToSmall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedSecondSubspaceToSmall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedSecondSubspaceToSmall ``Submission.DifferentialGeometry.Homology.augmentedSecondSubspaceToSmall


@[simp]
theorem augmentedFirstSubspaceToSmall_f_zero :
    (augmentedFirstSubspaceToSmall R X s t).f 0 = 𝟙 R := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedFirstSubspaceToSmall_f_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedFirstSubspaceToSmall_f_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedFirstSubspaceToSmall_f_zero ``Submission.DifferentialGeometry.Homology.augmentedFirstSubspaceToSmall_f_zero


@[simp]
theorem augmentedSecondSubspaceToSmall_f_zero :
    (augmentedSecondSubspaceToSmall R X s t).f 0 = 𝟙 R := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedSecondSubspaceToSmall_f_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedSecondSubspaceToSmall_f_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedSecondSubspaceToSmall_f_zero ``Submission.DifferentialGeometry.Homology.augmentedSecondSubspaceToSmall_f_zero


@[simp]
theorem augmentedFirstSubspaceToSmall_f_succ (n : ℕ) :
    (augmentedFirstSubspaceToSmall R X s t).f (n + 1) =
      (SSet.chainComplexMap (firstSubspaceToSmall X s t) R).f n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedFirstSubspaceToSmall_f_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedFirstSubspaceToSmall_f_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedFirstSubspaceToSmall_f_succ ``Submission.DifferentialGeometry.Homology.augmentedFirstSubspaceToSmall_f_succ


@[simp]
theorem augmentedSecondSubspaceToSmall_f_succ (n : ℕ) :
    (augmentedSecondSubspaceToSmall R X s t).f (n + 1) =
      (SSet.chainComplexMap (secondSubspaceToSmall X s t) R).f n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedSecondSubspaceToSmall_f_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedSecondSubspaceToSmall_f_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedSecondSubspaceToSmall_f_succ ``Submission.DifferentialGeometry.Homology.augmentedSecondSubspaceToSmall_f_succ

theorem augmentedSubspaceSmallSquare :
    _root_.CategoryTheory.IsPushout
      (augmentedSingularChainMap R
        (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left)))
      (augmentedSingularChainMap R
        (subspaceInclusion X (show s ∩ t ⊆ t from Set.inter_subset_right)))
      (augmentedFirstSubspaceToSmall R X s t) (augmentedSecondSubspaceToSmall R X s t) := by
  have hn : ∀ n, _root_.CategoryTheory.IsPushout
      ((augmentedSingularChainMap R
        (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left))).f n)
      ((augmentedSingularChainMap R
        (subspaceInclusion X (show s ∩ t ⊆ t from Set.inter_subset_right))).f n)
      ((augmentedFirstSubspaceToSmall R X s t).f n)
      ((augmentedSecondSubspaceToSmall R X s t).f n) := by
    intro n
    cases n with
    | zero => exact IsPushout.of_id_fst
    | succ n =>
      exact (HomologicalComplex.eval (ModuleCat.{u} k) (ComplexShape.down ℕ) n).map_isPushout
        (subspaceSmallChainSquare X s t R)
  refine ⟨⟨?w⟩, ⟨HomologicalComplex.isColimitOfEval _ _ (fun n => ?_)⟩⟩
  · apply HomologicalComplex.Hom.ext
    funext n
    exact (hn n).w
  · exact (PushoutCocone.isColimitMapCoconeEquiv _ _).symm (hn n).isColimit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedSubspaceSmallSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedSubspaceSmallSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedSubspaceSmallSquare ``Submission.DifferentialGeometry.Homology.augmentedSubspaceSmallSquare


abbrev augmentedSubspaceSmallShortComplex : _root_.CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ) :=
  DifferentialGeometry.ShortComplex.pushoutShortComplex (augmentedSubspaceSmallSquare R X s t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedSubspaceSmallShortComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedSubspaceSmallShortComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedSubspaceSmallShortComplex ``Submission.DifferentialGeometry.Homology.augmentedSubspaceSmallShortComplex

theorem augmentedSubspaceSmallShortExact :
    (augmentedSubspaceSmallShortComplex R X s t).ShortExact := by
  have : _root_.CategoryTheory.Mono (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left)) :=
    (TopCat.mono_iff_injective _).mpr (Set.inclusion_injective Set.inter_subset_left)
  have : _root_.CategoryTheory.Mono (augmentedSingularChainMap R
      (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left))) := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    cases n with
    | zero => change _root_.CategoryTheory.Mono (𝟙 R); infer_instance
    | succ n =>
      change _root_.CategoryTheory.Mono ((SSet.chainComplexMap (TopCat.toSSet.map
        (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left))) R).f n)
      unfold SSet.chainComplexMap
      infer_instance
  exact DifferentialGeometry.ShortComplex.pushoutShortExact (augmentedSubspaceSmallSquare R X s t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedSubspaceSmallShortExact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedSubspaceSmallShortExact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedSubspaceSmallShortExact ``Submission.DifferentialGeometry.Homology.augmentedSubspaceSmallShortExact


def augmentedSmallConnectingMap (n : ℕ) :
    (augmentedSmallChainComplex R X (twoSetFamily X s t)).homology (n + 2) ⟶
      reducedSingularHomology R (TopCat.of ↥(s ∩ t)) n :=
  (augmentedSubspaceSmallShortExact R X s t).δ (n + 2) (n + 1) rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedSmallConnectingMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedSmallConnectingMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedSmallConnectingMap ``Submission.DifferentialGeometry.Homology.augmentedSmallConnectingMap

private theorem isZero_middle_homology [ContractibleSpace s] [ContractibleSpace t] (n : ℕ) :
    IsZero ((augmentedSubspaceSmallShortComplex R X s t).X₂.homology (n + 1)) :=
  IsZero.of_iso ((_root_.CategoryTheory.Limits.biprod_isZero_iff _ _).mpr
    ⟨isZero_reducedSingularHomology_of_contractible R (TopCat.of s) n,
      isZero_reducedSingularHomology_of_contractible R (TopCat.of t) n⟩)
    (DifferentialGeometry.HomologicalComplex.homologyBiprodIso
      (augmentedSingularChainComplex R (TopCat.of s))
      (augmentedSingularChainComplex R (TopCat.of t)) (n + 1))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.isZero_middle_homology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.isZero_middle_homology target :: scope.openDecls } }

def augmentedSmallConnectingIso [ContractibleSpace s] [ContractibleSpace t] (n : ℕ) :
    (augmentedSmallChainComplex R X (twoSetFamily X s t)).homology (n + 2) ≅
      reducedSingularHomology R (TopCat.of ↥(s ∩ t)) n :=
  (augmentedSubspaceSmallShortExact R X s t).δIso (n + 2) (n + 1) rfl
    (isZero_middle_homology R X s t (n + 1)) (isZero_middle_homology R X s t n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedSmallConnectingIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedSmallConnectingIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedSmallConnectingIso ``Submission.DifferentialGeometry.Homology.augmentedSmallConnectingIso


@[simp]
theorem augmentedSmallConnectingIso_hom [ContractibleSpace s] [ContractibleSpace t] (n : ℕ) :
    (augmentedSmallConnectingIso R X s t n).hom = augmentedSmallConnectingMap R X s t n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedSmallConnectingIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedSmallConnectingIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedSmallConnectingIso_hom ``Submission.DifferentialGeometry.Homology.augmentedSmallConnectingIso_hom

private theorem twoSetFamily_open (hs : IsOpen s) (ht : IsOpen t) :
    ∀ b, IsOpen (twoSetFamily X s t b) := by
  intro b
  cases b
  · exact ht
  · exact hs

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.twoSetFamily_open
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.twoSetFamily_open target :: scope.openDecls } }

private theorem twoSetFamily_cover (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) :
    ∀ x : X, ∃ b, x ∈ twoSetFamily X s t b := by
  intro x
  rcases hcover x with h | h
  · exact ⟨true, h⟩
  · exact ⟨false, h⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.twoSetFamily_cover
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.twoSetFamily_cover target :: scope.openDecls } }

def reducedMayerVietorisConnectingIso [ContractibleSpace s] [ContractibleSpace t]
    (hs : IsOpen s) (ht : IsOpen t) (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) (n : ℕ) :
    reducedSingularHomology R X (n + 1) ≅
      reducedSingularHomology R (TopCat.of ↥(s ∩ t)) n :=
  (augmentedSmallChainHomologyIso R X (twoSetFamily X s t)
    (twoSetFamily_open X s t hs ht) (twoSetFamily_cover X s t hcover) (n + 1)).symm ≪≫
      augmentedSmallConnectingIso R X s t n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.reducedMayerVietorisConnectingIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.reducedMayerVietorisConnectingIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.reducedMayerVietorisConnectingIso ``Submission.DifferentialGeometry.Homology.reducedMayerVietorisConnectingIso

@[reassoc (attr := simp)]
theorem small_inclusion_reducedMayerVietorisConnectingIso
    [ContractibleSpace s] [ContractibleSpace t]
    (hs : IsOpen s) (ht : IsOpen t) (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) (n : ℕ) :
    HomologicalComplex.homologyMap
      (augmentedSmallChainMap R X (twoSetFamily X s t)) (n + 2) ≫
        (reducedMayerVietorisConnectingIso R X s t hs ht hcover n).hom =
          augmentedSmallConnectingMap R X s t n := by
  change (augmentedSmallChainHomologyIso R X (twoSetFamily X s t)
    (twoSetFamily_open X s t hs ht) (twoSetFamily_cover X s t hcover) (n + 1)).hom ≫
      ((augmentedSmallChainHomologyIso R X (twoSetFamily X s t)
        (twoSetFamily_open X s t hs ht) (twoSetFamily_cover X s t hcover) (n + 1)).inv ≫ _) = _
  rw [Iso.hom_inv_id_assoc]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.small_inclusion_reducedMayerVietorisConnectingIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.small_inclusion_reducedMayerVietorisConnectingIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.small_inclusion_reducedMayerVietorisConnectingIso ``Submission.DifferentialGeometry.Homology.small_inclusion_reducedMayerVietorisConnectingIso

end DifferentialGeometry.Homology
