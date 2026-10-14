import Submission.DifferentialGeometry.Topology.Homology.SmallChains.Subspace
import Submission.DifferentialGeometry.Topology.SimplicialSet.UnionChains

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.Simplicial _root_.AlgebraicTopology
noncomputable section
universe u
namespace DifferentialGeometry.Homology
variable (X : TopCat.{u}) (s t : Set X)


def twoSetFamily : Bool → Set X := fun b => if b then s else t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.twoSetFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.twoSetFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.twoSetFamily ``Submission.DifferentialGeometry.Homology.twoSetFamily


theorem smallSingularSimplices_inter :
    smallSingularSimplices X (fun _ : Unit => s ∩ t) =
      smallSingularSimplices X (fun _ : Unit => s) ⊓
        smallSingularSimplices X (fun _ : Unit => t) := by
  ext n σ
  change (∃ _ : Unit, Set.range (X.toSSetObjEquiv n σ) ⊆ s ∩ t) ↔
    ((∃ _ : Unit, Set.range (X.toSSetObjEquiv n σ) ⊆ s) ∧
      (∃ _ : Unit, Set.range (X.toSSetObjEquiv n σ) ⊆ t))
  simp only [exists_const, Set.subset_inter_iff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSimplices_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSimplices_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSimplices_inter ``Submission.DifferentialGeometry.Homology.smallSingularSimplices_inter


theorem smallSingularSimplices_twoSet :
    smallSingularSimplices X (twoSetFamily X s t) =
      smallSingularSimplices X (fun _ : Unit => s) ⊔
        smallSingularSimplices X (fun _ : Unit => t) := by
  ext n σ
  change (∃ b : Bool, Set.range (X.toSSetObjEquiv n σ) ⊆ twoSetFamily X s t b) ↔
    ((∃ _ : Unit, Set.range (X.toSSetObjEquiv n σ) ⊆ s) ∨
      (∃ _ : Unit, Set.range (X.toSSetObjEquiv n σ) ⊆ t))
  simp only [exists_const, Bool.exists_bool, twoSetFamily, Bool.false_eq_true,
    if_false, if_true, or_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSimplices_twoSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSimplices_twoSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSimplices_twoSet ``Submission.DifferentialGeometry.Homology.smallSingularSimplices_twoSet


def subspaceInclusion {s t : Set X} (h : s ⊆ t) : TopCat.of s ⟶ TopCat.of t :=
  TopCat.ofHom ⟨Set.inclusion h, continuous_inclusion h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.subspaceInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.subspaceInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.subspaceInclusion ``Submission.DifferentialGeometry.Homology.subspaceInclusion


def firstSubspaceToSmall : TopCat.toSSet.obj (TopCat.of s) ⟶
    (smallSingularSimplices X (twoSetFamily X s t) : SSet) :=
  (singularSubspaceIso X s).hom ≫ SSet.Subcomplex.homOfLE
    (smallSingularSimplices_le X (fun _ : Unit => s) (twoSetFamily X s t)
      (fun _ => ⟨true, Set.Subset.rfl⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.firstSubspaceToSmall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.firstSubspaceToSmall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.firstSubspaceToSmall ``Submission.DifferentialGeometry.Homology.firstSubspaceToSmall


def secondSubspaceToSmall : TopCat.toSSet.obj (TopCat.of t) ⟶
    (smallSingularSimplices X (twoSetFamily X s t) : SSet) :=
  (singularSubspaceIso X t).hom ≫ SSet.Subcomplex.homOfLE
    (smallSingularSimplices_le X (fun _ : Unit => t) (twoSetFamily X s t)
      (fun _ => ⟨false, Set.Subset.rfl⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.secondSubspaceToSmall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.secondSubspaceToSmall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.secondSubspaceToSmall ``Submission.DifferentialGeometry.Homology.secondSubspaceToSmall


@[reassoc (attr := simp)]
theorem firstSubspaceToSmall_ι :
    firstSubspaceToSmall X s t ≫ (smallSingularSimplices X (twoSetFamily X s t)).ι =
      TopCat.toSSet.map (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.firstSubspaceToSmall_ι then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.firstSubspaceToSmall_ι"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.firstSubspaceToSmall_ι ``Submission.DifferentialGeometry.Homology.firstSubspaceToSmall_ι


@[reassoc (attr := simp)]
theorem secondSubspaceToSmall_ι :
    secondSubspaceToSmall X s t ≫ (smallSingularSimplices X (twoSetFamily X s t)).ι =
      TopCat.toSSet.map (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(t, X))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.secondSubspaceToSmall_ι then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.secondSubspaceToSmall_ι"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.secondSubspaceToSmall_ι ``Submission.DifferentialGeometry.Homology.secondSubspaceToSmall_ι


theorem subspaceSmallSquare :
    _root_.CategoryTheory.IsPushout (TopCat.toSSet.map (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left)))
      (TopCat.toSSet.map (subspaceInclusion X (show s ∩ t ⊆ t from Set.inter_subset_right)))
      (firstSubspaceToSmall X s t) (secondSubspaceToSmall X s t) := by
  let A := smallSingularSimplices X (fun _ : Unit => s)
  let B := smallSingularSimplices X (fun _ : Unit => t)
  have sq : SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) := ⟨rfl, rfl⟩
  apply sq.isPushout.of_iso'
    (singularSubspaceIso X (s ∩ t) ≪≫ SSet.Subcomplex.eqToIso (smallSingularSimplices_inter X s t))
    (singularSubspaceIso X s) (singularSubspaceIso X t)
    (SSet.Subcomplex.eqToIso (smallSingularSimplices_twoSet X s t))
  all_goals
    ext n σ
    apply Subtype.ext
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.subspaceSmallSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.subspaceSmallSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.subspaceSmallSquare ``Submission.DifferentialGeometry.Homology.subspaceSmallSquare

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


theorem subspaceSmallChainSquare :
    _root_.CategoryTheory.IsPushout
      (SSet.chainComplexMap (TopCat.toSSet.map
        (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left))) R)
      (SSet.chainComplexMap (TopCat.toSSet.map
        (subspaceInclusion X (show s ∩ t ⊆ t from Set.inter_subset_right))) R)
      (SSet.chainComplexMap (firstSubspaceToSmall X s t) R)
      (SSet.chainComplexMap (secondSubspaceToSmall X s t) R) :=
  ((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).map_isPushout (subspaceSmallSquare X s t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.subspaceSmallChainSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.subspaceSmallChainSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.subspaceSmallChainSquare ``Submission.DifferentialGeometry.Homology.subspaceSmallChainSquare


abbrev subspaceSmallShortComplex : _root_.CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ) :=
  DifferentialGeometry.ShortComplex.pushoutShortComplex (subspaceSmallChainSquare X s t R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.subspaceSmallShortComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.subspaceSmallShortComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.subspaceSmallShortComplex ``Submission.DifferentialGeometry.Homology.subspaceSmallShortComplex


theorem subspaceSmallShortExact : (subspaceSmallShortComplex X s t R).ShortExact := by
  have : _root_.CategoryTheory.Mono (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left)) :=
    (TopCat.mono_iff_injective _).mpr (Set.inclusion_injective (show s ∩ t ⊆ s from Set.inter_subset_left))
  have : _root_.CategoryTheory.Mono (SSet.chainComplexMap (TopCat.toSSet.map
      (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left))) R) := by
    unfold SSet.chainComplexMap
    infer_instance
  exact DifferentialGeometry.ShortComplex.pushoutShortExact (subspaceSmallChainSquare X s t R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.subspaceSmallShortExact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.subspaceSmallShortExact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.subspaceSmallShortExact ``Submission.DifferentialGeometry.Homology.subspaceSmallShortExact

end DifferentialGeometry.Homology
