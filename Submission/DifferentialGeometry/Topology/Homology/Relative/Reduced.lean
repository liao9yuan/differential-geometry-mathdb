import Submission.DifferentialGeometry.Topology.Homology.Relative
import Submission.DifferentialGeometry.Topology.Homology.Reduced
import Submission.DifferentialGeometry.Topology.Homology.Algebra.Augment

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology
open scoped _root_.ZeroObject
noncomputable section
universe u
namespace DifferentialGeometry.Homology
variable (X : TopCat.{u}) (s : Set X) {k : Type u} [Ring k] (R : ModuleCat.{u} k)


def augmentedRelativeChainComplex : ChainComplex (ModuleCat.{u} k) ℕ :=
  (relativeChainComplex X s R).augment (0 : (relativeChainComplex X s R).X 0 ⟶ 0) (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedRelativeChainComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedRelativeChainComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedRelativeChainComplex ``Submission.DifferentialGeometry.Homology.augmentedRelativeChainComplex


def augmentedRelativeProjection :
    augmentedSingularChainComplex R X ⟶ augmentedRelativeChainComplex X s R :=
  DifferentialGeometry.ChainComplex.augmentMap (d_singularAugmentation R X) (by simp)
    (relativeProjection X s R) (0 : R ⟶ 0) (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedRelativeProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedRelativeProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedRelativeProjection ``Submission.DifferentialGeometry.Homology.augmentedRelativeProjection


@[simp]
theorem augmentedRelativeProjection_f_zero :
    (augmentedRelativeProjection X s R).f 0 = (0 : R ⟶ 0) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedRelativeProjection_f_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedRelativeProjection_f_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedRelativeProjection_f_zero ``Submission.DifferentialGeometry.Homology.augmentedRelativeProjection_f_zero


@[simp]
theorem augmentedRelativeProjection_f_succ (n : ℕ) :
    (augmentedRelativeProjection X s R).f (n + 1) = (relativeProjection X s R).f n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedRelativeProjection_f_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedRelativeProjection_f_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedRelativeProjection_f_succ ``Submission.DifferentialGeometry.Homology.augmentedRelativeProjection_f_succ


abbrev augmentedRelativeShortComplex : _root_.CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk
    (augmentedSingularChainMap R
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))))
    (augmentedRelativeProjection X s R) (by
      apply HomologicalComplex.Hom.ext
      funext n
      cases n with
      | zero => change 𝟙 R ≫ (0 : R ⟶ 0) = 0; simp
      | succ n =>
        exact congrArg (fun f => f.f n) (relativeInclusion_projection X s R))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedRelativeShortComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedRelativeShortComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedRelativeShortComplex ``Submission.DifferentialGeometry.Homology.augmentedRelativeShortComplex


theorem augmentedRelativeShortExact : (augmentedRelativeShortComplex X s R).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  cases n with
  | zero =>
    have hmono : _root_.CategoryTheory.Mono (𝟙 R) := inferInstance
    have hepi : _root_.CategoryTheory.Epi (0 : R ⟶ 0) := inferInstance
    refine { exact := ?_, mono_f := hmono, epi_g := hepi }
    apply (ShortComplex.exact_iff_epi _ (by rfl)).mpr
    change _root_.CategoryTheory.Epi (𝟙 R)
    infer_instance
  | succ n =>
    exact (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
      (relativeShortExact X s R) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedRelativeShortExact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedRelativeShortExact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedRelativeShortExact ``Submission.DifferentialGeometry.Homology.augmentedRelativeShortExact

private def relativePositiveShortComplexIso (n : ℕ) :
    (augmentedRelativeChainComplex X s R).sc' (n + 3) (n + 2) (n + 1) ≅
      (relativeChainComplex X s R).sc' (n + 2) (n + 1) n :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by change 𝟙 _ ≫ (relativeChainComplex X s R).d _ _ =
      (relativeChainComplex X s R).d _ _ ≫ 𝟙 _; simp)
    (by change 𝟙 _ ≫ (relativeChainComplex X s R).d _ _ =
      (relativeChainComplex X s R).d _ _ ≫ 𝟙 _; simp)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.relativePositiveShortComplexIso
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.relativePositiveShortComplexIso target :: scope.openDecls } }


def augmentedRelativeHomologySuccIso (n : ℕ) :
    (augmentedRelativeChainComplex X s R).homology (n + 2) ≅
      relativeHomology X s R (n + 1) :=
  (augmentedRelativeChainComplex X s R).homologyIsoSc' (n + 3) (n + 2) (n + 1)
    (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (relativePositiveShortComplexIso X s R n) ≪≫
      ((relativeChainComplex X s R).homologyIsoSc' (n + 2) (n + 1) n
        (by simp) (by simp)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedRelativeHomologySuccIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedRelativeHomologySuccIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedRelativeHomologySuccIso ``Submission.DifferentialGeometry.Homology.augmentedRelativeHomologySuccIso

def relativeReducedConnectingIso [ContractibleSpace X] (n : ℕ) :
    relativeHomology X s R (n + 1) ≅ reducedSingularHomology R (TopCat.of s) n :=
  (augmentedRelativeHomologySuccIso X s R n).symm ≪≫
    (augmentedRelativeShortExact X s R).δIso (n + 2) (n + 1) rfl
      (isZero_reducedSingularHomology_of_contractible R X (n + 1))
      (isZero_reducedSingularHomology_of_contractible R X n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.relativeReducedConnectingIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.relativeReducedConnectingIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.relativeReducedConnectingIso ``Submission.DifferentialGeometry.Homology.relativeReducedConnectingIso

@[reassoc (attr := simp)]
theorem augmentedRelativeHomologySuccIso_connecting [ContractibleSpace X] (n : ℕ) :
    (augmentedRelativeHomologySuccIso X s R n).hom ≫
      (relativeReducedConnectingIso X s R n).hom =
        (augmentedRelativeShortExact X s R).δ (n + 2) (n + 1) rfl := by
  change _ ≫ (_ ≫ _) = _
  erw [Iso.hom_inv_id_assoc]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.augmentedRelativeHomologySuccIso_connecting then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.augmentedRelativeHomologySuccIso_connecting"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.augmentedRelativeHomologySuccIso_connecting ``Submission.DifferentialGeometry.Homology.augmentedRelativeHomologySuccIso_connecting

end DifferentialGeometry.Homology
