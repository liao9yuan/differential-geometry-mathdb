import Submission.DifferentialGeometry.Topology.SimplicialSet.RealizationHomology
import Submission.DifferentialGeometry.Topology.SimplicialSet.ChainColimits
import Submission.DifferentialGeometry.Topology.Homology.Relative.Map
import Submission.DifferentialGeometry.Topology.Homology.Algebra.CokernelQuasiIso
import Mathlib.Topology.Homeomorph.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.Topology

universe u

namespace DifferentialGeometry.SSet

variable {A B X Y : _root_.SSet.{u}}


def realizationToRange (f : A ⟶ X) :
    _root_.SSet.toTop.obj A ⟶ TopCat.of (Set.range (_root_.SSet.toTop.map f)) :=
  TopCat.ofHom ⟨fun a ↦ ⟨(_root_.SSet.toTop.map f) a, ⟨a, rfl⟩⟩,
    (_root_.SSet.toTop.map f).hom.continuous.subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.realizationToRange then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.realizationToRange"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.realizationToRange ``Submission.DifferentialGeometry.SSet.realizationToRange


@[reassoc (attr := simp)]
theorem realizationToRange_inclusion (f : A ⟶ X) :
    realizationToRange f ≫
      TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
        C(Set.range (_root_.SSet.toTop.map f), _root_.SSet.toTop.obj X)) =
      _root_.SSet.toTop.map f := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.realizationToRange_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.realizationToRange_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.realizationToRange_inclusion ``Submission.DifferentialGeometry.SSet.realizationToRange_inclusion


theorem isIso_realizationToRange (f : A ⟶ X) (hf : _root_.Topology.IsEmbedding (_root_.SSet.toTop.map f)) :
    IsIso (realizationToRange f) := by
  let e : _root_.SSet.toTop.obj A ≅ TopCat.of (Set.range (_root_.SSet.toTop.map f)) :=
    TopCat.isoOfHomeo hf.toHomeomorph
  change _root_.CategoryTheory.IsIso e.hom
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.isIso_realizationToRange then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.isIso_realizationToRange"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.isIso_realizationToRange ``Submission.DifferentialGeometry.SSet.isIso_realizationToRange

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

theorem relativeRealizationSquare (f : A ⟶ X) :
    _root_.SSet.chainComplexMap f R ≫ realizationChainMap X R =
      (realizationChainMap A R ≫
        ((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map (realizationToRange f)) ≫
      DifferentialGeometry.Homology.relativeInclusion (_root_.SSet.toTop.obj X)
        (Set.range (_root_.SSet.toTop.map f)) R := by
  rw [realizationChainMap_naturality]
  unfold DifferentialGeometry.Homology.relativeInclusion
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, realizationToRange_inclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.relativeRealizationSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.relativeRealizationSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.relativeRealizationSquare ``Submission.DifferentialGeometry.SSet.relativeRealizationSquare

def relativeRealizationChainMap (f : A ⟶ X) :
    _root_.CategoryTheory.Limits.cokernel (_root_.SSet.chainComplexMap f R) ⟶
      DifferentialGeometry.Homology.relativeChainComplex (_root_.SSet.toTop.obj X)
        (Set.range (_root_.SSet.toTop.map f)) R :=
  cokernel.map (_root_.SSet.chainComplexMap f R)
    (DifferentialGeometry.Homology.relativeInclusion (_root_.SSet.toTop.obj X)
      (Set.range (_root_.SSet.toTop.map f)) R)
    (realizationChainMap A R ≫
      ((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map (realizationToRange f))
    (realizationChainMap X R) (relativeRealizationSquare R f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.relativeRealizationChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.relativeRealizationChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.relativeRealizationChainMap ``Submission.DifferentialGeometry.SSet.relativeRealizationChainMap

@[reassoc (attr := simp)]
theorem relativeRealizationProjection (f : A ⟶ X) :
    cokernel.π (_root_.SSet.chainComplexMap f R) ≫ relativeRealizationChainMap R f =
      realizationChainMap X R ≫ DifferentialGeometry.Homology.relativeProjection (_root_.SSet.toTop.obj X)
        (Set.range (_root_.SSet.toTop.map f)) R :=
  cokernel.π_desc _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.relativeRealizationProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.relativeRealizationProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.relativeRealizationProjection ``Submission.DifferentialGeometry.SSet.relativeRealizationProjection

theorem quasiIso_relativeRealizationChainMap (f : A ⟶ X) [_root_.CategoryTheory.Mono f]
    (hf : _root_.Topology.IsEmbedding (_root_.SSet.toTop.map f))
    (hA : QuasiIso (realizationChainMap A R)) (hX : QuasiIso (realizationChainMap X R)) :
    QuasiIso (relativeRealizationChainMap R f) := by
  have : _root_.CategoryTheory.Mono (_root_.SSet.chainComplexMap f R) := by
    unfold _root_.SSet.chainComplexMap
    infer_instance
  have : _root_.CategoryTheory.IsIso (realizationToRange f) := isIso_realizationToRange f hf
  have : QuasiIso (realizationChainMap A R) := hA
  unfold relativeRealizationChainMap
  exact DifferentialGeometry.HomologicalComplex.quasiIso_cokernel_map _ _ _ _ _
    (quasiIso_comp (realizationChainMap A R)
      (((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map (realizationToRange f))) hX

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.quasiIso_relativeRealizationChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.quasiIso_relativeRealizationChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.quasiIso_relativeRealizationChainMap ``Submission.DifferentialGeometry.SSet.quasiIso_relativeRealizationChainMap

def relativeRealizationShortComplexMap (f : A ⟶ X) :
    DifferentialGeometry.HomologicalComplex.cokernelSequence (_root_.SSet.chainComplexMap f R) ⟶
      DifferentialGeometry.Homology.relativeShortComplex (_root_.SSet.toTop.obj X)
        (Set.range (_root_.SSet.toTop.map f)) R where
  τ₁ := realizationChainMap A R ≫
    ((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map (realizationToRange f)
  τ₂ := realizationChainMap X R
  τ₃ := relativeRealizationChainMap R f
  comm₁₂ := (relativeRealizationSquare R f).symm
  comm₂₃ := (relativeRealizationProjection R f).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.relativeRealizationShortComplexMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.relativeRealizationShortComplexMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.relativeRealizationShortComplexMap ``Submission.DifferentialGeometry.SSet.relativeRealizationShortComplexMap

variable {f : A ⟶ X} {g : B ⟶ Y} {a : A ⟶ B} {b : X ⟶ Y}
  (w : f ≫ b = a ≫ g)

include w


theorem simplicialChainSquare :
    _root_.SSet.chainComplexMap f R ≫ _root_.SSet.chainComplexMap b R =
      _root_.SSet.chainComplexMap a R ≫ _root_.SSet.chainComplexMap g R := by
  change (((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).map f) ≫
      (((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).map b) =
    (((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).map a) ≫
      (((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).map g)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, w]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.simplicialChainSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.simplicialChainSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.simplicialChainSquare ``Submission.DifferentialGeometry.SSet.simplicialChainSquare


def relativeSimplicialChainMap :
    cokernel (_root_.SSet.chainComplexMap f R) ⟶ _root_.CategoryTheory.Limits.cokernel (_root_.SSet.chainComplexMap g R) :=
  cokernel.map _ _ (_root_.SSet.chainComplexMap a R) (_root_.SSet.chainComplexMap b R)
    (simplicialChainSquare R w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.relativeSimplicialChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.relativeSimplicialChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.relativeSimplicialChainMap ``Submission.DifferentialGeometry.SSet.relativeSimplicialChainMap


@[reassoc (attr := simp)]
theorem relativeSimplicialProjection :
    cokernel.π (_root_.SSet.chainComplexMap f R) ≫ relativeSimplicialChainMap R w =
      _root_.SSet.chainComplexMap b R ≫ cokernel.π (_root_.SSet.chainComplexMap g R) :=
  cokernel.π_desc _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.relativeSimplicialProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.relativeSimplicialProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.relativeSimplicialProjection ``Submission.DifferentialGeometry.SSet.relativeSimplicialProjection


theorem realizationRange_mapsTo :
    Set.MapsTo (_root_.SSet.toTop.map b) (Set.range (_root_.SSet.toTop.map f))
      (Set.range (_root_.SSet.toTop.map g)) := by
  rintro x ⟨z, rfl⟩
  have hw := congrArg (fun v ↦ _root_.SSet.toTop.map v) w
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hw
  exact ⟨(_root_.SSet.toTop.map a) z, (ConcreteCategory.congr_hom hw z).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.realizationRange_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.realizationRange_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.realizationRange_mapsTo ``Submission.DifferentialGeometry.SSet.realizationRange_mapsTo

theorem relativeRealizationChainMap_naturality :
    relativeSimplicialChainMap R w ≫ relativeRealizationChainMap R g =
      relativeRealizationChainMap R f ≫
        DifferentialGeometry.Homology.relativeChainMap R (_root_.SSet.toTop.map b)
          (realizationRange_mapsTo w) := by
  apply (_root_.CategoryTheory.cancel_epi (cokernel.π (_root_.SSet.chainComplexMap f R))).mp
  simp only [relativeSimplicialProjection_assoc, relativeRealizationProjection,
    relativeRealizationProjection_assoc,
    DifferentialGeometry.Homology.relativeProjection_chainMap]
  exact congrArg (fun v ↦ v ≫ DifferentialGeometry.Homology.relativeProjection (_root_.SSet.toTop.obj Y)
      (Set.range (_root_.SSet.toTop.map g)) R) (realizationChainMap_naturality b R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.relativeRealizationChainMap_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.relativeRealizationChainMap_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.relativeRealizationChainMap_naturality ``Submission.DifferentialGeometry.SSet.relativeRealizationChainMap_naturality

end DifferentialGeometry.SSet
