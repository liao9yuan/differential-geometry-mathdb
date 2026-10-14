import Submission.DifferentialGeometry.Topology.Homology.SmallChains

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.Opposite _root_.Simplicial _root_.AlgebraicTopology

universe u

namespace DifferentialGeometry.Homology

variable (X : TopCat.{u}) (s : Set X)

local notation "A" => smallSingularSimplices X (fun _ : Unit ↦ s)
local notation "j" => TopCat.toSSet.map (TopCat.ofHom
  (ContinuousMap.mk Subtype.val (continuous_subtype_val : Continuous (Subtype.val : s → X))))


def singularSubspaceEquiv (n : SimplexCategoryᵒᵖ) :
    (TopCat.toSSet.obj (TopCat.of s)).obj n ≃ (A : SSet).obj n where
  toFun σ := ⟨(j).app n σ, by
    refine ⟨(), ?_⟩
    rintro _ ⟨z, rfl⟩
    exact (((TopCat.of s).toSSetObjEquiv n) σ z).property⟩
  invFun σ := ((TopCat.of s).toSSetObjEquiv n).symm
    ⟨fun z ↦ ⟨X.toSSetObjEquiv n σ.val z, σ.property.choose_spec ⟨z, rfl⟩⟩,
      (X.toSSetObjEquiv n σ.val).continuous.subtype_mk _⟩
  left_inv σ := by
    apply ((TopCat.of s).toSSetObjEquiv n).injective
    ext z
    rfl
  right_inv σ := by
    apply Subtype.ext
    apply (X.toSSetObjEquiv n).injective
    ext z
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubspaceEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubspaceEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubspaceEquiv ``Submission.DifferentialGeometry.Homology.singularSubspaceEquiv


def singularSubspaceIso : TopCat.toSSet.obj (TopCat.of s) ≅ (A : SSet) :=
  NatIso.ofComponents (fun n ↦ (singularSubspaceEquiv X s n).toIso) (by
    intro n m f
    ext σ
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((j).naturality f) σ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubspaceIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubspaceIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubspaceIso ``Submission.DifferentialGeometry.Homology.singularSubspaceIso


@[reassoc (attr := simp)]
theorem singularSubspaceIso_hom_ι :
    (singularSubspaceIso X s).hom ≫ (A).ι = (j) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubspaceIso_hom_ι then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubspaceIso_hom_ι"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubspaceIso_hom_ι ``Submission.DifferentialGeometry.Homology.singularSubspaceIso_hom_ι


@[reassoc (attr := simp)]
theorem singularSubspaceIso_inv_inclusion :
    (singularSubspaceIso X s).inv ≫ (j) = (A).ι := by
  rw [← singularSubspaceIso_hom_ι X s, Iso.inv_hom_id_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubspaceIso_inv_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubspaceIso_inv_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubspaceIso_inv_inclusion ``Submission.DifferentialGeometry.Homology.singularSubspaceIso_inv_inclusion

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


def singularSubspaceChainIso :
    (((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj (TopCat.of s)) ≅
      (A : SSet).chainComplex R :=
  ((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).mapIso (singularSubspaceIso X s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubspaceChainIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubspaceChainIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubspaceChainIso ``Submission.DifferentialGeometry.Homology.singularSubspaceChainIso


@[reassoc]
theorem ι_singularSubspaceChainIso_hom_f {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of s) _⦋n⦌) :
    (TopCat.toSSet.obj (TopCat.of s)).ιChainComplex σ ≫
        (singularSubspaceChainIso X s R).hom.f n =
      (A : SSet).ιChainComplex (singularSubspaceEquiv X s (_root_.Opposite.op ⦋n⦌) σ) :=
  SSet.ι_chainComplexMap_f _ _ _ R σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.ι_singularSubspaceChainIso_hom_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.ι_singularSubspaceChainIso_hom_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.ι_singularSubspaceChainIso_hom_f ``Submission.DifferentialGeometry.Homology.ι_singularSubspaceChainIso_hom_f


@[reassoc]
theorem ι_singularSubspaceChainIso_inv_f {n : ℕ} (σ : (A : SSet) _⦋n⦌) :
    (A : SSet).ιChainComplex σ ≫ (singularSubspaceChainIso X s R).inv.f n =
      (TopCat.toSSet.obj (TopCat.of s)).ιChainComplex
        ((singularSubspaceEquiv X s (_root_.Opposite.op ⦋n⦌)).symm σ) :=
  SSet.ι_chainComplexMap_f _ _ _ R σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.ι_singularSubspaceChainIso_inv_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.ι_singularSubspaceChainIso_inv_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.ι_singularSubspaceChainIso_inv_f ``Submission.DifferentialGeometry.Homology.ι_singularSubspaceChainIso_inv_f

@[reassoc (attr := simp)]
theorem singularSubspaceChainIso_hom_inclusion :
    (singularSubspaceChainIso X s R).hom ≫ smallChainMap X (fun _ : Unit ↦ s) R =
      ((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))) := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ =
    ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, singularSubspaceIso_hom_ι]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubspaceChainIso_hom_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubspaceChainIso_hom_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubspaceChainIso_hom_inclusion ``Submission.DifferentialGeometry.Homology.singularSubspaceChainIso_hom_inclusion


@[reassoc (attr := simp)]
theorem singularSubspaceChainIso_inv_inclusion :
    (singularSubspaceChainIso X s R).inv ≫
        ((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map
          (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X))) =
      smallChainMap X (fun _ : Unit ↦ s) R := by
  rw [← singularSubspaceChainIso_hom_inclusion X s R, Iso.inv_hom_id_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubspaceChainIso_inv_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubspaceChainIso_inv_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubspaceChainIso_inv_inclusion ``Submission.DifferentialGeometry.Homology.singularSubspaceChainIso_inv_inclusion

end DifferentialGeometry.Homology
