import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Submission.DifferentialGeometry.Topology.SphereSeparation.SphereComparison
import Submission.DifferentialGeometry.Topology.SphereSeparation.SpecializedDuality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Simplicial
open scoped _root_.Simplicial

namespace DifferentialGeometry.Topology.SphereSeparation



private noncomputable def integerSimplicialChainsEvalIso (n : ℕ) :
    ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ) ⋙
        HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n) ≅
      ((_root_.CategoryTheory.evaluation SimplexCategoryᵒᵖ Type).obj
        (Opposite.op (SimplexCategory.mk n))) ⋙
        sigmaConst.obj (ModuleCat.of ℤ ℤ) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.integerSimplicialChainsEvalIso
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.integerSimplicialChainsEvalIso target :: scope.openDecls } }

noncomputable instance integerSimplicialChains_preservesColimitsOfShape
    {J : Type} [_root_.CategoryTheory.Category J] :
    _root_.CategoryTheory.Limits.PreservesColimitsOfShape J
      ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun n => by
    exact _root_.CategoryTheory.Limits.preservesColimitsOfShape_of_natIso
      (integerSimplicialChainsEvalIso n).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.integerSimplicialChains_preservesColimitsOfShape then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.integerSimplicialChains_preservesColimitsOfShape"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.integerSimplicialChains_preservesColimitsOfShape ``Submission.DifferentialGeometry.Topology.SphereSeparation.integerSimplicialChains_preservesColimitsOfShape

theorem integerChains_isPushout_of_subcomplex_bicartSq
    {X : SSet} {A₁ A₂ A₃ A₄ : X.Subcomplex}
    (sq : SSet.Subcomplex.BicartSq A₁ A₂ A₃ A₄) :
    _root_.CategoryTheory.IsPushout
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₁₂)
        (ModuleCat.of ℤ ℤ))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₁₃)
        (ModuleCat.of ℤ ℤ))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₂₄)
        (ModuleCat.of ℤ ℤ))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₃₄)
        (ModuleCat.of ℤ ℤ)) :=
  (sq.isPushout.map
    ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.integerChains_isPushout_of_subcomplex_bicartSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.integerChains_isPushout_of_subcomplex_bicartSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.integerChains_isPushout_of_subcomplex_bicartSq ``Submission.DifferentialGeometry.Topology.SphereSeparation.integerChains_isPushout_of_subcomplex_bicartSq

theorem integerChains_isPushout_inf_sup
    {X : SSet} (A B : X.Subcomplex) :
    _root_.CategoryTheory.IsPushout
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
        (ModuleCat.of ℤ ℤ))
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))
        (ModuleCat.of ℤ ℤ))
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))
        (ModuleCat.of ℤ ℤ))
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B))
        (ModuleCat.of ℤ ℤ)) :=
  integerChains_isPushout_of_subcomplex_bicartSq
    ({ sup_eq := rfl, inf_eq := rfl } :
      SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.integerChains_isPushout_inf_sup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.integerChains_isPushout_inf_sup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.integerChains_isPushout_inf_sup ``Submission.DifferentialGeometry.Topology.SphereSeparation.integerChains_isPushout_inf_sup

theorem mono_integerSimplicialChainMap
    {X Y : SSet} (f : X ⟶ Y) [_root_.CategoryTheory.Mono f] :
    Mono (SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)) := by
  dsimp [SSet.chainComplexMap, SSet.chainComplexFunctor,
    AlgebraicTopology.singularChainComplexFunctor]
  apply +allowSynthFailures Functor.map_mono
  apply +allowSynthFailures Functor.map_mono
  dsimp [SSet, SimplicialObject.whiskering, _root_.CategoryTheory.SimplicialObject]
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.mono_integerSimplicialChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.mono_integerSimplicialChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.mono_integerSimplicialChainMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.mono_integerSimplicialChainMap

theorem integerChains_mayerVietoris_shortExact
    {X : SSet} (A B : X.Subcomplex) :
    (integerChains_isPushout_inf_sup A B).shortComplex.ShortExact := by
  let h := integerChains_isPushout_inf_sup A B
  let _ : _root_.CategoryTheory.Mono
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
        (ModuleCat.of ℤ ℤ)) :=
    mono_integerSimplicialChainMap _
  apply ShortComplex.ShortExact.mk'
  · exact h.exact_shortComplex
  · change _root_.CategoryTheory.Mono (biprod.lift
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
        (ModuleCat.of ℤ ℤ))
      (-SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))
        (ModuleCat.of ℤ ℤ)))
    infer_instance
  · exact h.epi_shortComplex_g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.integerChains_mayerVietoris_shortExact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.integerChains_mayerVietoris_shortExact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.integerChains_mayerVietoris_shortExact ``Submission.DifferentialGeometry.Topology.SphereSeparation.integerChains_mayerVietoris_shortExact

noncomputable def integerChainsRelativeUnionComparison
    {X : SSet} (A B : X.Subcomplex) :
    _root_.CategoryTheory.Limits.cokernel
        (SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))
          (ModuleCat.of ℤ ℤ)) ⟶
      _root_.CategoryTheory.Limits.cokernel
        (SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))
          (ModuleCat.of ℤ ℤ)) :=
  let h := integerChains_isPushout_inf_sup A B
  cokernel.map _ _
    (SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
      (ModuleCat.of ℤ ℤ))
    (SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B))
      (ModuleCat.of ℤ ℤ)) h.w.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.integerChainsRelativeUnionComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.integerChainsRelativeUnionComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.integerChainsRelativeUnionComparison ``Submission.DifferentialGeometry.Topology.SphereSeparation.integerChainsRelativeUnionComparison

theorem isIso_integerChainsRelativeUnionComparison
    {X : SSet} (A B : X.Subcomplex) :
    IsIso (integerChainsRelativeUnionComparison A B) := by
  let h := (integerChains_isPushout_inf_sup A B).flip
  exact _root_.CategoryTheory.Limits.isIso_cokernel_map_of_isPushout h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isIso_integerChainsRelativeUnionComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isIso_integerChainsRelativeUnionComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isIso_integerChainsRelativeUnionComparison ``Submission.DifferentialGeometry.Topology.SphereSeparation.isIso_integerChainsRelativeUnionComparison

noncomputable def integerChainsRelativeUnionIso
    {X : SSet} (A B : X.Subcomplex) :
    _root_.CategoryTheory.Limits.cokernel
        (SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))
          (ModuleCat.of ℤ ℤ)) ≅
      _root_.CategoryTheory.Limits.cokernel
        (SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))
          (ModuleCat.of ℤ ℤ)) := by
  let _ := isIso_integerChainsRelativeUnionComparison A B
  exact _root_.CategoryTheory.asIso (integerChainsRelativeUnionComparison A B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.integerChainsRelativeUnionIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.integerChainsRelativeUnionIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.integerChainsRelativeUnionIso ``Submission.DifferentialGeometry.Topology.SphereSeparation.integerChainsRelativeUnionIso



theorem mem_range_toSSet_subspace_iff
    {X : Type} [TopologicalSpace X] (A : Set X)
    {n : SimplexCategoryᵒᵖ}
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj n) :
    s ∈ (SSet.Subcomplex.range
        (TopCat.toSSet.map (topologicalSubspaceInclusion A))).obj n ↔
      Set.range (TopCat.toSSetObjEquiv (TopCat.of X) n s) ⊆ A := by
  constructor
  · rintro ⟨t, rfl⟩ x ⟨z, rfl⟩
    exact (TopCat.toSSetObjEquiv (TopCat.of A) n t z).2
  · intro hs
    let t : C(stdSimplex ℝ (Fin (n.unop.len + 1)), A) :=
      ⟨fun z ↦ ⟨TopCat.toSSetObjEquiv (TopCat.of X) n s z,
          hs ⟨z, rfl⟩⟩,
        (TopCat.toSSetObjEquiv (TopCat.of X) n s).continuous.subtype_mk _⟩
    refine ⟨(TopCat.toSSetObjEquiv (TopCat.of A) n).symm t, ?_⟩
    apply (TopCat.toSSetObjEquiv (TopCat.of X) n).injective
    apply ContinuousMap.ext
    intro z
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.mem_range_toSSet_subspace_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.mem_range_toSSet_subspace_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.mem_range_toSSet_subspace_iff ``Submission.DifferentialGeometry.Topology.SphereSeparation.mem_range_toSSet_subspace_iff

theorem range_toSSet_subspace_inter
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    SSet.Subcomplex.range
        (TopCat.toSSet.map (topologicalSubspaceInclusion (A ∩ B))) =
      SSet.Subcomplex.range
          (TopCat.toSSet.map (topologicalSubspaceInclusion A)) ⊓
        SSet.Subcomplex.range
          (TopCat.toSSet.map (topologicalSubspaceInclusion B)) := by
  ext n s
  rw [mem_range_toSSet_subspace_iff]
  rw [Subfunctor.min_obj, Set.mem_inter_iff,
    mem_range_toSSet_subspace_iff, mem_range_toSSet_subspace_iff]
  constructor
  · intro hs
    exact ⟨fun x hx ↦ (hs hx).1, fun x hx ↦ (hs hx).2⟩
  · rintro ⟨hsA, hsB⟩ x hx
    exact ⟨hsA hx, hsB hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.range_toSSet_subspace_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.range_toSSet_subspace_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.range_toSSet_subspace_inter ``Submission.DifferentialGeometry.Topology.SphereSeparation.range_toSSet_subspace_inter

noncomputable def singularChainsSubspaceRangeIso
    {X : Type} [TopologicalSpace X] (A : Set X) :
    integerSingularChains (TopCat.of A) ≅
      ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
        (SSet.Subcomplex.range
          (TopCat.toSSet.map (topologicalSubspaceInclusion A))) := by
  let i := topologicalSubspaceInclusion A
  letI : _root_.CategoryTheory.Mono i := (TopCat.mono_iff_injective i).2 Subtype.val_injective
  letI : _root_.CategoryTheory.Mono (TopCat.toSSet.map i) := by apply Functor.map_mono
  exact ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).mapIso
      (_root_.CategoryTheory.asIso (SSet.Subcomplex.toRange (TopCat.toSSet.map i)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularChainsSubspaceRangeIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularChainsSubspaceRangeIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularChainsSubspaceRangeIso ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularChainsSubspaceRangeIso

noncomputable def singularChainsIntersectionInfIso
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    integerSingularChains (TopCat.of (A ∩ B : Set X)) ≅
      ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
        ((SSet.Subcomplex.range
              (TopCat.toSSet.map (topologicalSubspaceInclusion A)) ⊓
            SSet.Subcomplex.range
              (TopCat.toSSet.map (topologicalSubspaceInclusion B))) :
          (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) :=
  singularChainsSubspaceRangeIso (A ∩ B) ≪≫
    ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).mapIso
        (SSet.Subcomplex.eqToIso (range_toSSet_subspace_inter A B))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionInfIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionInfIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionInfIso ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionInfIso

noncomputable abbrev singularSubspaceRange
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (TopCat.toSSet.obj (TopCat.of X)).Subcomplex :=
  SSet.Subcomplex.range
    (TopCat.toSSet.map (topologicalSubspaceInclusion A))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularSubspaceRange then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularSubspaceRange"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularSubspaceRange ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularSubspaceRange

noncomputable def singularChainsIntersectionToLeft
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    integerSingularChains (TopCat.of (A ∩ B : Set X)) ⟶
      integerSingularChains (TopCat.of A) :=
  (singularChainsIntersectionInfIso A B).hom ≫
    SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE
        (inf_le_left : singularSubspaceRange (A := A) ⊓
          singularSubspaceRange (A := B) ≤ singularSubspaceRange (A := A)))
      (ModuleCat.of ℤ ℤ) ≫
    (singularChainsSubspaceRangeIso A).inv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionToLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionToLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionToLeft ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionToLeft

noncomputable def singularChainsIntersectionToRight
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    integerSingularChains (TopCat.of (A ∩ B : Set X)) ⟶
      integerSingularChains (TopCat.of B) :=
  (singularChainsIntersectionInfIso A B).hom ≫
    SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE
        (inf_le_right : singularSubspaceRange (A := A) ⊓
          singularSubspaceRange (A := B) ≤ singularSubspaceRange (A := B)))
      (ModuleCat.of ℤ ℤ) ≫
    (singularChainsSubspaceRangeIso B).inv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionToRight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionToRight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionToRight ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularChainsIntersectionToRight

noncomputable def singularChainsLeftToSmall
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    integerSingularChains (TopCat.of A) ⟶
      ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
        (((singularSubspaceRange (A := A) ⊔ singularSubspaceRange (A := B)) :
          (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet) :=
  (singularChainsSubspaceRangeIso A).hom ≫
    SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE
        (le_sup_left : singularSubspaceRange (A := A) ≤
          singularSubspaceRange (A := A) ⊔ singularSubspaceRange (A := B)))
      (ModuleCat.of ℤ ℤ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularChainsLeftToSmall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularChainsLeftToSmall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularChainsLeftToSmall ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularChainsLeftToSmall

noncomputable def singularChainsRightToSmall
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    integerSingularChains (TopCat.of B) ⟶
      ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
        (((singularSubspaceRange (A := A) ⊔ singularSubspaceRange (A := B)) :
          (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet) :=
  (singularChainsSubspaceRangeIso B).hom ≫
    SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE
        (le_sup_right : singularSubspaceRange (A := B) ≤
          singularSubspaceRange (A := A) ⊔ singularSubspaceRange (A := B)))
      (ModuleCat.of ℤ ℤ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularChainsRightToSmall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularChainsRightToSmall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularChainsRightToSmall ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularChainsRightToSmall

theorem integerSingularChains_isPushout_subspaces
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    _root_.CategoryTheory.IsPushout
      (singularChainsIntersectionToLeft A B)
      (singularChainsIntersectionToRight A B)
      (singularChainsLeftToSmall A B)
      (singularChainsRightToSmall A B) := by
  let h := integerChains_isPushout_inf_sup
    (singularSubspaceRange (A := A)) (singularSubspaceRange (A := B))
  apply h.of_iso'
    (singularChainsIntersectionInfIso A B)
    (singularChainsSubspaceRangeIso A)
    (singularChainsSubspaceRangeIso B)
    (Iso.refl _)
  · simp [singularChainsIntersectionToLeft]
  · simp [singularChainsIntersectionToRight]
  · dsimp [singularChainsLeftToSmall]
    rw [Category.comp_id]
  · dsimp [singularChainsRightToSmall]
    rw [Category.comp_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.integerSingularChains_isPushout_subspaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.integerSingularChains_isPushout_subspaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.integerSingularChains_isPushout_subspaces ``Submission.DifferentialGeometry.Topology.SphereSeparation.integerSingularChains_isPushout_subspaces

theorem integerSingularChains_mayerVietoris_shortExact_subspaces
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    (integerSingularChains_isPushout_subspaces A B).shortComplex.ShortExact := by
  let iLeft := SSet.Subcomplex.homOfLE
    (inf_le_left : singularSubspaceRange (A := A) ⊓
      singularSubspaceRange (A := B) ≤ singularSubspaceRange (A := A))
  let _ : _root_.CategoryTheory.Mono (SSet.chainComplexMap iLeft (ModuleCat.of ℤ ℤ)) :=
    mono_integerSimplicialChainMap iLeft
  let _ : _root_.CategoryTheory.Mono (singularChainsIntersectionToLeft A B) := by
    dsimp [singularChainsIntersectionToLeft]
    infer_instance
  let h := integerSingularChains_isPushout_subspaces A B
  apply ShortComplex.ShortExact.mk'
  · exact h.exact_shortComplex
  · change _root_.CategoryTheory.Mono (biprod.lift
      (singularChainsIntersectionToLeft A B)
      (-singularChainsIntersectionToRight A B))
    infer_instance
  · exact h.epi_shortComplex_g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.integerSingularChains_mayerVietoris_shortExact_subspaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.integerSingularChains_mayerVietoris_shortExact_subspaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.integerSingularChains_mayerVietoris_shortExact_subspaces ``Submission.DifferentialGeometry.Topology.SphereSeparation.integerSingularChains_mayerVietoris_shortExact_subspaces




theorem isOpen_sphereTwoPuncture (p : SphereTwo) :
    IsOpen ({p}ᶜ : Set SphereTwo) :=
  isClosed_singleton.isOpen_compl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isOpen_sphereTwoPuncture then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isOpen_sphereTwoPuncture"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isOpen_sphereTwoPuncture ``Submission.DifferentialGeometry.Topology.SphereSeparation.isOpen_sphereTwoPuncture


theorem sphereTwoPunctureCover
    {p q : SphereTwo} (hpq : p ≠ q) :
    ({p}ᶜ : Set SphereTwo) ∪ {q}ᶜ = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff,
    Set.mem_univ, iff_true]
  by_cases hxp : x = p
  · exact Or.inr (by simpa [hxp] using hpq)
  · exact Or.inl hxp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sphereTwoPunctureCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sphereTwoPunctureCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sphereTwoPunctureCover ``Submission.DifferentialGeometry.Topology.SphereSeparation.sphereTwoPunctureCover

theorem sphereTwoPuncture_inter
    (p q : SphereTwo) :
    ({p}ᶜ : Set SphereTwo) ∩ {q}ᶜ = ({p, q} : Set SphereTwo)ᶜ := by
  ext x
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sphereTwoPuncture_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sphereTwoPuncture_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sphereTwoPuncture_inter ``Submission.DifferentialGeometry.Topology.SphereSeparation.sphereTwoPuncture_inter

theorem sphereTwoPunctureCover_mayerVietoris_shortExact
    (p q : SphereTwo) :
    (integerSingularChains_isPushout_subspaces
      ({p}ᶜ : Set SphereTwo) {q}ᶜ).shortComplex.ShortExact :=
  integerSingularChains_mayerVietoris_shortExact_subspaces _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sphereTwoPunctureCover_mayerVietoris_shortExact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sphereTwoPunctureCover_mayerVietoris_shortExact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sphereTwoPunctureCover_mayerVietoris_shortExact ``Submission.DifferentialGeometry.Topology.SphereSeparation.sphereTwoPunctureCover_mayerVietoris_shortExact

end DifferentialGeometry.Topology.SphereSeparation
