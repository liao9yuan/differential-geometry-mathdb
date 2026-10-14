import Submission.DifferentialGeometry.Topology.SphereSeparation.SubdivisionPrism
import Submission.DifferentialGeometry.Topology.SphereSeparation.SpecializedDuality
import Submission.DifferentialGeometry.Topology.SphereSeparation.LocallyNilpotentHomotopy
import Submission.DifferentialGeometry.Topology.SphereSeparation.SubdivisionSmallness

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

private noncomputable abbrev AmbientChains (X : TopCat) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  integerSingularChainComplex X

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.AmbientChains
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.AmbientChains target :: scope.openDecls } }

noncomputable def leftToSmallSingularSubcomplex
    (X : TopCat) (V W : Set X) :
    TopCat.toSSet.obj (TopCat.of V) ⟶ (smallSingularSubcomplex X V W : SSet) :=
  SSet.Subcomplex.lift
    (TopCat.toSSet.map (topologicalSubspaceInclusion V))
    (show SSet.Subcomplex.range
          (TopCat.toSSet.map (topologicalSubspaceInclusion V)) ≤
        smallSingularSubcomplex X V W by
      exact le_sup_left)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.leftToSmallSingularSubcomplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.leftToSmallSingularSubcomplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.leftToSmallSingularSubcomplex ``Submission.DifferentialGeometry.Topology.SphereSeparation.leftToSmallSingularSubcomplex

noncomputable def rightToSmallSingularSubcomplex
    (X : TopCat) (V W : Set X) :
    TopCat.toSSet.obj (TopCat.of W) ⟶ (smallSingularSubcomplex X V W : SSet) :=
  SSet.Subcomplex.lift
    (TopCat.toSSet.map (topologicalSubspaceInclusion W))
    (show SSet.Subcomplex.range
          (TopCat.toSSet.map (topologicalSubspaceInclusion W)) ≤
        smallSingularSubcomplex X V W by
      exact le_sup_right)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.rightToSmallSingularSubcomplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.rightToSmallSingularSubcomplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.rightToSmallSingularSubcomplex ``Submission.DifferentialGeometry.Topology.SphereSeparation.rightToSmallSingularSubcomplex

@[reassoc (attr := simp)]
theorem leftToSmallSingularSubcomplex_comp_inclusion
    (X : TopCat) (V W : Set X) :
    leftToSmallSingularSubcomplex X V W ≫
        (smallSingularSubcomplex X V W).ι =
      TopCat.toSSet.map (topologicalSubspaceInclusion V) := by
  exact SSet.Subcomplex.lift_ι _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.leftToSmallSingularSubcomplex_comp_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.leftToSmallSingularSubcomplex_comp_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.leftToSmallSingularSubcomplex_comp_inclusion ``Submission.DifferentialGeometry.Topology.SphereSeparation.leftToSmallSingularSubcomplex_comp_inclusion

@[reassoc (attr := simp)]
theorem rightToSmallSingularSubcomplex_comp_inclusion
    (X : TopCat) (V W : Set X) :
    rightToSmallSingularSubcomplex X V W ≫
        (smallSingularSubcomplex X V W).ι =
      TopCat.toSSet.map (topologicalSubspaceInclusion W) := by
  exact SSet.Subcomplex.lift_ι _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.rightToSmallSingularSubcomplex_comp_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.rightToSmallSingularSubcomplex_comp_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.rightToSmallSingularSubcomplex_comp_inclusion ``Submission.DifferentialGeometry.Topology.SphereSeparation.rightToSmallSingularSubcomplex_comp_inclusion


noncomputable def smallBarycentricPiece
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (smallSingularSubcomplex X V W : SSet) _⦋n⦌)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (smallSingularSubcomplex X V W : SSet) _⦋n⦌ := by
  refine ⟨barycentricPieceOfSingularSimplex X s.1 σ, ?_⟩
  rcases s.2 with hs | hs
  · rcases hs with ⟨t, ht⟩
    apply Or.inl
    refine ⟨barycentricPieceOfSingularSimplex (TopCat.of V) t σ, ?_⟩
    rw [barycentricPieceOfSingularSimplex_naturality, ht]
  · rcases hs with ⟨t, ht⟩
    apply Or.inr
    refine ⟨barycentricPieceOfSingularSimplex (TopCat.of W) t σ, ?_⟩
    rw [barycentricPieceOfSingularSimplex_naturality, ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricPiece then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallBarycentricPiece"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricPiece ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricPiece

@[simp]
theorem smallBarycentricPiece_val
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (smallSingularSubcomplex X V W : SSet) _⦋n⦌)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (smallBarycentricPiece X V W s σ).1 =
      barycentricPieceOfSingularSimplex X s.1 σ :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricPiece_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallBarycentricPiece_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricPiece_val ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricPiece_val

noncomputable def smallBarycentricSubdivisionDegreeMap
    (X : TopCat) (V W : Set X) (n : ℕ) :
    (smallSingularChainComplex X V W).X n ⟶
      (smallSingularChainComplex X V W).X n :=
  Sigma.desc fun s =>
    ∑ σ : Equiv.Perm (Fin (n + 1)),
      (Equiv.Perm.sign σ : ℤ) •
        (smallSingularSubcomplex X V W : SSet).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) (smallBarycentricPiece X V W s σ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDegreeMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDegreeMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDegreeMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDegreeMap

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ιChainComplex_smallBarycentricSubdivisionDegreeMap
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (smallSingularSubcomplex X V W : SSet) _⦋n⦌) :
    (smallSingularSubcomplex X V W : SSet).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s ≫
        smallBarycentricSubdivisionDegreeMap X V W n =
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        (Equiv.Perm.sign σ : ℤ) •
          (smallSingularSubcomplex X V W : SSet).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) (smallBarycentricPiece X V W s σ) := by
  dsimp [smallBarycentricSubdivisionDegreeMap, SSet.ιChainComplex]
  rw [Sigma.ι_desc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ιChainComplex_smallBarycentricSubdivisionDegreeMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ιChainComplex_smallBarycentricSubdivisionDegreeMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ιChainComplex_smallBarycentricSubdivisionDegreeMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.ιChainComplex_smallBarycentricSubdivisionDegreeMap

set_option backward.isDefEq.respectTransparency false in
theorem smallBarycentricSubdivisionDegreeMap_comp_inclusion
    (X : TopCat) (V W : Set X) (n : ℕ) :
    smallBarycentricSubdivisionDegreeMap X V W n ≫
        (smallSingularChainInclusion X V W).f n =
      (smallSingularChainInclusion X V W).f n ≫
        (signedBarycentricSubdivisionChainEndomorphism X).f n := by
  change smallBarycentricSubdivisionDegreeMap X V W n ≫
        (SSet.chainComplexMap (smallSingularSubcomplex X V W).ι
          (ModuleCat.of ℤ ℤ)).f n =
      (SSet.chainComplexMap (smallSingularSubcomplex X V W).ι
          (ModuleCat.of ℤ ℤ)).f n ≫
        barycentricSubdivisionDegreeMap X n
  apply SSet.chainComplex_hom_ext
  intro s
  rw [← Category.assoc,
    ιChainComplex_smallBarycentricSubdivisionDegreeMap,
    Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, SSet.ι_chainComplexMap_f]
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  rw [ιChainComplex_barycentricSubdivisionDegreeMap]
  apply Finset.sum_congr rfl
  intro σ _
  congr 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDegreeMap_comp_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDegreeMap_comp_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDegreeMap_comp_inclusion ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDegreeMap_comp_inclusion

noncomputable def smallBarycentricSubdivisionChainEndomorphism
    (X : TopCat) (V W : Set X) :
    smallSingularChainComplex X V W ⟶
      smallSingularChainComplex X V W where
  f n := smallBarycentricSubdivisionDegreeMap X V W n
  comm' i j hij := by
    obtain rfl : i = j + 1 := by simpa using hij.symm
    let _ : _root_.CategoryTheory.Mono (smallSingularChainInclusion X V W) :=
      mono_smallSingularChainInclusion X V W
    apply (_root_.CategoryTheory.cancel_mono ((smallSingularChainInclusion X V W).f j)).1
    calc
      (smallBarycentricSubdivisionDegreeMap X V W (j + 1) ≫
          (smallSingularChainComplex X V W).d (j + 1) j) ≫
            (smallSingularChainInclusion X V W).f j =
        smallBarycentricSubdivisionDegreeMap X V W (j + 1) ≫
          ((smallSingularChainComplex X V W).d (j + 1) j ≫
            (smallSingularChainInclusion X V W).f j) := by
              simp only [Category.assoc]
      _ = smallBarycentricSubdivisionDegreeMap X V W (j + 1) ≫
          ((smallSingularChainInclusion X V W).f (j + 1) ≫
            (integerSingularChainComplex X).d (j + 1) j) := by
              rw [← (smallSingularChainInclusion X V W).comm (j + 1) j]
      _ = (smallBarycentricSubdivisionDegreeMap X V W (j + 1) ≫
            (smallSingularChainInclusion X V W).f (j + 1)) ≫
          (integerSingularChainComplex X).d (j + 1) j := by
              simp only [Category.assoc]
      _ = ((smallSingularChainInclusion X V W).f (j + 1) ≫
            (signedBarycentricSubdivisionChainEndomorphism X).f (j + 1)) ≫
          (integerSingularChainComplex X).d (j + 1) j := by
              rw [smallBarycentricSubdivisionDegreeMap_comp_inclusion]
      _ = (smallSingularChainInclusion X V W).f (j + 1) ≫
          ((signedBarycentricSubdivisionChainEndomorphism X).f (j + 1) ≫
            (integerSingularChainComplex X).d (j + 1) j) := by
              simp only [Category.assoc]
      _ = (smallSingularChainInclusion X V W).f (j + 1) ≫
          ((integerSingularChainComplex X).d (j + 1) j ≫
            (signedBarycentricSubdivisionChainEndomorphism X).f j) := by
              rw [(signedBarycentricSubdivisionChainEndomorphism X).comm
                (j + 1) j]
      _ = ((smallSingularChainInclusion X V W).f (j + 1) ≫
            (integerSingularChainComplex X).d (j + 1) j) ≫
          (signedBarycentricSubdivisionChainEndomorphism X).f j := by
              simp only [Category.assoc]
      _ = ((smallSingularChainComplex X V W).d (j + 1) j ≫
            (smallSingularChainInclusion X V W).f j) ≫
          (signedBarycentricSubdivisionChainEndomorphism X).f j := by
              rw [(smallSingularChainInclusion X V W).comm (j + 1) j]
      _ = (smallSingularChainComplex X V W).d (j + 1) j ≫
          ((smallSingularChainInclusion X V W).f j ≫
            (signedBarycentricSubdivisionChainEndomorphism X).f j) := by
              simp only [Category.assoc]
      _ = (smallSingularChainComplex X V W).d (j + 1) j ≫
          (smallBarycentricSubdivisionDegreeMap X V W j ≫
            (smallSingularChainInclusion X V W).f j) := by
              rw [smallBarycentricSubdivisionDegreeMap_comp_inclusion]
      _ = ((smallSingularChainComplex X V W).d (j + 1) j ≫
            smallBarycentricSubdivisionDegreeMap X V W j) ≫
          (smallSingularChainInclusion X V W).f j := by
              simp only [Category.assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionChainEndomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionChainEndomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionChainEndomorphism ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionChainEndomorphism

theorem smallBarycentricSubdivisionChainEndomorphism_comp_inclusion
    (X : TopCat) (V W : Set X) :
    smallBarycentricSubdivisionChainEndomorphism X V W ≫
        smallSingularChainInclusion X V W =
      smallSingularChainInclusion X V W ≫
        signedBarycentricSubdivisionChainEndomorphism X := by
  apply HomologicalComplex.hom_ext
  intro n
  exact smallBarycentricSubdivisionDegreeMap_comp_inclusion X V W n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionChainEndomorphism_comp_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionChainEndomorphism_comp_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionChainEndomorphism_comp_inclusion ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionChainEndomorphism_comp_inclusion



noncomputable def leftToSmallSingularChainMap
    (X : TopCat) (V W : Set X) :
    AmbientChains (TopCat.of V) ⟶ smallSingularChainComplex X V W :=
  SSet.chainComplexMap (leftToSmallSingularSubcomplex X V W)
    (ModuleCat.of ℤ ℤ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.leftToSmallSingularChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.leftToSmallSingularChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.leftToSmallSingularChainMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.leftToSmallSingularChainMap

noncomputable def rightToSmallSingularChainMap
    (X : TopCat) (V W : Set X) :
    AmbientChains (TopCat.of W) ⟶ smallSingularChainComplex X V W :=
  SSet.chainComplexMap (rightToSmallSingularSubcomplex X V W)
    (ModuleCat.of ℤ ℤ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.rightToSmallSingularChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.rightToSmallSingularChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.rightToSmallSingularChainMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.rightToSmallSingularChainMap

@[reassoc (attr := simp)]
theorem leftToSmallSingularChainMap_comp_inclusion
    (X : TopCat) (V W : Set X) :
    leftToSmallSingularChainMap X V W ≫
        smallSingularChainInclusion X V W =
      integerSingularChainMap (topologicalSubspaceInclusion V) := by
  change ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
        (leftToSmallSingularSubcomplex X V W) ≫
      ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
        (smallSingularSubcomplex X V W).ι =
    ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map
      (TopCat.toSSet.map (topologicalSubspaceInclusion V))
  rw [← Functor.map_comp, leftToSmallSingularSubcomplex_comp_inclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.leftToSmallSingularChainMap_comp_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.leftToSmallSingularChainMap_comp_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.leftToSmallSingularChainMap_comp_inclusion ``Submission.DifferentialGeometry.Topology.SphereSeparation.leftToSmallSingularChainMap_comp_inclusion

@[reassoc (attr := simp)]
theorem rightToSmallSingularChainMap_comp_inclusion
    (X : TopCat) (V W : Set X) :
    rightToSmallSingularChainMap X V W ≫
        smallSingularChainInclusion X V W =
      integerSingularChainMap (topologicalSubspaceInclusion W) := by
  change ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
        (rightToSmallSingularSubcomplex X V W) ≫
      ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
        (smallSingularSubcomplex X V W).ι =
    ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map
      (TopCat.toSSet.map (topologicalSubspaceInclusion W))
  rw [← Functor.map_comp, rightToSmallSingularSubcomplex_comp_inclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.rightToSmallSingularChainMap_comp_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.rightToSmallSingularChainMap_comp_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.rightToSmallSingularChainMap_comp_inclusion ``Submission.DifferentialGeometry.Topology.SphereSeparation.rightToSmallSingularChainMap_comp_inclusion

private def SmallSimplexFactorsLeftOf
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (smallSingularSubcomplex X V W : SSet) _⦋n⦌) : Prop :=
  ∃ t : (TopCat.toSSet.obj (TopCat.of V)) _⦋n⦌,
    (TopCat.toSSet.map (topologicalSubspaceInclusion V)).app _ t = s.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.SmallSimplexFactorsLeftOf
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.SmallSimplexFactorsLeftOf target :: scope.openDecls } }

private def SmallSimplexFactorsRightOf
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (smallSingularSubcomplex X V W : SSet) _⦋n⦌) : Prop :=
  ∃ t : (TopCat.toSSet.obj (TopCat.of W)) _⦋n⦌,
    (TopCat.toSSet.map (topologicalSubspaceInclusion W)).app _ t = s.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.SmallSimplexFactorsRightOf
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.SmallSimplexFactorsRightOf target :: scope.openDecls } }

private theorem smallSimplex_factors_left_or_right
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (smallSingularSubcomplex X V W : SSet) _⦋n⦌) :
    SmallSimplexFactorsLeftOf X V W s ∨
      SmallSimplexFactorsRightOf X V W s :=
  s.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallSimplex_factors_left_or_right
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.smallSimplex_factors_left_or_right target :: scope.openDecls } }

noncomputable def smallBarycentricSubdivisionPrismGenerator
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (smallSingularSubcomplex X V W : SSet) _⦋n⦌) :
    ModuleCat.of ℤ ℤ ⟶ (smallSingularChainComplex X V W).X (n + 1) := by
  classical
  exact if hV : SmallSimplexFactorsLeftOf X V W s then
    let t := Classical.choose hV
    (TopCat.toSSet.obj (TopCat.of V)).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) t ≫
      barycentricSubdivisionPrismComponent n (TopCat.of V) ≫
      (leftToSmallSingularChainMap X V W).f (n + 1)
  else
    let hW : SmallSimplexFactorsRightOf X V W s := by
      rcases smallSimplex_factors_left_or_right X V W s with h | h
      · exact False.elim (hV h)
      · exact h
    let t := Classical.choose hW
    (TopCat.toSSet.obj (TopCat.of W)).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) t ≫
      barycentricSubdivisionPrismComponent n (TopCat.of W) ≫
      (rightToSmallSingularChainMap X V W).f (n + 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismGenerator ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismGenerator

set_option backward.isDefEq.respectTransparency false in
theorem smallBarycentricSubdivisionPrismGenerator_comp_inclusion
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (smallSingularSubcomplex X V W : SSet) _⦋n⦌) :
    smallBarycentricSubdivisionPrismGenerator X V W s ≫
        (smallSingularChainInclusion X V W).f (n + 1) =
      (TopCat.toSSet.obj X).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s.1 ≫
        barycentricSubdivisionPrismComponent n X := by
  classical
  by_cases hV : SmallSimplexFactorsLeftOf X V W s
  · rw [smallBarycentricSubdivisionPrismGenerator, dif_pos hV]
    have ht :
        (TopCat.toSSet.map (topologicalSubspaceInclusion V)).app _
            (Classical.choose hV) =
          s.1 := Classical.choose_spec hV
    have hcomp := HomologicalComplex.congr_hom
      (leftToSmallSingularChainMap_comp_inclusion X V W) (n + 1)
    have hcomp' :
        (leftToSmallSingularChainMap X V W).f (n + 1) ≫
            (smallSingularChainInclusion X V W).f (n + 1) =
          (integerSingularChainMap
            (topologicalSubspaceInclusion V)).f (n + 1) := by
      simpa only [HomologicalComplex.comp_f] using hcomp
    calc
      _ = ((TopCat.toSSet.obj (TopCat.of V)).ιChainComplex
              (R := ModuleCat.of ℤ ℤ) (Classical.choose hV) ≫
            barycentricSubdivisionPrismComponent n (TopCat.of V)) ≫
          ((leftToSmallSingularChainMap X V W).f (n + 1) ≫
            (smallSingularChainInclusion X V W).f (n + 1)) := by
              simp only [Category.assoc]
      _ = ((TopCat.toSSet.obj (TopCat.of V)).ιChainComplex
              (R := ModuleCat.of ℤ ℤ) (Classical.choose hV) ≫
            barycentricSubdivisionPrismComponent n (TopCat.of V)) ≫
          (integerSingularChainMap
            (topologicalSubspaceInclusion V)).f (n + 1) := by rw [hcomp']
      _ = (TopCat.toSSet.obj X).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
                ((TopCat.toSSet.map
                  (topologicalSubspaceInclusion V)).app _
                    (Classical.choose hV)) ≫
            barycentricSubdivisionPrismComponent n X :=
          (ι_map_barycentricSubdivisionPrismComponent
            (topologicalSubspaceInclusion V) n (Classical.choose hV)).symm
      _ = _ := by rw [ht]
  · rw [smallBarycentricSubdivisionPrismGenerator, dif_neg hV]
    let hW : SmallSimplexFactorsRightOf X V W s := by
      rcases smallSimplex_factors_left_or_right X V W s with h | h
      · exact False.elim (hV h)
      · exact h
    have ht :
        (TopCat.toSSet.map (topologicalSubspaceInclusion W)).app _
            (Classical.choose hW) =
          s.1 := Classical.choose_spec hW
    have hcomp := HomologicalComplex.congr_hom
      (rightToSmallSingularChainMap_comp_inclusion X V W) (n + 1)
    have hcomp' :
        (rightToSmallSingularChainMap X V W).f (n + 1) ≫
            (smallSingularChainInclusion X V W).f (n + 1) =
          (integerSingularChainMap
            (topologicalSubspaceInclusion W)).f (n + 1) := by
      simpa only [HomologicalComplex.comp_f] using hcomp
    calc
      _ = ((TopCat.toSSet.obj (TopCat.of W)).ιChainComplex
              (R := ModuleCat.of ℤ ℤ) (Classical.choose hW) ≫
            barycentricSubdivisionPrismComponent n (TopCat.of W)) ≫
          ((rightToSmallSingularChainMap X V W).f (n + 1) ≫
            (smallSingularChainInclusion X V W).f (n + 1)) := by
              simp only [Category.assoc]
      _ = ((TopCat.toSSet.obj (TopCat.of W)).ιChainComplex
              (R := ModuleCat.of ℤ ℤ) (Classical.choose hW) ≫
            barycentricSubdivisionPrismComponent n (TopCat.of W)) ≫
          (integerSingularChainMap
            (topologicalSubspaceInclusion W)).f (n + 1) := by rw [hcomp']
      _ = (TopCat.toSSet.obj X).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
                ((TopCat.toSSet.map
                  (topologicalSubspaceInclusion W)).app _
                    (Classical.choose hW)) ≫
            barycentricSubdivisionPrismComponent n X :=
          (ι_map_barycentricSubdivisionPrismComponent
            (topologicalSubspaceInclusion W) n (Classical.choose hW)).symm
      _ = _ := by rw [ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismGenerator_comp_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismGenerator_comp_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismGenerator_comp_inclusion ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismGenerator_comp_inclusion

noncomputable def smallBarycentricSubdivisionPrismComponent
    (X : TopCat) (V W : Set X) (n : ℕ) :
    (smallSingularChainComplex X V W).X n ⟶
      (smallSingularChainComplex X V W).X (n + 1) :=
  Sigma.desc fun s =>
    smallBarycentricSubdivisionPrismGenerator X V W s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismComponent ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismComponent

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ι_smallBarycentricSubdivisionPrismComponent
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (smallSingularSubcomplex X V W : SSet) _⦋n⦌) :
    (smallSingularSubcomplex X V W : SSet).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s ≫
        smallBarycentricSubdivisionPrismComponent X V W n =
      smallBarycentricSubdivisionPrismGenerator X V W s := by
  dsimp [smallBarycentricSubdivisionPrismComponent, SSet.ιChainComplex]
  rw [Sigma.ι_desc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ι_smallBarycentricSubdivisionPrismComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ι_smallBarycentricSubdivisionPrismComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ι_smallBarycentricSubdivisionPrismComponent ``Submission.DifferentialGeometry.Topology.SphereSeparation.ι_smallBarycentricSubdivisionPrismComponent

set_option backward.isDefEq.respectTransparency false in
theorem smallBarycentricSubdivisionPrismComponent_comp_inclusion
    (X : TopCat) (V W : Set X) (n : ℕ) :
    smallBarycentricSubdivisionPrismComponent X V W n ≫
        (smallSingularChainInclusion X V W).f (n + 1) =
      (smallSingularChainInclusion X V W).f n ≫
        barycentricSubdivisionPrismComponent n X := by
  apply SSet.chainComplex_hom_ext
  intro s
  have hι :
      (smallSingularSubcomplex X V W : SSet).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) s ≫
          (smallSingularChainInclusion X V W).f n =
        (TopCat.toSSet.obj X).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s.1 := by
    change (smallSingularSubcomplex X V W : SSet).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) s ≫
          (SSet.chainComplexMap (smallSingularSubcomplex X V W).ι
            (ModuleCat.of ℤ ℤ)).f n = _
    rw [SSet.ι_chainComplexMap_f]
    rfl
  rw [← Category.assoc, ι_smallBarycentricSubdivisionPrismComponent,
    smallBarycentricSubdivisionPrismGenerator_comp_inclusion]
  rw [← Category.assoc, hι]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismComponent_comp_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismComponent_comp_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismComponent_comp_inclusion ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismComponent_comp_inclusion

private noncomputable def smallBarycentricSubdivisionPrismHomOfRel
    (X : TopCat) (V W : Set X) (i j : ℕ)
    (hji : (ComplexShape.down ℕ).Rel j i) :
    (smallSingularChainComplex X V W).X i ⟶
      (smallSingularChainComplex X V W).X j := by
  have h : i + 1 = j := by simpa using hji
  subst j
  exact smallBarycentricSubdivisionPrismComponent X V W i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismHomOfRel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismHomOfRel target :: scope.openDecls } }

@[simp]
private theorem smallBarycentricSubdivisionPrismHomOfRel_succ
    (X : TopCat) (V W : Set X) (i : ℕ)
    (h : (ComplexShape.down ℕ).Rel (i + 1) i) :
    smallBarycentricSubdivisionPrismHomOfRel X V W i (i + 1) h =
      smallBarycentricSubdivisionPrismComponent X V W i := by
  unfold smallBarycentricSubdivisionPrismHomOfRel
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismHomOfRel_succ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismHomOfRel_succ target :: scope.openDecls } }

noncomputable def smallBarycentricSubdivisionPrismNullMap
    (X : TopCat) (V W : Set X) :
    smallSingularChainComplex X V W ⟶
      smallSingularChainComplex X V W :=
  _root_.Homotopy.nullHomotopicMap'
    (smallBarycentricSubdivisionPrismHomOfRel X V W)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismNullMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismNullMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismNullMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismNullMap

private noncomputable def ambientBarycentricSubdivisionPrismHomOfRel
    (X : TopCat) (i j : ℕ)
    (hji : (ComplexShape.down ℕ).Rel j i) :
    (AmbientChains X).X i ⟶ (AmbientChains X).X j := by
  have h : i + 1 = j := by simpa using hji
  subst j
  exact barycentricSubdivisionPrismComponent i X

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.ambientBarycentricSubdivisionPrismHomOfRel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.ambientBarycentricSubdivisionPrismHomOfRel target :: scope.openDecls } }

@[simp]
private theorem ambientBarycentricSubdivisionPrismHomOfRel_succ
    (X : TopCat) (i : ℕ)
    (h : (ComplexShape.down ℕ).Rel (i + 1) i) :
    ambientBarycentricSubdivisionPrismHomOfRel X i (i + 1) h =
      barycentricSubdivisionPrismComponent i X := by
  unfold ambientBarycentricSubdivisionPrismHomOfRel
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.ambientBarycentricSubdivisionPrismHomOfRel_succ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.ambientBarycentricSubdivisionPrismHomOfRel_succ target :: scope.openDecls } }

private noncomputable def ambientBarycentricSubdivisionPrismNullMap
    (X : TopCat) : AmbientChains X ⟶ AmbientChains X :=
  _root_.Homotopy.nullHomotopicMap'
    (ambientBarycentricSubdivisionPrismHomOfRel X)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.ambientBarycentricSubdivisionPrismNullMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.ambientBarycentricSubdivisionPrismNullMap target :: scope.openDecls } }

set_option backward.isDefEq.respectTransparency false in
private theorem ambientBarycentricSubdivisionPrismComponent_zero
    (X : TopCat) : barycentricSubdivisionPrismComponent 0 X = 0 := by
  apply SSet.chainComplex_hom_ext
  intro s
  rw [ι_barycentricSubdivisionPrismComponent_zero]
  rw [_root_.CategoryTheory.Limits.comp_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.ambientBarycentricSubdivisionPrismComponent_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.ambientBarycentricSubdivisionPrismComponent_zero target :: scope.openDecls } }

private theorem ambientBarycentricSubdivisionPrismNullMap_f_zero
    (X : TopCat) :
    (ambientBarycentricSubdivisionPrismNullMap X).f 0 = 0 := by
  rw [ambientBarycentricSubdivisionPrismNullMap,
    _root_.Homotopy.nullHomotopicMap'_f_of_not_rel_left
      (show (ComplexShape.down ℕ).Rel 1 0 by simp)
      (show ∀ l : ℕ, ¬(ComplexShape.down ℕ).Rel 0 l by simp)]
  rw [ambientBarycentricSubdivisionPrismHomOfRel_succ,
    ambientBarycentricSubdivisionPrismComponent_zero]
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.ambientBarycentricSubdivisionPrismNullMap_f_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.ambientBarycentricSubdivisionPrismNullMap_f_zero target :: scope.openDecls } }

private theorem ambientBarycentricSubdivisionPrismNullMap_f_succ
    (X : TopCat) (k : ℕ) :
    (ambientBarycentricSubdivisionPrismNullMap X).f (k + 1) =
      (AmbientChains X).d (k + 1) k ≫
          barycentricSubdivisionPrismComponent k X +
        barycentricSubdivisionPrismComponent (k + 1) X ≫
          (AmbientChains X).d (k + 2) (k + 1) := by
  rw [ambientBarycentricSubdivisionPrismNullMap,
    _root_.Homotopy.nullHomotopicMap'_f
      (show (ComplexShape.down ℕ).Rel (k + 2) (k + 1) by simp)
      (show (ComplexShape.down ℕ).Rel (k + 1) k by simp)]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.ambientBarycentricSubdivisionPrismNullMap_f_succ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.ambientBarycentricSubdivisionPrismNullMap_f_succ target :: scope.openDecls } }

private theorem ambientBarycentricSubdivisionPrismNullMap_eq
    (X : TopCat) :
    ambientBarycentricSubdivisionPrismNullMap X =
      barycentricSubdivisionPrismNullMap X := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
      rw [ambientBarycentricSubdivisionPrismNullMap_f_zero,
        barycentricSubdivisionPrismNullMap_f_zero]
  | succ k =>
      rw [ambientBarycentricSubdivisionPrismNullMap_f_succ,
        barycentricSubdivisionPrismNullMap_f_succ]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.ambientBarycentricSubdivisionPrismNullMap_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.ambientBarycentricSubdivisionPrismNullMap_eq target :: scope.openDecls } }

set_option backward.isDefEq.respectTransparency false in
private theorem smallBarycentricSubdivisionPrismHomOfRel_comp_inclusion
    (X : TopCat) (V W : Set X) (i j : ℕ)
    (hji : (ComplexShape.down ℕ).Rel j i) :
    smallBarycentricSubdivisionPrismHomOfRel X V W i j hji ≫
        (smallSingularChainInclusion X V W).f j =
      (smallSingularChainInclusion X V W).f i ≫
        ambientBarycentricSubdivisionPrismHomOfRel X i j hji := by
  have h : i + 1 = j := by simpa using hji
  subst j
  change smallBarycentricSubdivisionPrismComponent X V W i ≫
      (smallSingularChainInclusion X V W).f (i + 1) =
    (smallSingularChainInclusion X V W).f i ≫
      barycentricSubdivisionPrismComponent i X
  exact smallBarycentricSubdivisionPrismComponent_comp_inclusion X V W i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismHomOfRel_comp_inclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismHomOfRel_comp_inclusion target :: scope.openDecls } }

theorem smallBarycentricSubdivisionPrismNullMap_comp_inclusion
    (X : TopCat) (V W : Set X) :
    smallBarycentricSubdivisionPrismNullMap X V W ≫
        smallSingularChainInclusion X V W =
      smallSingularChainInclusion X V W ≫
        barycentricSubdivisionPrismNullMap X := by
  rw [← ambientBarycentricSubdivisionPrismNullMap_eq]
  rw [smallBarycentricSubdivisionPrismNullMap,
    ambientBarycentricSubdivisionPrismNullMap,
    _root_.Homotopy.nullHomotopicMap'_comp,
    _root_.Homotopy.comp_nullHomotopicMap']
  congr
  funext i j hji
  exact smallBarycentricSubdivisionPrismHomOfRel_comp_inclusion
    X V W i j hji

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismNullMap_comp_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismNullMap_comp_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismNullMap_comp_inclusion ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionPrismNullMap_comp_inclusion


noncomputable def smallBarycentricSubdivisionDifference
    (X : TopCat) (V W : Set X) :
    smallSingularChainComplex X V W ⟶
      smallSingularChainComplex X V W :=
  smallBarycentricSubdivisionChainEndomorphism X V W - 𝟙 _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDifference then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDifference"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDifference ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDifference

theorem smallBarycentricSubdivisionDifference_comp_inclusion
    (X : TopCat) (V W : Set X) :
    smallBarycentricSubdivisionDifference X V W ≫
        smallSingularChainInclusion X V W =
      smallSingularChainInclusion X V W ≫
        signedBarycentricSubdivisionDifference X := by
  rw [smallBarycentricSubdivisionDifference,
    signedBarycentricSubdivisionDifference,
    Preadditive.sub_comp, Preadditive.comp_sub,
    Category.id_comp, Category.comp_id,
    smallBarycentricSubdivisionChainEndomorphism_comp_inclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDifference_comp_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDifference_comp_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDifference_comp_inclusion ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDifference_comp_inclusion

theorem smallBarycentricSubdivisionDifference_eq_prismNullMap
    (X : TopCat) (V W : Set X) :
    smallBarycentricSubdivisionDifference X V W =
      smallBarycentricSubdivisionPrismNullMap X V W := by
  let _ : _root_.CategoryTheory.Mono (smallSingularChainInclusion X V W) :=
    mono_smallSingularChainInclusion X V W
  apply (_root_.CategoryTheory.cancel_mono (smallSingularChainInclusion X V W)).1
  rw [smallBarycentricSubdivisionDifference_comp_inclusion,
    smallBarycentricSubdivisionPrismNullMap_comp_inclusion,
    signedBarycentricSubdivisionDifference_eq_prismNullMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDifference_eq_prismNullMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDifference_eq_prismNullMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDifference_eq_prismNullMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDifference_eq_prismNullMap

noncomputable def smallBarycentricSubdivisionDifferenceNullHomotopy
    (X : TopCat) (V W : Set X) :
    _root_.Homotopy (smallBarycentricSubdivisionDifference X V W) 0 :=
  (_root_.Homotopy.ofEq
      (smallBarycentricSubdivisionDifference_eq_prismNullMap X V W)).trans
    (_root_.Homotopy.nullHomotopy'
      (smallBarycentricSubdivisionPrismHomOfRel X V W))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDifferenceNullHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDifferenceNullHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDifferenceNullHomotopy ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionDifferenceNullHomotopy

noncomputable def smallBarycentricSubdivisionChainHomotopy
    (X : TopCat) (V W : Set X) :
    _root_.Homotopy
      (smallBarycentricSubdivisionChainEndomorphism X V W)
      (𝟙 (smallSingularChainComplex X V W)) :=
  _root_.Homotopy.equivSubZero.symm
    (smallBarycentricSubdivisionDifferenceNullHomotopy X V W)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionChainHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionChainHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionChainHomotopy ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallBarycentricSubdivisionChainHomotopy



noncomputable def smallChainsCokernelSubdivision
    (X : TopCat) (V W : Set X) :
    _root_.CategoryTheory.Limits.cokernel (smallSingularChainInclusion X V W) ⟶
      cokernel (smallSingularChainInclusion X V W) :=
  chainCokernelEndomorphism
    (smallSingularChainInclusion X V W)
    (smallBarycentricSubdivisionChainEndomorphism X V W)
    (signedBarycentricSubdivisionChainEndomorphism X)
    (smallBarycentricSubdivisionChainEndomorphism_comp_inclusion
      X V W).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivision ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivision


noncomputable def smallChainsCokernelSubdivisionPrismComponent
    (X : TopCat) (V W : Set X) (n : ℕ) :
    (_root_.CategoryTheory.Limits.cokernel (smallSingularChainInclusion X V W)).X n ⟶
      (_root_.CategoryTheory.Limits.cokernel (smallSingularChainInclusion X V W)).X (n + 1) :=
  (PreservesCokernel.iso
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)
      (smallSingularChainInclusion X V W)).hom ≫
    cokernel.desc ((smallSingularChainInclusion X V W).f n)
      (barycentricSubdivisionPrismComponent n X ≫
        (cokernel.π (smallSingularChainInclusion X V W)).f (n + 1))
      (by
      have hzero :
          (smallSingularChainInclusion X V W).f (n + 1) ≫
              (cokernel.π
                (smallSingularChainInclusion X V W)).f (n + 1) = 0 := by
        have h := HomologicalComplex.congr_hom
          (cokernel.condition (smallSingularChainInclusion X V W)) (n + 1)
        simpa only [HomologicalComplex.comp_f,
          HomologicalComplex.zero_f_apply] using h
      calc
        (smallSingularChainInclusion X V W).f n ≫
              (barycentricSubdivisionPrismComponent n X ≫
                (cokernel.π
                  (smallSingularChainInclusion X V W)).f (n + 1)) =
            ((smallSingularChainInclusion X V W).f n ≫
                barycentricSubdivisionPrismComponent n X) ≫
              (cokernel.π
                (smallSingularChainInclusion X V W)).f (n + 1) := by
                  simp only [Category.assoc]
        _ = (smallBarycentricSubdivisionPrismComponent X V W n ≫
                (smallSingularChainInclusion X V W).f (n + 1)) ≫
              (cokernel.π
                (smallSingularChainInclusion X V W)).f (n + 1) := by
                  rw [smallBarycentricSubdivisionPrismComponent_comp_inclusion]
        _ = smallBarycentricSubdivisionPrismComponent X V W n ≫
              ((smallSingularChainInclusion X V W).f (n + 1) ≫
                (cokernel.π
                  (smallSingularChainInclusion X V W)).f (n + 1)) := by
                  simp only [Category.assoc]
        _ = 0 := by rw [hzero, _root_.CategoryTheory.Limits.comp_zero])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionPrismComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionPrismComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionPrismComponent ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionPrismComponent

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem smallChainsCokernelProjection_comp_subdivisionPrismComponent
    (X : TopCat) (V W : Set X) (n : ℕ) :
    (cokernel.π (smallSingularChainInclusion X V W)).f n ≫
        smallChainsCokernelSubdivisionPrismComponent X V W n =
      barycentricSubdivisionPrismComponent n X ≫
        (cokernel.π
          (smallSingularChainInclusion X V W)).f (n + 1) := by
  have hπ :
      (cokernel.π (smallSingularChainInclusion X V W)).f n ≫
          (PreservesCokernel.iso
            (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)
            (smallSingularChainInclusion X V W)).hom =
        cokernel.π ((smallSingularChainInclusion X V W).f n) := by
    exact PreservesCokernel.π_iso_hom
      (G := HomologicalComplex.eval
        (ModuleCat ℤ) (ComplexShape.down ℕ) n)
      (f := smallSingularChainInclusion X V W)
  change (cokernel.π (smallSingularChainInclusion X V W)).f n ≫
      ((PreservesCokernel.iso
          (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)
          (smallSingularChainInclusion X V W)).hom ≫
        cokernel.desc ((smallSingularChainInclusion X V W).f n)
          (barycentricSubdivisionPrismComponent n X ≫
            (cokernel.π
              (smallSingularChainInclusion X V W)).f (n + 1)) _) = _
  rw [← Category.assoc, hπ, cokernel.π_desc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelProjection_comp_subdivisionPrismComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelProjection_comp_subdivisionPrismComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelProjection_comp_subdivisionPrismComponent ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelProjection_comp_subdivisionPrismComponent

private noncomputable def smallChainsCokernelSubdivisionPrismHomOfRel
    (X : TopCat) (V W : Set X) (i j : ℕ)
    (hji : (ComplexShape.down ℕ).Rel j i) :
    (_root_.CategoryTheory.Limits.cokernel (smallSingularChainInclusion X V W)).X i ⟶
      (_root_.CategoryTheory.Limits.cokernel (smallSingularChainInclusion X V W)).X j := by
  have h : i + 1 = j := by simpa using hji
  subst j
  exact smallChainsCokernelSubdivisionPrismComponent X V W i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionPrismHomOfRel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionPrismHomOfRel target :: scope.openDecls } }

set_option backward.isDefEq.respectTransparency false in
private theorem smallChainsCokernelSubdivisionPrismHomOfRel_succ
    (X : TopCat) (V W : Set X) (i : ℕ)
    (h : (ComplexShape.down ℕ).Rel (i + 1) i) :
    smallChainsCokernelSubdivisionPrismHomOfRel X V W i (i + 1) h =
      smallChainsCokernelSubdivisionPrismComponent X V W i := by
  unfold smallChainsCokernelSubdivisionPrismHomOfRel
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionPrismHomOfRel_succ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionPrismHomOfRel_succ target :: scope.openDecls } }

noncomputable def smallChainsCokernelSubdivisionPrismNullMap
    (X : TopCat) (V W : Set X) :
    _root_.CategoryTheory.Limits.cokernel (smallSingularChainInclusion X V W) ⟶
      cokernel (smallSingularChainInclusion X V W) :=
  _root_.Homotopy.nullHomotopicMap'
    (smallChainsCokernelSubdivisionPrismHomOfRel X V W)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionPrismNullMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionPrismNullMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionPrismNullMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionPrismNullMap

set_option backward.isDefEq.respectTransparency false in
private theorem smallChainsCokernelSubdivisionPrismHomOfRel_projection
    (X : TopCat) (V W : Set X) (i j : ℕ)
    (hji : (ComplexShape.down ℕ).Rel j i) :
    (cokernel.π (smallSingularChainInclusion X V W)).f i ≫
        smallChainsCokernelSubdivisionPrismHomOfRel X V W i j hji =
      ambientBarycentricSubdivisionPrismHomOfRel X i j hji ≫
        (cokernel.π (smallSingularChainInclusion X V W)).f j := by
  have h : i + 1 = j := by simpa using hji
  subst j
  change (cokernel.π (smallSingularChainInclusion X V W)).f i ≫
      smallChainsCokernelSubdivisionPrismComponent X V W i =
    barycentricSubdivisionPrismComponent i X ≫
      (cokernel.π (smallSingularChainInclusion X V W)).f (i + 1)
  exact smallChainsCokernelProjection_comp_subdivisionPrismComponent X V W i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionPrismHomOfRel_projection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionPrismHomOfRel_projection target :: scope.openDecls } }

theorem smallChainsCokernelProjection_comp_subdivisionPrismNullMap
    (X : TopCat) (V W : Set X) :
    cokernel.π (smallSingularChainInclusion X V W) ≫
        smallChainsCokernelSubdivisionPrismNullMap X V W =
      barycentricSubdivisionPrismNullMap X ≫
        cokernel.π (smallSingularChainInclusion X V W) := by
  rw [← ambientBarycentricSubdivisionPrismNullMap_eq]
  rw [smallChainsCokernelSubdivisionPrismNullMap,
    ambientBarycentricSubdivisionPrismNullMap,
    _root_.Homotopy.comp_nullHomotopicMap',
    _root_.Homotopy.nullHomotopicMap'_comp]
  congr
  funext i j hji
  exact smallChainsCokernelSubdivisionPrismHomOfRel_projection
    X V W i j hji

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelProjection_comp_subdivisionPrismNullMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelProjection_comp_subdivisionPrismNullMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelProjection_comp_subdivisionPrismNullMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelProjection_comp_subdivisionPrismNullMap

@[reassoc (attr := simp)]
theorem smallChainsCokernelProjection_comp_subdivision
    (X : TopCat) (V W : Set X) :
    cokernel.π (smallSingularChainInclusion X V W) ≫
        smallChainsCokernelSubdivision X V W =
      signedBarycentricSubdivisionChainEndomorphism X ≫
        cokernel.π (smallSingularChainInclusion X V W) := by
  exact chainCokernelProjection_naturality
    (smallSingularChainInclusion X V W)
    (smallBarycentricSubdivisionChainEndomorphism X V W)
    (signedBarycentricSubdivisionChainEndomorphism X)
    (smallBarycentricSubdivisionChainEndomorphism_comp_inclusion
      X V W).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelProjection_comp_subdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelProjection_comp_subdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelProjection_comp_subdivision ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelProjection_comp_subdivision


noncomputable def smallChainsCokernelSubdivisionDifference
    (X : TopCat) (V W : Set X) :
    _root_.CategoryTheory.Limits.cokernel (smallSingularChainInclusion X V W) ⟶
      cokernel (smallSingularChainInclusion X V W) :=
  smallChainsCokernelSubdivision X V W - 𝟙 _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionDifference then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionDifference"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionDifference ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionDifference

theorem smallChainsCokernelProjection_comp_subdivisionDifference
    (X : TopCat) (V W : Set X) :
    cokernel.π (smallSingularChainInclusion X V W) ≫
        smallChainsCokernelSubdivisionDifference X V W =
      signedBarycentricSubdivisionDifference X ≫
        cokernel.π (smallSingularChainInclusion X V W) := by
  rw [smallChainsCokernelSubdivisionDifference,
    signedBarycentricSubdivisionDifference,
    Preadditive.comp_sub, Preadditive.sub_comp,
    Category.comp_id, Category.id_comp,
    smallChainsCokernelProjection_comp_subdivision]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelProjection_comp_subdivisionDifference then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelProjection_comp_subdivisionDifference"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelProjection_comp_subdivisionDifference ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelProjection_comp_subdivisionDifference

theorem smallChainsCokernelSubdivisionDifference_eq_prismNullMap
    (X : TopCat) (V W : Set X) :
    smallChainsCokernelSubdivisionDifference X V W =
      smallChainsCokernelSubdivisionPrismNullMap X V W := by
  apply (_root_.CategoryTheory.cancel_epi
    (cokernel.π (smallSingularChainInclusion X V W))).1
  rw [smallChainsCokernelProjection_comp_subdivisionDifference,
    smallChainsCokernelProjection_comp_subdivisionPrismNullMap,
    signedBarycentricSubdivisionDifference_eq_prismNullMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionDifference_eq_prismNullMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionDifference_eq_prismNullMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionDifference_eq_prismNullMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionDifference_eq_prismNullMap

noncomputable def smallChainsCokernelSubdivisionDifferenceNullHomotopy
    (X : TopCat) (V W : Set X) :
    _root_.Homotopy
      (smallChainsCokernelSubdivisionDifference X V W) 0 :=
  (_root_.Homotopy.ofEq
      (smallChainsCokernelSubdivisionDifference_eq_prismNullMap X V W)).trans
    (_root_.Homotopy.nullHomotopy'
      (smallChainsCokernelSubdivisionPrismHomOfRel X V W))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionDifferenceNullHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionDifferenceNullHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionDifferenceNullHomotopy ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionDifferenceNullHomotopy

noncomputable def smallChainsCokernelSubdivisionHomotopy
    (X : TopCat) (V W : Set X) :
    _root_.Homotopy (smallChainsCokernelSubdivision X V W)
      (𝟙 (_root_.CategoryTheory.Limits.cokernel (smallSingularChainInclusion X V W))) :=
  _root_.Homotopy.equivSubZero.symm
    (smallChainsCokernelSubdivisionDifferenceNullHomotopy X V W)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionHomotopy ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivisionHomotopy



theorem smallChainsCokernelSubdivision_eventually_zero
    (X : TopCat) {V₀ W₀ V W : Set X}
    (hV₀ : IsOpen V₀) (hW₀ : IsOpen W₀)
    (hcover : V₀ ∪ W₀ = Set.univ)
    (hV : V₀ ⊆ V) (hW : W₀ ⊆ W) (n : ℕ) :
    ∀ x : (integerSingularChainComplex X).X n, ∃ k : ℕ,
      (cokernel.π (smallSingularChainInclusion X V W)).f n
        ((((signedBarycentricSubdivisionChainEndomorphism X).f n)^[k]) x) =
          0 := by
  apply subdivision_eventually_zero_in_smallChainCokernel X
    hV₀ hW₀ hcover hV hW n
  intro x hx
  have hmap := HomologicalComplex.congr_hom
    (smallChainsCokernelProjection_comp_subdivision X V W) n
  have happly := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hmap) x
  calc
    (cokernel.π (smallSingularChainInclusion X V W)).f n
        ((singularBarycentricSubdivision X).f n x) =
      (smallChainsCokernelSubdivision X V W).f n
        ((cokernel.π (smallSingularChainInclusion X V W)).f n x) :=
          happly.symm
    _ = (smallChainsCokernelSubdivision X V W).f n 0 := by rw [hx]
    _ = 0 := map_zero _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivision_eventually_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivision_eventually_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivision_eventually_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallChainsCokernelSubdivision_eventually_zero

theorem quasiIso_smallSingularChainInclusion
    (X : TopCat) (V W : Set X)
    (hV : IsOpen V) (hW : IsOpen W)
    (hcover : V ∪ W = Set.univ) :
    QuasiIso (smallSingularChainInclusion X V W) := by
  let _ : _root_.CategoryTheory.Mono (smallSingularChainInclusion X V W) :=
    mono_smallSingularChainInclusion X V W
  apply quasiIso_of_cokernelSubdivision_eventually_zero
    (smallSingularChainInclusion X V W)
    (smallBarycentricSubdivisionChainEndomorphism X V W)
    (signedBarycentricSubdivisionChainEndomorphism X)
    (smallBarycentricSubdivisionChainEndomorphism_comp_inclusion X V W).symm
    (smallChainsCokernelSubdivisionHomotopy X V W)
  intro n x
  exact smallChainsCokernelSubdivision_eventually_zero X
    hV hW hcover (fun _ h ↦ h) (fun _ h ↦ h) n x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.quasiIso_smallSingularChainInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.quasiIso_smallSingularChainInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.quasiIso_smallSingularChainInclusion ``Submission.DifferentialGeometry.Topology.SphereSeparation.quasiIso_smallSingularChainInclusion

theorem quasiIso_smallSingularChainInclusion_of_openCover_refines
    (X : TopCat) {V₀ W₀ V W : Set X}
    (hV₀ : IsOpen V₀) (hW₀ : IsOpen W₀)
    (hcover : V₀ ∪ W₀ = Set.univ)
    (hV : V₀ ⊆ V) (hW : W₀ ⊆ W) :
    QuasiIso (smallSingularChainInclusion X V W) := by
  let _ : _root_.CategoryTheory.Mono (smallSingularChainInclusion X V W) :=
    mono_smallSingularChainInclusion X V W
  apply quasiIso_of_cokernelSubdivision_eventually_zero
    (smallSingularChainInclusion X V W)
    (smallBarycentricSubdivisionChainEndomorphism X V W)
    (signedBarycentricSubdivisionChainEndomorphism X)
    (smallBarycentricSubdivisionChainEndomorphism_comp_inclusion X V W).symm
    (smallChainsCokernelSubdivisionHomotopy X V W)
  intro n x
  exact smallChainsCokernelSubdivision_eventually_zero X
    hV₀ hW₀ hcover hV hW n x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.quasiIso_smallSingularChainInclusion_of_openCover_refines then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.quasiIso_smallSingularChainInclusion_of_openCover_refines"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.quasiIso_smallSingularChainInclusion_of_openCover_refines ``Submission.DifferentialGeometry.Topology.SphereSeparation.quasiIso_smallSingularChainInclusion_of_openCover_refines

end DifferentialGeometry.Topology.SphereSeparation
