import Submission.DifferentialGeometry.Topology.Homology.Subdivision.Homotopy
import Submission.DifferentialGeometry.Topology.Homology.SmallChains

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set E} (hs : Convex ℝ s)

local notation "A" => smallSingularSimplices (TopCat.of E) (fun _ : Unit ↦ s)

omit [NormedSpace ℝ E] in
private theorem small_vertices_mem {n : ℕ} (σ : (A : SSet) _⦋n⦌) (i : Fin (n + 1)) :
    singularSimplexVertices σ.val i ∈ s := by
  obtain ⟨_, hσ⟩ := σ.property
  exact hσ ⟨stdSimplex.vertex i, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.small_vertices_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.small_vertices_mem target :: scope.openDecls } }


def smallBarycenter {n : ℕ} (σ : (A : SSet) _⦋n⦌) : s :=
  ⟨singularSimplexBarycenter σ.val,
    singularSimplexBarycenter_mem _ hs (small_vertices_mem σ)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallBarycenter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallBarycenter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallBarycenter ``Submission.DifferentialGeometry.Homology.smallBarycenter


def smallAffineSimplex {n : ℕ} (σ : (A : SSet) _⦋n⦌) : (A : SSet) _⦋n⦌ :=
  ⟨affineSingularSimplex (singularSimplexVertices σ.val), by
    refine ⟨(), ?_⟩
    exact range_affineSimplex_subset _ hs (small_vertices_mem σ)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallAffineSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallAffineSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallAffineSimplex ``Submission.DifferentialGeometry.Homology.smallAffineSimplex


def smallConeSimplex (p : s) {n : ℕ} (σ : (A : SSet) _⦋n⦌) :
    (A : SSet) _⦋n + 1⦌ :=
  ⟨affineSingularSimplex (Fin.cons (p : E) (singularSimplexVertices σ.val)), by
    refine ⟨(), ?_⟩
    exact range_affineSimplex_subset _ hs (Fin.cases p.property (small_vertices_mem σ))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallConeSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallConeSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallConeSimplex ``Submission.DifferentialGeometry.Homology.smallConeSimplex


def smallAffineStraightening : (A : SSet) ⟶ (A : SSet) :=
  SSet.Subcomplex.lift ((A).ι ≫ affineStraightening) (by
    intro n τ hτ
    obtain ⟨σ, rfl⟩ := hτ
    exact (smallAffineSimplex hs (n := n.unop.len) σ).property)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallAffineStraightening then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallAffineStraightening"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallAffineStraightening ``Submission.DifferentialGeometry.Homology.smallAffineStraightening


@[reassoc]
theorem smallAffineStraightening_ι :
    smallAffineStraightening hs ≫ (A).ι = (A).ι ≫ affineStraightening := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallAffineStraightening_ι then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallAffineStraightening_ι"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallAffineStraightening_ι ``Submission.DifferentialGeometry.Homology.smallAffineStraightening_ι

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

local notation "KA" => _root_.SSet.chainComplex (A : SSet) R
local notation "K" => _root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R
local notation "I" => _root_.SSet.chainComplexMap (SSet.Subcomplex.ι (A)) R
local notation "SA" => _root_.SSet.chainComplexMap (smallAffineStraightening hs) R
local notation "S" => _root_.SSet.chainComplexMap (affineStraightening (E := E)) R


theorem smallAffineStraightening_inclusion : (SA) ≫ (I) = (I) ≫ (S) := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ =
    ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, ← Functor.map_comp, smallAffineStraightening_ι]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallAffineStraightening_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallAffineStraightening_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallAffineStraightening_inclusion ``Submission.DifferentialGeometry.Homology.smallAffineStraightening_inclusion


def smallAffineCone (p : s) (n : ℕ) : (KA).X n ⟶ (KA).X (n + 1) :=
  Sigma.desc (fun σ ↦ (A : SSet).ιChainComplex (smallConeSimplex hs p σ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallAffineCone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallAffineCone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallAffineCone ``Submission.DifferentialGeometry.Homology.smallAffineCone


@[reassoc]
theorem ι_smallAffineCone (p : s) {n : ℕ} (σ : (A : SSet) _⦋n⦌) :
    (A : SSet).ιChainComplex σ ≫ smallAffineCone hs R p n =
      (A : SSet).ιChainComplex (smallConeSimplex hs p σ) :=
  Sigma.ι_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.ι_smallAffineCone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.ι_smallAffineCone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.ι_smallAffineCone ``Submission.DifferentialGeometry.Homology.ι_smallAffineCone


@[reassoc]
theorem smallAffineCone_inclusion (p : s) (n : ℕ) :
    smallAffineCone hs R p n ≫ (I).f (n + 1) = (I).f n ≫ affineCone R (p : E) n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_smallAffineCone, SSet.ι_chainComplexMap_f,
    ← Category.assoc, SSet.ι_chainComplexMap_f, ι_affineCone]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallAffineCone_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallAffineCone_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallAffineCone_inclusion ``Submission.DifferentialGeometry.Homology.smallAffineCone_inclusion


def smallAffineSubdivisionMap (n : ℕ) : (KA).X n ⟶ (KA).X n :=
  match n with
  | 0 => 𝟙 _
  | n + 1 => Sigma.desc (fun σ ↦ (A : SSet).ιChainComplex σ ≫
      (KA).d (n + 1) n ≫ smallAffineSubdivisionMap n ≫
        smallAffineCone hs R (smallBarycenter hs σ) n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallAffineSubdivisionMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallAffineSubdivisionMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallAffineSubdivisionMap ``Submission.DifferentialGeometry.Homology.smallAffineSubdivisionMap


@[simp]
theorem smallAffineSubdivisionMap_zero : smallAffineSubdivisionMap hs R 0 = 𝟙 _ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallAffineSubdivisionMap_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallAffineSubdivisionMap_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallAffineSubdivisionMap_zero ``Submission.DifferentialGeometry.Homology.smallAffineSubdivisionMap_zero


@[reassoc]
theorem ι_smallAffineSubdivisionMap_succ (n : ℕ) (σ : (A : SSet) _⦋n + 1⦌) :
    (A : SSet).ιChainComplex σ ≫ smallAffineSubdivisionMap hs R (n + 1) =
      (A : SSet).ιChainComplex σ ≫ (KA).d (n + 1) n ≫
        smallAffineSubdivisionMap hs R n ≫ smallAffineCone hs R (smallBarycenter hs σ) n :=
  Sigma.ι_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.ι_smallAffineSubdivisionMap_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.ι_smallAffineSubdivisionMap_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.ι_smallAffineSubdivisionMap_succ ``Submission.DifferentialGeometry.Homology.ι_smallAffineSubdivisionMap_succ


theorem smallAffineSubdivisionMap_inclusion (n : ℕ) :
    smallAffineSubdivisionMap hs R n ≫ (I).f n = (I).f n ≫ affineSubdivisionMap R n := by
  induction n with
  | zero => rw [smallAffineSubdivisionMap_zero, affineSubdivisionMap_zero,
      Category.id_comp, Category.comp_id]
  | succ n hn =>
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, ι_smallAffineSubdivisionMap_succ]
    simp only [Category.assoc]
    rw [smallAffineCone_inclusion]
    rw [← Category.assoc (smallAffineSubdivisionMap hs R n), hn]
    simp only [Category.assoc]
    rw [← Category.assoc ((KA).d (n + 1) n), ← (I).comm]
    simp only [Category.assoc]
    rw [← Category.assoc _ ((I).f (n + 1)), SSet.ι_chainComplexMap_f]
    rw [← Category.assoc ((A : SSet).ιChainComplex σ) ((I).f (n + 1)),
      SSet.ι_chainComplexMap_f, ι_affineSubdivisionMap_succ]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallAffineSubdivisionMap_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallAffineSubdivisionMap_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallAffineSubdivisionMap_inclusion ``Submission.DifferentialGeometry.Homology.smallAffineSubdivisionMap_inclusion

private theorem smallDifference_inclusion (n : ℕ) :
    (smallAffineSubdivisionMap hs R n - (SA).f n) ≫ (I).f n =
      (I).f n ≫ (affineSubdivision R - S).f n := by
  rw [Preadditive.sub_comp, smallAffineSubdivisionMap_inclusion]
  have h := HomologicalComplex.congr_hom (smallAffineStraightening_inclusion hs R) n
  simp only [HomologicalComplex.comp_f] at h
  rw [h, HomologicalComplex.sub_f_apply, Preadditive.comp_sub, affineSubdivision_f]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.smallDifference_inclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.smallDifference_inclusion target :: scope.openDecls } }


def smallAffineSubdivisionHomotopyMap (n : ℕ) : (KA).X n ⟶ (KA).X (n + 1) :=
  match n with
  | 0 => 0
  | n + 1 => Sigma.desc (fun σ ↦
      ((A : SSet).ιChainComplex σ ≫ (smallAffineSubdivisionMap hs R (n + 1) - (SA).f (n + 1)) -
        (A : SSet).ιChainComplex σ ≫ (KA).d (n + 1) n ≫
          smallAffineSubdivisionHomotopyMap n) ≫
        smallAffineCone hs R (smallBarycenter hs σ) (n + 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallAffineSubdivisionHomotopyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallAffineSubdivisionHomotopyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallAffineSubdivisionHomotopyMap ``Submission.DifferentialGeometry.Homology.smallAffineSubdivisionHomotopyMap


@[simp]
theorem smallAffineSubdivisionHomotopyMap_zero :
    smallAffineSubdivisionHomotopyMap hs R 0 = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallAffineSubdivisionHomotopyMap_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallAffineSubdivisionHomotopyMap_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallAffineSubdivisionHomotopyMap_zero ``Submission.DifferentialGeometry.Homology.smallAffineSubdivisionHomotopyMap_zero


@[reassoc]
theorem ι_smallAffineSubdivisionHomotopyMap_succ (n : ℕ) (σ : (A : SSet) _⦋n + 1⦌) :
    (A : SSet).ιChainComplex σ ≫ smallAffineSubdivisionHomotopyMap hs R (n + 1) =
      ((A : SSet).ιChainComplex σ ≫ (smallAffineSubdivisionMap hs R (n + 1) - (SA).f (n + 1)) -
        (A : SSet).ιChainComplex σ ≫ (KA).d (n + 1) n ≫
          smallAffineSubdivisionHomotopyMap hs R n) ≫
        smallAffineCone hs R (smallBarycenter hs σ) (n + 1) :=
  Sigma.ι_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.ι_smallAffineSubdivisionHomotopyMap_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.ι_smallAffineSubdivisionHomotopyMap_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.ι_smallAffineSubdivisionHomotopyMap_succ ``Submission.DifferentialGeometry.Homology.ι_smallAffineSubdivisionHomotopyMap_succ

theorem smallAffineSubdivisionHomotopyMap_inclusion (n : ℕ) :
    smallAffineSubdivisionHomotopyMap hs R n ≫ (I).f (n + 1) =
      (I).f n ≫ affineSubdivisionHomotopyMap R n := by
  induction n with
  | zero => rw [smallAffineSubdivisionHomotopyMap_zero, affineSubdivisionHomotopyMap_zero,
      _root_.CategoryTheory.Limits.zero_comp, _root_.CategoryTheory.Limits.comp_zero]
  | succ n hn =>
    apply SSet.chainComplex_hom_ext
    intro σ
    have hz :
        ((A : SSet).ιChainComplex σ ≫
            (smallAffineSubdivisionMap hs R (n + 1) - (SA).f (n + 1)) -
          (A : SSet).ιChainComplex σ ≫ (KA).d (n + 1) n ≫
            smallAffineSubdivisionHomotopyMap hs R n) ≫ (I).f (n + 1) =
        (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ.val ≫
            (affineSubdivision R - S).f (n + 1) -
          (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ.val ≫
            (K).d (n + 1) n ≫ affineSubdivisionHomotopyMap R n := by
      rw [Preadditive.sub_comp]
      simp only [Category.assoc]
      rw [smallDifference_inclusion, hn]
      rw [← Category.assoc ((KA).d (n + 1) n), ← (I).comm]
      simp only [Category.assoc]
      rw [← Category.assoc ((A : SSet).ιChainComplex σ) ((I).f (n + 1)),
        SSet.ι_chainComplexMap_f]
      rw [← Category.assoc ((A : SSet).ιChainComplex σ) ((I).f (n + 1)),
        SSet.ι_chainComplexMap_f]
      rfl
    rw [← Category.assoc, ι_smallAffineSubdivisionHomotopyMap_succ, Category.assoc,
      smallAffineCone_inclusion, ← Category.assoc, hz]
    rw [← Category.assoc ((A : SSet).ιChainComplex σ) ((I).f (n + 1)),
      SSet.ι_chainComplexMap_f, ι_affineSubdivisionHomotopyMap_succ]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallAffineSubdivisionHomotopyMap_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallAffineSubdivisionHomotopyMap_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallAffineSubdivisionHomotopyMap_inclusion ``Submission.DifferentialGeometry.Homology.smallAffineSubdivisionHomotopyMap_inclusion

end DifferentialGeometry.Homology
