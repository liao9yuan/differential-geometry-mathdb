import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Order.Interval.Finset.Fin

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.PartialOrder
open _root_.Simplicial
open scoped _root_.Simplicial

namespace DifferentialGeometry.Topology.SphereSeparation




def uliftOrderHom {α β : Type} [Preorder α] [Preorder β]
    (f : α →o β) : ULift α →o ULift β where
  toFun x := ULift.up (f x.down)
  monotone' _ _ h := f.monotone h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.uliftOrderHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.uliftOrderHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.uliftOrderHom ``Submission.DifferentialGeometry.Topology.SphereSeparation.uliftOrderHom


noncomputable def nonemptyFaceLastVertex {n : ℕ}
    (A : _root_.PartialOrder.NonemptyFiniteChains (ULift (Fin (n + 1)))) :
    ULift (Fin (n + 1)) :=
  A.finset.max' A.nonempty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceLastVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceLastVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceLastVertex ``Submission.DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceLastVertex


theorem nonemptyFaceLastVertex_mono {n : ℕ}
    {A B : _root_.PartialOrder.NonemptyFiniteChains (ULift (Fin (n + 1)))}
    (h : A ≤ B) :
    nonemptyFaceLastVertex A ≤ nonemptyFaceLastVertex B :=
  Finset.max'_subset A.nonempty h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceLastVertex_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceLastVertex_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceLastVertex_mono ``Submission.DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceLastVertex_mono


noncomputable def nonemptyFaceLastVertexOrderHom (n : ℕ) :
    _root_.PartialOrder.NonemptyFiniteChains (ULift (Fin (n + 1))) →o
      ULift (Fin (n + 1)) where
  toFun := nonemptyFaceLastVertex
  monotone' _ _ := nonemptyFaceLastVertex_mono

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceLastVertexOrderHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceLastVertexOrderHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceLastVertexOrderHom ``Submission.DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceLastVertexOrderHom

theorem nonemptyFaceLastVertex_map
    {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (A : _root_.PartialOrder.NonemptyFiniteChains (ULift (Fin (m + 1)))) :
    nonemptyFaceLastVertex (A.map (uliftOrderHom f)) =
      ULift.up (f (nonemptyFaceLastVertex A).down) := by
  classical
  unfold nonemptyFaceLastVertex
  rw [Finset.max'_eq_iff]
  constructor
  · rw [NonemptyFiniteChains.mem_map_iff]
    exact ⟨A.finset.max' A.nonempty, A.finset.max'_mem A.nonempty, rfl⟩
  · intro b hb
    rw [NonemptyFiniteChains.mem_map_iff] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact (uliftOrderHom f).monotone (A.finset.le_max' a ha)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceLastVertex_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceLastVertex_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceLastVertex_map ``Submission.DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceLastVertex_map




noncomputable def simplexCategoryLastVertex :
    SimplexCategory.toPartOrd ⋙ PartOrd.nonemptyFiniteChainsFunctor ⟶
      SimplexCategory.toPartOrd where
  app n := PartOrd.ofHom (nonemptyFaceLastVertexOrderHom n.len)
  naturality {m n} f := by
    ext A
    exact nonemptyFaceLastVertex_map f.toOrderHom A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.simplexCategoryLastVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.simplexCategoryLastVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.simplexCategoryLastVertex ``Submission.DifferentialGeometry.Topology.SphereSeparation.simplexCategoryLastVertex

def standardSimplexNerveIso :
    SSet.stdSimplex ≅ SimplexCategory.toPartOrd ⋙ PartOrd.nerveFunctor :=
  NatIso.ofComponents
    (fun n => SSet.stdSimplex.isoNerve n.len)
    (fun {m n} f => by
      ext d s
      rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.standardSimplexNerveIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.standardSimplexNerveIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.standardSimplexNerveIso ``Submission.DifferentialGeometry.Topology.SphereSeparation.standardSimplexNerveIso


noncomputable def subdividedStandardSimplexLastVertex :
    SimplexCategory.sd ⟶ SSet.stdSimplex :=
  Functor.whiskerRight simplexCategoryLastVertex PartOrd.nerveFunctor ≫
    standardSimplexNerveIso.inv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.subdividedStandardSimplexLastVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.subdividedStandardSimplexLastVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.subdividedStandardSimplexLastVertex ``Submission.DifferentialGeometry.Topology.SphereSeparation.subdividedStandardSimplexLastVertex



noncomputable def SSet.barycentricSubdivisionLastVertex :
    SSet.sd ⟶ 𝟭 SSet :=
  SSet.sd.descOfIsLeftKanExtension SSet.stdSimplex.sdIso.inv (𝟭 SSet)
    (subdividedStandardSimplexLastVertex ≫
      (Functor.rightUnitor SSet.stdSimplex).inv)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.SphereSeparation.SSet
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SSet.barycentricSubdivisionLastVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SSet.barycentricSubdivisionLastVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SSet.barycentricSubdivisionLastVertex ``Submission.DifferentialGeometry.Topology.SphereSeparation.SSet.barycentricSubdivisionLastVertex

theorem barycentricSubdivisionLastVertex_standardSimplex :
    SSet.stdSimplex.sdIso.inv ≫
        Functor.whiskerLeft SSet.stdSimplex
          SSet.barycentricSubdivisionLastVertex =
      subdividedStandardSimplexLastVertex ≫
        (Functor.rightUnitor SSet.stdSimplex).inv :=
  SSet.sd.descOfIsLeftKanExtension_fac _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionLastVertex_standardSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionLastVertex_standardSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionLastVertex_standardSimplex ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionLastVertex_standardSimplex

noncomputable def barycentricSubdivisionChainMap
    {C : Type} [_root_.CategoryTheory.Category C] [_root_.CategoryTheory.Preadditive C] [HasCoproducts.{0} C]
    (X : SSet) (R : C) :
    (SSet.sd.obj X).chainComplex R ⟶ X.chainComplex R :=
  SSet.chainComplexMap (SSet.barycentricSubdivisionLastVertex.app X) R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainMap


theorem barycentricSubdivisionChainMap_naturality
    {C : Type} [_root_.CategoryTheory.Category C] [_root_.CategoryTheory.Preadditive C] [HasCoproducts.{0} C]
    {X Y : SSet} (f : X ⟶ Y) (R : C) :
    barycentricSubdivisionChainMap X R ≫ SSet.chainComplexMap f R =
      SSet.chainComplexMap (SSet.sd.map f) R ≫
        barycentricSubdivisionChainMap Y R := by
  change ((SSet.chainComplexFunctor C).obj R).map
      (SSet.barycentricSubdivisionLastVertex.app X) ≫
        ((SSet.chainComplexFunctor C).obj R).map f =
    ((SSet.chainComplexFunctor C).obj R).map (SSet.sd.map f) ≫
      ((SSet.chainComplexFunctor C).obj R).map
        (SSet.barycentricSubdivisionLastVertex.app Y)
  rw [← Functor.map_comp, ← Functor.map_comp]
  have h := (SSet.barycentricSubdivisionLastVertex.naturality f).symm
  rw [Functor.id_map] at h
  exact congr_arg (((SSet.chainComplexFunctor C).obj R).map) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainMap_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainMap_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainMap_naturality ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainMap_naturality



noncomputable def nonemptyFaceBarycenter {n : ℕ}
    (A : Finset (Fin (n + 1))) (hA : A.Nonempty) :
    stdSimplex ℝ (Fin (n + 1)) := by
  letI : Nonempty A := hA.coe_sort
  exact stdSimplex.map Subtype.val
    (stdSimplex.barycenter : stdSimplex ℝ A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceBarycenter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceBarycenter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceBarycenter ``Submission.DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceBarycenter

@[simp]
theorem nonemptyFaceBarycenter_apply {n : ℕ}
    (A : Finset (Fin (n + 1))) (hA : A.Nonempty)
    (i : Fin (n + 1)) :
    nonemptyFaceBarycenter A hA i =
      if i ∈ A then (A.card : ℝ)⁻¹ else 0 := by
  classical
  unfold nonemptyFaceBarycenter
  dsimp only [stdSimplex.map, stdSimplex.barycenter]
  change (FunOnFinite.linearMap ℝ ℝ Subtype.val
    (fun _ : A => (Fintype.card A : ℝ)⁻¹)) i = _
  rw [FunOnFinite.linearMap_apply_apply]
  by_cases hi : i ∈ A
  · have hfilter :
        Finset.univ.filter (fun x : A => (x : Fin (n + 1)) = i) =
          {⟨i, hi⟩} := by
      ext x
      simp [Subtype.ext_iff]
    rw [hfilter]
    simp only [Finset.sum_singleton, if_pos hi, Fintype.card_coe]
  · simp [hi]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceBarycenter_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceBarycenter_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceBarycenter_apply ``Submission.DifferentialGeometry.Topology.SphereSeparation.nonemptyFaceBarycenter_apply

noncomputable def affineStandardSimplexMap
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (v : ι → stdSimplex ℝ κ) :
    C(stdSimplex ℝ ι, stdSimplex ℝ κ) where
  toFun x :=
    ⟨fun k => ∑ i, x i * v i k, by
      constructor
      · intro k
        exact Finset.sum_nonneg fun i _ =>
          mul_nonneg (stdSimplex.zero_le x i) (stdSimplex.zero_le (v i) k)
      · rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, stdSimplex.sum_eq_one, mul_one]
        exact stdSimplex.sum_eq_one x⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro k
    exact continuous_finsetSum Finset.univ fun i _ =>
      ((continuous_apply i).comp continuous_subtype_val).mul continuous_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.affineStandardSimplexMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.affineStandardSimplexMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.affineStandardSimplexMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.affineStandardSimplexMap

@[simp]
theorem affineStandardSimplexMap_apply
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (v : ι → stdSimplex ℝ κ) (x : stdSimplex ℝ ι) (k : κ) :
    affineStandardSimplexMap v x k = ∑ i, x i * v i k :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.affineStandardSimplexMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.affineStandardSimplexMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.affineStandardSimplexMap_apply ``Submission.DifferentialGeometry.Topology.SphereSeparation.affineStandardSimplexMap_apply

@[simp]
theorem affineStandardSimplexMap_vertex
    {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (v : ι → stdSimplex ℝ κ) (i : ι) :
    affineStandardSimplexMap v (stdSimplex.vertex i) = v i := by
  classical
  ext k
  rw [affineStandardSimplexMap_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [stdSimplex.vertex, hji]
  · simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.affineStandardSimplexMap_vertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.affineStandardSimplexMap_vertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.affineStandardSimplexMap_vertex ``Submission.DifferentialGeometry.Topology.SphereSeparation.affineStandardSimplexMap_vertex


noncomputable def barycentricPrefix {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    Finset (Fin (n + 1)) :=
  (Finset.Iic k).image σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix

theorem barycentricPrefix_nonempty {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    (barycentricPrefix σ k).Nonempty := by
  classical
  exact ⟨σ k, Finset.mem_image.2 ⟨k, by simp, rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix_nonempty ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix_nonempty

@[simp]
theorem mem_barycentricPrefix_iff {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (k i : Fin (n + 1)) :
    i ∈ barycentricPrefix σ k ↔ σ.symm i ≤ k := by
  classical
  rw [barycentricPrefix, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro hi
    exact ⟨σ.symm i, by simpa, σ.apply_symm_apply i⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.mem_barycentricPrefix_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.mem_barycentricPrefix_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.mem_barycentricPrefix_iff ``Submission.DifferentialGeometry.Topology.SphereSeparation.mem_barycentricPrefix_iff


theorem barycentricPrefix_mono {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) :
    Monotone (barycentricPrefix σ) := by
  intro k l hkl i hi
  rw [mem_barycentricPrefix_iff] at hi ⊢
  exact hi.trans hkl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix_mono ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix_mono

@[simp]
theorem barycentricPrefix_card {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    (barycentricPrefix σ k).card = k + 1 := by
  classical
  rw [barycentricPrefix, Finset.card_image_of_injective _ σ.injective,
    Fin.card_Iic]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix_card then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix_card"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix_card ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix_card

@[simp]
theorem barycentricPrefix_last {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) :
    barycentricPrefix σ (Fin.last n) = Finset.univ := by
  ext i
  simp only [mem_barycentricPrefix_iff, Finset.mem_univ, iff_true]
  exact Fin.le_last _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix_last then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix_last"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix_last ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricPrefix_last

theorem barycentricPrefixBarycenter_apply {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (k i : Fin (n + 1)) :
    nonemptyFaceBarycenter (barycentricPrefix σ k)
        (barycentricPrefix_nonempty σ k) i =
      if σ.symm i ≤ k then ((k : ℕ) + 1 : ℝ)⁻¹ else 0 := by
  rw [nonemptyFaceBarycenter_apply, barycentricPrefix_card]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricPrefixBarycenter_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricPrefixBarycenter_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricPrefixBarycenter_apply ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricPrefixBarycenter_apply

noncomputable def barycentricContractionFactor (n : ℕ) : ℝ :=
  (n : ℝ) / (n + 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricContractionFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricContractionFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricContractionFactor ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricContractionFactor

theorem barycentricContractionFactor_nonneg (n : ℕ) :
    0 ≤ barycentricContractionFactor n := by
  exact div_nonneg (Nat.cast_nonneg n) (by positivity)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricContractionFactor_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricContractionFactor_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricContractionFactor_nonneg ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricContractionFactor_nonneg

theorem barycentricContractionFactor_lt_one (n : ℕ) :
    barycentricContractionFactor n < 1 := by
  rw [barycentricContractionFactor, div_lt_one (by positivity)]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricContractionFactor_lt_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricContractionFactor_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricContractionFactor_lt_one ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricContractionFactor_lt_one

private theorem inv_natSucc_sub_inv_natSucc_le_barycentricContractionFactor
    {n k l : ℕ} (hln : l ≤ n) :
    ((k : ℝ) + 1)⁻¹ - ((l : ℝ) + 1)⁻¹ ≤
      barycentricContractionFactor n := by
  have hk : ((k : ℝ) + 1)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    norm_num
  have hnl : ((n : ℝ) + 1)⁻¹ ≤ ((l : ℝ) + 1)⁻¹ := by
    apply (inv_le_inv₀ (by positivity) (by positivity)).2
    exact_mod_cast Nat.add_le_add_right hln 1
  calc
    ((k : ℝ) + 1)⁻¹ - ((l : ℝ) + 1)⁻¹ ≤
        1 - ((n : ℝ) + 1)⁻¹ := sub_le_sub hk hnl
    _ = barycentricContractionFactor n := by
      rw [barycentricContractionFactor]
      field_simp
      ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.inv_natSucc_sub_inv_natSucc_le_barycentricContractionFactor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.inv_natSucc_sub_inv_natSucc_le_barycentricContractionFactor target :: scope.openDecls } }

private theorem inv_natSucc_le_barycentricContractionFactor
    {n l : ℕ} (hl : 1 ≤ l) (hln : l ≤ n) :
    ((l : ℝ) + 1)⁻¹ ≤ barycentricContractionFactor n := by
  rw [barycentricContractionFactor, inv_eq_one_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  norm_cast
  nlinarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.inv_natSucc_le_barycentricContractionFactor
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.inv_natSucc_le_barycentricContractionFactor target :: scope.openDecls } }

theorem dist_barycentricPrefixBarycenter_apply_le_of_le {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) {k l : Fin (n + 1)} (hkl : k ≤ l)
    (i : Fin (n + 1)) :
    _root_.Dist.dist
        (nonemptyFaceBarycenter (barycentricPrefix σ k)
          (barycentricPrefix_nonempty σ k) i)
        (nonemptyFaceBarycenter (barycentricPrefix σ l)
          (barycentricPrefix_nonempty σ l) i) ≤
      barycentricContractionFactor n := by
  rw [barycentricPrefixBarycenter_apply,
    barycentricPrefixBarycenter_apply, Real.dist_eq]
  by_cases hik : σ.symm i ≤ k
  · have hil : σ.symm i ≤ l := hik.trans hkl
    rw [if_pos hik, if_pos hil]
    have hinv : ((l : ℝ) + 1)⁻¹ ≤ ((k : ℝ) + 1)⁻¹ := by
      apply (inv_le_inv₀ (by positivity) (by positivity)).2
      exact_mod_cast Nat.add_le_add_right (show (k : ℕ) ≤ l from hkl) 1
    rw [abs_of_nonneg (sub_nonneg.2 hinv)]
    exact inv_natSucc_sub_inv_natSucc_le_barycentricContractionFactor
      (Nat.le_of_lt_succ l.isLt)
  · rw [if_neg hik]
    by_cases hil : σ.symm i ≤ l
    · rw [if_pos hil, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
      have hlt : k < l := lt_of_le_of_ne hkl fun h => hik (h ▸ hil)
      exact inv_natSucc_le_barycentricContractionFactor
        (Nat.succ_le_iff.2 (Nat.zero_lt_of_lt (show (k : ℕ) < l from hlt)))
        (Nat.le_of_lt_succ l.isLt)
    · rw [if_neg hil, sub_zero, abs_zero]
      exact barycentricContractionFactor_nonneg n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.dist_barycentricPrefixBarycenter_apply_le_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.dist_barycentricPrefixBarycenter_apply_le_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.dist_barycentricPrefixBarycenter_apply_le_of_le ``Submission.DifferentialGeometry.Topology.SphereSeparation.dist_barycentricPrefixBarycenter_apply_le_of_le

noncomputable def barycentricPermutationSimplexMap {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 1))) :=
  affineStandardSimplexMap fun k =>
    nonemptyFaceBarycenter (barycentricPrefix σ k)
      (barycentricPrefix_nonempty σ k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricPermutationSimplexMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricPermutationSimplexMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricPermutationSimplexMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricPermutationSimplexMap

theorem dist_affineStandardSimplexMap_le_of_pairwise
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (v : ι → stdSimplex ℝ κ) {r : ℝ} (hr : 0 ≤ r)
    (hv : ∀ i j k, _root_.Dist.dist (v i k) (v j k) ≤ r)
    (x y : stdSimplex ℝ ι) :
    _root_.Dist.dist (affineStandardSimplexMap v x)
        (affineStandardSimplexMap v y) ≤ r := by
  rw [Subtype.dist_eq, dist_pi_le_iff hr]
  intro k
  rw [Real.dist_eq]
  have hdecomp :
      (∑ i, x i * v i k) - (∑ j, y j * v j k) =
        ∑ i, ∑ j, (x i * y j) * (v i k - v j k) := by
    calc
      (∑ i, x i * v i k) - (∑ j, y j * v j k) =
          (∑ i, x i * v i k) * (∑ j, y j) -
            (∑ i, x i) * (∑ j, y j * v j k) := by
              rw [stdSimplex.sum_eq_one x, stdSimplex.sum_eq_one y]
              ring
      _ = ∑ i, ∑ j, (x i * y j) * (v i k - v j k) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
  change |(∑ i, x i * v i k) - (∑ j, y j * v j k)| ≤ r
  rw [hdecomp]
  calc
    |∑ i, ∑ j, (x i * y j) * (v i k - v j k)| ≤
        ∑ i, |∑ j, (x i * y j) * (v i k - v j k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |(x i * y j) * (v i k - v j k)| := by
      exact Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, (x i * y j) * r := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (mul_nonneg
        (stdSimplex.zero_le x i) (stdSimplex.zero_le y j))]
      exact mul_le_mul_of_nonneg_left
        (by simpa [Real.dist_eq] using hv i j k)
        (mul_nonneg (stdSimplex.zero_le x i) (stdSimplex.zero_le y j))
    _ = r := by
      calc
        (∑ i, ∑ j, (x i * y j) * r) =
            ∑ i, (x i * r) * ∑ j, y j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = ∑ i, x i * r := by rw [stdSimplex.sum_eq_one y]; simp
        _ = r := by rw [← Finset.sum_mul, stdSimplex.sum_eq_one x, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.dist_affineStandardSimplexMap_le_of_pairwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.dist_affineStandardSimplexMap_le_of_pairwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.dist_affineStandardSimplexMap_le_of_pairwise ``Submission.DifferentialGeometry.Topology.SphereSeparation.dist_affineStandardSimplexMap_le_of_pairwise

theorem dist_barycentricPermutationSimplexMap_le {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1)))
    (x y : stdSimplex ℝ (Fin (n + 1))) :
    _root_.Dist.dist (barycentricPermutationSimplexMap σ x)
        (barycentricPermutationSimplexMap σ y) ≤
      barycentricContractionFactor n := by
  apply dist_affineStandardSimplexMap_le_of_pairwise _
    (barycentricContractionFactor_nonneg n)
  intro k l i
  rcases le_total k l with hkl | hlk
  · exact dist_barycentricPrefixBarycenter_apply_le_of_le σ hkl i
  · rw [dist_comm]
    exact dist_barycentricPrefixBarycenter_apply_le_of_le σ hlk i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.dist_barycentricPermutationSimplexMap_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.dist_barycentricPermutationSimplexMap_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.dist_barycentricPermutationSimplexMap_le ``Submission.DifferentialGeometry.Topology.SphereSeparation.dist_barycentricPermutationSimplexMap_le

theorem diam_range_barycentricPermutationSimplexMap_le {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) :
    Metric.diam (Set.range (barycentricPermutationSimplexMap σ)) ≤
      barycentricContractionFactor n := by
  apply Metric.diam_le_of_forall_dist_le
    (barycentricContractionFactor_nonneg n)
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  exact dist_barycentricPermutationSimplexMap_le σ x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.diam_range_barycentricPermutationSimplexMap_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.diam_range_barycentricPermutationSimplexMap_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.diam_range_barycentricPermutationSimplexMap_le ``Submission.DifferentialGeometry.Topology.SphereSeparation.diam_range_barycentricPermutationSimplexMap_le



noncomputable def standardSimplexStraightLineHomotopy
    {Z : Type} [TopologicalSpace Z] {n : ℕ}
    (f g : C(Z, stdSimplex ℝ (Fin (n + 1)))) :
    ContinuousMap.Homotopy f g where
  toFun p :=
    ⟨p.1.1 • (g p.2 : Fin (n + 1) → ℝ) +
        (1 - p.1.1) • (f p.2 : Fin (n + 1) → ℝ), by
      exact (convex_stdSimplex ℝ _)
        (g p.2).2 (f p.2).2 p.1.2.1
        (sub_nonneg.2 p.1.2.2) (add_sub_cancel _ _)⟩
  continuous_toFun := by fun_prop
  map_zero_left x := by
    apply Subtype.ext
    funext i
    simp
    rfl
  map_one_left x := by
    apply Subtype.ext
    funext i
    simp
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.standardSimplexStraightLineHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.standardSimplexStraightLineHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.standardSimplexStraightLineHomotopy ``Submission.DifferentialGeometry.Topology.SphereSeparation.standardSimplexStraightLineHomotopy

noncomputable def topCatStandardSimplexStraightLineHomotopy
    {Z : TopCat} {n : ℕ}
    (f g : Z ⟶ TopCat.of (stdSimplex ℝ (Fin (n + 1)))) :
    TopCat.Homotopy f g :=
  standardSimplexStraightLineHomotopy f.hom g.hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topCatStandardSimplexStraightLineHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topCatStandardSimplexStraightLineHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topCatStandardSimplexStraightLineHomotopy ``Submission.DifferentialGeometry.Topology.SphereSeparation.topCatStandardSimplexStraightLineHomotopy

noncomputable def standardSimplexPrismChainHomotopy
    {C : Type} [_root_.CategoryTheory.Category C] [_root_.CategoryTheory.Preadditive C] [HasCoproducts.{0} C]
    {Z : TopCat} {n : ℕ}
    (f g : Z ⟶ TopCat.of (stdSimplex ℝ (Fin (n + 1)))) (R : C) :
    _root_.Homotopy
      (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map f)
      (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map g) :=
  (topCatStandardSimplexStraightLineHomotopy f g).singularChainComplexFunctorObjMap R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.standardSimplexPrismChainHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.standardSimplexPrismChainHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.standardSimplexPrismChainHomotopy ``Submission.DifferentialGeometry.Topology.SphereSeparation.standardSimplexPrismChainHomotopy

noncomputable def barycentricPermutationSimplexPrismChainHomotopy
    {C : Type} [_root_.CategoryTheory.Category C] [_root_.CategoryTheory.Preadditive C] [HasCoproducts.{0} C]
    {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (R : C) :
    _root_.Homotopy
      (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map
        (𝟙 (TopCat.of (stdSimplex ℝ (Fin (n + 1))))))
      (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map
        (TopCat.ofHom (barycentricPermutationSimplexMap σ))) :=
  standardSimplexPrismChainHomotopy _ _ R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricPermutationSimplexPrismChainHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricPermutationSimplexPrismChainHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricPermutationSimplexPrismChainHomotopy ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricPermutationSimplexPrismChainHomotopy

theorem barycentricPermutationSimplex_homologyMap_eq
    {C : Type} [_root_.CategoryTheory.Category C] [_root_.CategoryTheory.Preadditive C] [HasCoproducts.{0} C]
    [_root_.CategoryTheory.CategoryWithHomology C]
    {n q : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (R : C) :
    HomologicalComplex.homologyMap
        (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map
          (𝟙 (TopCat.of (stdSimplex ℝ (Fin (n + 1)))))) q =
      HomologicalComplex.homologyMap
        (((AlgebraicTopology.singularChainComplexFunctor C).obj R).map
          (TopCat.ofHom (barycentricPermutationSimplexMap σ))) q :=
  (barycentricPermutationSimplexPrismChainHomotopy σ R).homologyMap_eq q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricPermutationSimplex_homologyMap_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricPermutationSimplex_homologyMap_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricPermutationSimplex_homologyMap_eq ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricPermutationSimplex_homologyMap_eq

@[simp]
theorem barycentricPermutationSimplexMap_vertex {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    barycentricPermutationSimplexMap σ (stdSimplex.vertex k) =
      nonemptyFaceBarycenter (barycentricPrefix σ k)
        (barycentricPrefix_nonempty σ k) := by
  classical
  exact affineStandardSimplexMap_vertex _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricPermutationSimplexMap_vertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricPermutationSimplexMap_vertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricPermutationSimplexMap_vertex ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricPermutationSimplexMap_vertex

noncomputable def singularSimplexBarycentricPiece
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (s : C(stdSimplex ℝ (Fin (n + 1)), X))
    (σ : Equiv.Perm (Fin (n + 1))) :
    C(stdSimplex ℝ (Fin (n + 1)), X) :=
  s.comp (barycentricPermutationSimplexMap σ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularSimplexBarycentricPiece then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularSimplexBarycentricPiece"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularSimplexBarycentricPiece ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularSimplexBarycentricPiece

theorem range_singularSimplexBarycentricPiece_subset
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (s : C(stdSimplex ℝ (Fin (n + 1)), X))
    (σ : Equiv.Perm (Fin (n + 1))) :
    Set.range (singularSimplexBarycentricPiece s σ) ⊆ Set.range s := by
  rintro _ ⟨x, rfl⟩
  exact ⟨barycentricPermutationSimplexMap σ x, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.range_singularSimplexBarycentricPiece_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.range_singularSimplexBarycentricPiece_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.range_singularSimplexBarycentricPiece_subset ``Submission.DifferentialGeometry.Topology.SphereSeparation.range_singularSimplexBarycentricPiece_subset

theorem range_singularSimplexBarycentricPiece_subset_of_subset
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (s : C(stdSimplex ℝ (Fin (n + 1)), X))
    (σ : Equiv.Perm (Fin (n + 1))) (A : Set X)
    (hs : Set.range s ⊆ A) :
    Set.range (singularSimplexBarycentricPiece s σ) ⊆ A :=
  (range_singularSimplexBarycentricPiece_subset s σ).trans hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.range_singularSimplexBarycentricPiece_subset_of_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.range_singularSimplexBarycentricPiece_subset_of_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.range_singularSimplexBarycentricPiece_subset_of_subset ``Submission.DifferentialGeometry.Topology.SphereSeparation.range_singularSimplexBarycentricPiece_subset_of_subset

theorem singularSimplexBarycentricPiece_smallFor_twoSets
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (V W : Set X) (s : C(stdSimplex ℝ (Fin (n + 1)), X))
    (σ : Equiv.Perm (Fin (n + 1)))
    (hs : Set.range s ⊆ V ∨ Set.range s ⊆ W) :
    Set.range (singularSimplexBarycentricPiece s σ) ⊆ V ∨
      Set.range (singularSimplexBarycentricPiece s σ) ⊆ W :=
  hs.imp
    (range_singularSimplexBarycentricPiece_subset_of_subset s σ V)
    (range_singularSimplexBarycentricPiece_subset_of_subset s σ W)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularSimplexBarycentricPiece_smallFor_twoSets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularSimplexBarycentricPiece_smallFor_twoSets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularSimplexBarycentricPiece_smallFor_twoSets ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularSimplexBarycentricPiece_smallFor_twoSets



noncomputable def barycentricPieceOfSingularSimplex
    (X : TopCat) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (TopCat.toSSet.obj X) _⦋n⦌ :=
  (X.toSSetObjEquiv _).symm
    ((X.toSSetObjEquiv _ s).comp (barycentricPermutationSimplexMap σ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricPieceOfSingularSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricPieceOfSingularSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricPieceOfSingularSimplex ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricPieceOfSingularSimplex

@[simp]
theorem toSSetObjEquiv_barycentricPieceOfSingularSimplex
    (X : TopCat) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌)
    (σ : Equiv.Perm (Fin (n + 1))) :
    X.toSSetObjEquiv _ (barycentricPieceOfSingularSimplex X s σ) =
      (X.toSSetObjEquiv _ s).comp (barycentricPermutationSimplexMap σ) :=
  Equiv.apply_symm_apply _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.toSSetObjEquiv_barycentricPieceOfSingularSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.toSSetObjEquiv_barycentricPieceOfSingularSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.toSSetObjEquiv_barycentricPieceOfSingularSimplex ``Submission.DifferentialGeometry.Topology.SphereSeparation.toSSetObjEquiv_barycentricPieceOfSingularSimplex


theorem barycentricPieceOfSingularSimplex_naturality
    {X Y : TopCat} (f : X ⟶ Y) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (TopCat.toSSet.map f).app _
        (barycentricPieceOfSingularSimplex X s σ) =
      barycentricPieceOfSingularSimplex Y
        ((TopCat.toSSet.map f).app _ s) σ := by
  apply (Y.toSSetObjEquiv _).injective
  ext x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricPieceOfSingularSimplex_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricPieceOfSingularSimplex_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricPieceOfSingularSimplex_naturality ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricPieceOfSingularSimplex_naturality

theorem barycentricPieceOfSingularSimplex_zero
    (X : TopCat) (s : (TopCat.toSSet.obj X) _⦋0⦌)
    (σ : Equiv.Perm (Fin 1)) :
    barycentricPieceOfSingularSimplex X s σ = s := by
  apply (X.toSSetObjEquiv _).injective
  rw [toSSetObjEquiv_barycentricPieceOfSingularSimplex]
  ext x
  exact congr_arg (X.toSSetObjEquiv _ s) (Subsingleton.elim _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricPieceOfSingularSimplex_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricPieceOfSingularSimplex_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricPieceOfSingularSimplex_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricPieceOfSingularSimplex_zero

noncomputable def barycentricSubdivisionDegreeMap (X : TopCat) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X n ⟶
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).X n :=
  Sigma.desc fun s =>
    ∑ σ : Equiv.Perm (Fin (n + 1)),
      (Equiv.Perm.sign σ : ℤ) •
        (TopCat.toSSet.obj X).ιChainComplex
          (R := ModuleCat.of ℤ ℤ)
          (barycentricPieceOfSingularSimplex X s σ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionDegreeMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionDegreeMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionDegreeMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionDegreeMap

@[reassoc (attr := simp)]
theorem ιChainComplex_barycentricSubdivisionDegreeMap
    (X : TopCat) {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s ≫
        barycentricSubdivisionDegreeMap X n =
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        (Equiv.Perm.sign σ : ℤ) •
          (TopCat.toSSet.obj X).ιChainComplex
            (R := ModuleCat.of ℤ ℤ)
            (barycentricPieceOfSingularSimplex X s σ) := by
  dsimp [barycentricSubdivisionDegreeMap, SSet.ιChainComplex]
  apply Sigma.ι_desc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ιChainComplex_barycentricSubdivisionDegreeMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ιChainComplex_barycentricSubdivisionDegreeMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ιChainComplex_barycentricSubdivisionDegreeMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.ιChainComplex_barycentricSubdivisionDegreeMap

theorem barycentricSubdivisionDegreeMap_naturality
    {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    barycentricSubdivisionDegreeMap X n ≫
        ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map f).f n) =
      ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map f).f n) ≫
        barycentricSubdivisionDegreeMap Y n := by
  change barycentricSubdivisionDegreeMap X n ≫
      (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)).f n =
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)).f n ≫
      barycentricSubdivisionDegreeMap Y n
  apply SSet.chainComplex_hom_ext
  intro s
  rw [← Category.assoc, ιChainComplex_barycentricSubdivisionDegreeMap,
    Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, SSet.ι_chainComplexMap_f]
  rw [← Category.assoc, SSet.ι_chainComplexMap_f,
    ιChainComplex_barycentricSubdivisionDegreeMap]
  apply Finset.sum_congr rfl
  intro σ _
  rw [barycentricPieceOfSingularSimplex_naturality]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionDegreeMap_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionDegreeMap_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionDegreeMap_naturality ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionDegreeMap_naturality


theorem barycentricSubdivisionDegreeMap_zero (X : TopCat) :
    barycentricSubdivisionDegreeMap X 0 = 𝟙 _ := by
  apply SSet.chainComplex_hom_ext
  intro s
  rw [ιChainComplex_barycentricSubdivisionDegreeMap]
  simp [barycentricPieceOfSingularSimplex_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionDegreeMap_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionDegreeMap_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionDegreeMap_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionDegreeMap_zero

def BarycentricSubdivisionBoundaryCompatible (X : TopCat) : Prop :=
  ∀ n : ℕ,
    barycentricSubdivisionDegreeMap X (n + 1) ≫
        (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).obj X).d (n + 1) n =
      (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).obj X).d (n + 1) n ≫
        barycentricSubdivisionDegreeMap X n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.BarycentricSubdivisionBoundaryCompatible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.BarycentricSubdivisionBoundaryCompatible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.BarycentricSubdivisionBoundaryCompatible ``Submission.DifferentialGeometry.Topology.SphereSeparation.BarycentricSubdivisionBoundaryCompatible

noncomputable def barycentricSubdivisionChainEndomorphism
    (X : TopCat) (h : BarycentricSubdivisionBoundaryCompatible X) :
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj X ⟶
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj X where
  f n := barycentricSubdivisionDegreeMap X n
  comm' i j hij := by
    obtain rfl : i = j + 1 := by simpa using hij.symm
    exact h j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainEndomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainEndomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainEndomorphism ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainEndomorphism

theorem barycentricSubdivisionChainEndomorphism_naturality
    {X Y : TopCat} (f : X ⟶ Y)
    (hX : BarycentricSubdivisionBoundaryCompatible X)
    (hY : BarycentricSubdivisionBoundaryCompatible Y) :
    barycentricSubdivisionChainEndomorphism X hX ≫
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map f =
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map f ≫
        barycentricSubdivisionChainEndomorphism Y hY := by
  apply HomologicalComplex.hom_ext
  intro n
  exact barycentricSubdivisionDegreeMap_naturality f n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainEndomorphism_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainEndomorphism_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainEndomorphism_naturality ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainEndomorphism_naturality

@[simp]
theorem barycentricSubdivisionChainEndomorphism_f_zero
    (X : TopCat) (h : BarycentricSubdivisionBoundaryCompatible X) :
    (barycentricSubdivisionChainEndomorphism X h).f 0 = 𝟙 _ :=
  barycentricSubdivisionDegreeMap_zero X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainEndomorphism_f_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainEndomorphism_f_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainEndomorphism_f_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.barycentricSubdivisionChainEndomorphism_f_zero

end DifferentialGeometry.Topology.SphereSeparation
