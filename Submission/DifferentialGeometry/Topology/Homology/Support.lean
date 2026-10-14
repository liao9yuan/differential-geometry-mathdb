import Submission.DifferentialGeometry.Topology.Homology.SingularSubcomplex
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.ConcreteCategory
import Submission.DifferentialGeometry.MathlibCompat.CompactSpaceStdSimplex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.Submission.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.CategoryTheory.Limits _root_.AlgebraicTopology _root_.HomologicalComplex _root_.Submission.HomologicalComplex _root_.Simplicial

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

lemma exists_finset_sum_ι {ι : Type u} (Z : ι → ModuleCat.{u} ℤ)
    (x : (∐ Z : ModuleCat.{u} ℤ)) :
    ∃ (S : Finset ι) (y : ∀ i, Z i), x = ∑ i ∈ S, Sigma.ι Z i (y i) := by
  classical
  set d := (ModuleCat.coprodIsoDirectSum Z).hom x with hd
  refine ⟨d.support, fun i => d i, ?_⟩
  have h1 : x = (ModuleCat.coprodIsoDirectSum Z).inv d := by
    rw [hd, ← ModuleCat.comp_apply]
    simp
  have h2 := DirectSum.sum_support_of d
  rw [h1]
  conv_lhs => rw [← h2]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← DirectSum.lof_eq_of ℤ, ModuleCat.lof_coprodIsoDirectSum_inv_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.exists_finset_sum_ι then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.exists_finset_sum_ι"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.exists_finset_sum_ι ``Submission.DifferentialGeometry.Topology.SingularPair.exists_finset_sum_ι

variable (R : ModuleCat.{u} ℤ) (X : TopCat.{u})

def simplexSupport (k : ℕ) (S : Finset ((TopCat.toSSet.obj X) _⦋k⦌)) : Set X :=
  ⋃ σ ∈ S, Set.range (X.toSSetObjEquiv _ σ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.simplexSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.simplexSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.simplexSupport ``Submission.DifferentialGeometry.Topology.SingularPair.simplexSupport

lemma isCompact_simplexSupport (k : ℕ) (S : Finset ((TopCat.toSSet.obj X) _⦋k⦌)) :
    IsCompact (simplexSupport X k S) :=
  S.isCompact_biUnion fun σ _ => MathlibCompat.isCompact_singularSimplex_range X k σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isCompact_simplexSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isCompact_simplexSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isCompact_simplexSupport ``Submission.DifferentialGeometry.Topology.SingularPair.isCompact_simplexSupport

lemma mem_singSub_simplexSupport {k : ℕ} {S : Finset ((TopCat.toSSet.obj X) _⦋k⦌)}
    {σ : (TopCat.toSSet.obj X) _⦋k⦌} (hσ : σ ∈ S) :
    σ ∈ (singSub X (simplexSupport X k S)).obj _ :=
  (mem_singSub_iff X _ σ).2 (Set.subset_biUnion_of_mem (u := fun σ => Set.range
    (X.toSSetObjEquiv _ σ)) hσ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mem_singSub_simplexSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mem_singSub_simplexSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mem_singSub_simplexSupport ``Submission.DifferentialGeometry.Topology.SingularPair.mem_singSub_simplexSupport

abbrev singSubChainMap (K : Set X) :
    ((singSub X K : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).chainComplex R ⟶ singularChains R X :=
  SSet.chainComplexMap (singSub X K).ι R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.singSubChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.singSubChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.singSubChainMap ``Submission.DifferentialGeometry.Topology.SingularPair.singSubChainMap

instance _root_.Submission.DifferentialGeometry.Topology.SingularPair.instMonoModuleCatIntFNatSingSubChainMap (K : Set X) (k : ℕ) : _root_.CategoryTheory.Mono ((singSubChainMap R X K).f k) :=
  inferInstanceAs (_root_.CategoryTheory.Mono ((SSet.chainComplexMap (singSub X K).pair.hom R).f k))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.instMonoModuleCatIntFNatSingSubChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.instMonoModuleCatIntFNatSingSubChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.instMonoModuleCatIntFNatSingSubChainMap ``Submission.DifferentialGeometry.Topology.SingularPair.instMonoModuleCatIntFNatSingSubChainMap

instance _root_.Submission.DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatSingSubChainMap (K : Set X) : _root_.CategoryTheory.Mono (singSubChainMap R X K) :=
  inferInstanceAs (_root_.CategoryTheory.Mono (SSet.chainComplexMap (singSub X K).pair.hom R))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatSingSubChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatSingSubChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatSingSubChainMap ``Submission.DifferentialGeometry.Topology.SingularPair.instMonoChainComplexModuleCatIntNatSingSubChainMap

theorem exists_isCompact_singSubChainMap_f_eq (k : ℕ) (x : (singularChains R X).X k) :
    ∃ K : Set X, IsCompact K ∧ ∃ w, (singSubChainMap R X K).f k w = x := by
  obtain ⟨S, y, hS⟩ :=
    exists_finset_sum_ι (fun _ : (TopCat.toSSet.obj X) _⦋k⦌ => R) x
  refine ⟨simplexSupport X k S, isCompact_simplexSupport X k S, ?_⟩
  have hmem :
      x ∈ LinearMap.range ((singSubChainMap R X (simplexSupport X k S)).f k).hom := by
    rw [hS]
    refine Submodule.sum_mem _ fun σ hσ => ?_
    refine ⟨SSet.ιChainComplex (R := R) (X := ((singSub X (simplexSupport X k S) :
      (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}))
      ⟨σ, mem_singSub_simplexSupport X hσ⟩ (y σ), ?_⟩
    exact ConcreteCategory.congr_hom
      (SSet.ι_chainComplexMap_f _ _ (singSub X (simplexSupport X k S)).ι R
        ⟨σ, mem_singSub_simplexSupport X hσ⟩) (y σ)
  obtain ⟨w, hw⟩ := hmem
  exact ⟨w, hw⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.exists_isCompact_singSubChainMap_f_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.exists_isCompact_singSubChainMap_f_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.exists_isCompact_singSubChainMap_f_eq ``Submission.DifferentialGeometry.Topology.SingularPair.exists_isCompact_singSubChainMap_f_eq

lemma homologyπ_mem_range_homologyMap {L M : ChainComplex (ModuleCat.{u} ℤ) ℕ} (φ : L ⟶ M)
    [∀ j, _root_.CategoryTheory.Mono (φ.f j)] (k : ℕ) (z : M.cycles k) (w : L.X k)
    (hw : φ.f k w = M.iCycles k z) :
    M.homologyπ k z ∈ Set.range (_root_.HomologicalComplex.homologyMap φ k) := by
  have hdw : L.d k ((ComplexShape.down ℕ).next k) w = 0 := by
    apply (ModuleCat.mono_iff_injective (φ.f _)).1 inferInstance
    rw [← ModuleCat.comp_apply, ← φ.comm, ModuleCat.comp_apply, hw, ← ModuleCat.comp_apply,
      _root_.HomologicalComplex.iCycles_d, map_zero]
    simp
  have hw' : L.iCycles k (L.cyclesMk w _ rfl hdw) = w := L.i_cyclesMk w _ rfl hdw
  have hcyc : _root_.HomologicalComplex.cyclesMap φ k (L.cyclesMk w _ rfl hdw) = z := by
    apply (ModuleCat.mono_iff_injective (M.iCycles k)).1 inferInstance
    rw [← ModuleCat.comp_apply, _root_.HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply, hw', hw]
  refine ⟨L.homologyπ k (L.cyclesMk w _ rfl hdw), ?_⟩
  rw [← ModuleCat.comp_apply, _root_.HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply, hcyc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homologyπ_mem_range_homologyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homologyπ_mem_range_homologyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homologyπ_mem_range_homologyMap ``Submission.DifferentialGeometry.Topology.SingularPair.homologyπ_mem_range_homologyMap

theorem exists_isCompact_mem_range_inclMap (k : ℕ) (c : singularHomology R X k) :
    ∃ K : Set X, IsCompact K ∧ c ∈ Set.range (inclMap R X K k) := by
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective ((singularChains R X).homologyπ k)).1 inferInstance c
  obtain ⟨K, hK, w, hw⟩ :=
    exists_isCompact_singSubChainMap_f_eq R X k ((singularChains R X).iCycles k z)
  obtain ⟨a, ha⟩ := homologyπ_mem_range_homologyMap (singSubChainMap R X K) k z w hw
  refine ⟨K, hK, (singularSubcomplexHomologyIso X R K k).hom a, ?_⟩
  rw [← ModuleCat.comp_apply, singularSubcomplexHomologyIso_hom_inclMap]
  exact ha.trans hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.exists_isCompact_mem_range_inclMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.exists_isCompact_mem_range_inclMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.exists_isCompact_mem_range_inclMap ``Submission.DifferentialGeometry.Topology.SingularPair.exists_isCompact_mem_range_inclMap

lemma inclMap_inclOfLE {A B : Set X} (h : A ⊆ B) (n : ℕ) :
    homologyMap ((singularChainFunctor R).map (inclOfLE h)) n ≫ inclMap R X B n = inclMap R X A n := by
  change _root_.HomologicalComplex.homologyMap ((singularChainFunctor R).map (inclOfLE h)) n ≫ _root_.HomologicalComplex.homologyMap ((singularChainFunctor R).map (incl X B)) n =
    _root_.HomologicalComplex.homologyMap ((singularChainFunctor R).map (incl X A)) n
  rw [← _root_.HomologicalComplex.homologyMap_comp, ← Functor.map_comp, inclOfLE_incl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.inclMap_inclOfLE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.inclMap_inclOfLE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.inclMap_inclOfLE ``Submission.DifferentialGeometry.Topology.SingularPair.inclMap_inclOfLE

lemma range_inclMap_mono {A B : Set X} (h : A ⊆ B) (n : ℕ) :
    Set.range (inclMap R X A n) ⊆ Set.range (inclMap R X B n) := by
  rintro _ ⟨a, rfl⟩
  refine ⟨homologyMap ((singularChainFunctor R).map (inclOfLE h)) n a, ?_⟩
  rw [← inclMap_inclOfLE R X h n]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.range_inclMap_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.range_inclMap_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.range_inclMap_mono ``Submission.DifferentialGeometry.Topology.SingularPair.range_inclMap_mono

theorem exists_isCompact_superset_mem_range_inclMap (k : ℕ) (c : singularHomology R X k) {K₀ : Set X}
    (hK₀ : IsCompact K₀) :
    ∃ K : Set X, IsCompact K ∧ K₀ ⊆ K ∧ c ∈ Set.range (inclMap R X K k) := by
  obtain ⟨K, hK, hc⟩ := exists_isCompact_mem_range_inclMap R X k c
  exact ⟨K₀ ∪ K, hK₀.union hK, Set.subset_union_left,
    range_inclMap_mono R X Set.subset_union_right k hc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.exists_isCompact_superset_mem_range_inclMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.exists_isCompact_superset_mem_range_inclMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.exists_isCompact_superset_mem_range_inclMap ``Submission.DifferentialGeometry.Topology.SingularPair.exists_isCompact_superset_mem_range_inclMap

instance hasDimensionLT_zero_pair_empty_left : (pair X ∅).left.HasDimensionLT 0 := by
  rw [← SSet.notNonempty_iff_hasDimensionLT_zero]
  rintro ⟨σ⟩
  exact ((TopCat.of (∅ : Set X)).toSSetObjEquiv _ σ (Classical.arbitrary _)).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.hasDimensionLT_zero_pair_empty_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.hasDimensionLT_zero_pair_empty_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.hasDimensionLT_zero_pair_empty_left ``Submission.DifferentialGeometry.Topology.SingularPair.hasDimensionLT_zero_pair_empty_left

instance isIso_relπ_empty (k : ℕ) : _root_.CategoryTheory.IsIso (relπ R X ∅ k) :=
  inferInstanceAs (_root_.CategoryTheory.IsIso ((pair X ∅).homologyπ R k))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_relπ_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_relπ_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_relπ_empty ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_relπ_empty

def relativeHomologyEmptyIso (k : ℕ) : relativeHomology R X ∅ k ≅ singularHomology R X k := (_root_.CategoryTheory.asIso (relπ R X ∅ k)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyEmptyIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyEmptyIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyEmptyIso ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyEmptyIso

@[simp]
lemma relativeHomologyEmptyIso_inv (k : ℕ) : (relativeHomologyEmptyIso R X k).inv = relπ R X ∅ k := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyEmptyIso_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyEmptyIso_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyEmptyIso_inv ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyEmptyIso_inv

@[reassoc (attr := simp)]
lemma relπ_relativeHomologyEmptyIso_hom (k : ℕ) : relπ R X ∅ k ≫ (relativeHomologyEmptyIso R X k).hom = 𝟙 _ := by
  rw [← relativeHomologyEmptyIso_inv, Iso.inv_hom_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relπ_relativeHomologyEmptyIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relπ_relativeHomologyEmptyIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relπ_relativeHomologyEmptyIso_hom ``Submission.DifferentialGeometry.Topology.SingularPair.relπ_relativeHomologyEmptyIso_hom

@[reassoc (attr := simp)]
lemma relativeHomologyEmptyIso_hom_relπ (k : ℕ) : (relativeHomologyEmptyIso R X k).hom ≫ relπ R X ∅ k = 𝟙 _ := by
  rw [← relativeHomologyEmptyIso_inv, Iso.hom_inv_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyEmptyIso_hom_relπ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyEmptyIso_hom_relπ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyEmptyIso_hom_relπ ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyEmptyIso_hom_relπ

lemma incl_univ_eq : incl X Set.univ = (TopCat.isoOfHomeo (Homeomorph.Set.univ X)).hom := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.incl_univ_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.incl_univ_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.incl_univ_eq ``Submission.DifferentialGeometry.Topology.SingularPair.incl_univ_eq

instance isIso_incl_univ : _root_.CategoryTheory.IsIso (incl X Set.univ) := by
  rw [incl_univ_eq]
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_incl_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_incl_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_incl_univ ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_incl_univ

instance isIso_pair_univ_hom : _root_.CategoryTheory.IsIso (pair X Set.univ).hom :=
  inferInstanceAs (_root_.CategoryTheory.IsIso (TopCat.toSSet.map (incl X Set.univ)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_pair_univ_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_pair_univ_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_pair_univ_hom ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_pair_univ_hom

theorem isZero_relativeHomology_univ (k : ℕ) : _root_.CategoryTheory.Limits.IsZero (relativeHomology R X Set.univ k) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) k).map_isZero
    (SSetPair.isZero_chainComplex (pair X Set.univ) R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_univ ``Submission.DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_univ

end DifferentialGeometry.Topology.SingularPair
