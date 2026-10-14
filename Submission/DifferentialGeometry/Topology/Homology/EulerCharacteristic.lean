import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.Homotopy.Contractible

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology
open scoped _root_.ContinuousMap

universe u

namespace DifferentialGeometry.Homology

variable (k : Type u) [Field k]

def finiteHomologyType (X : TopCat.{u}) : Prop :=
  (∀ n : ℕ, FiniteDimensional k
    (((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X)) ∧
    ∃ N : ℕ, ∀ n : ℕ, N < n →
      _root_.CategoryTheory.Limits.IsZero (((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.finiteHomologyType then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.finiteHomologyType"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.finiteHomologyType ``Submission.DifferentialGeometry.Homology.finiteHomologyType

def eulerChar (X : TopCat.{u}) : ℤ :=
  GradedObject.eulerChar (ComplexShape.down ℕ)
    (fun n ↦ ((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.eulerChar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.eulerChar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.eulerChar ``Submission.DifferentialGeometry.Homology.eulerChar

variable {X Y : TopCat.{u}}

@[simps hom inv]
def singularHomologyIso (e : X ≃ₕ Y) (n : ℕ) :
    ((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X ≅
      ((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj Y where
  hom := ((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
    (TopCat.ofHom e.toFun)
  inv := ((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
    (TopCat.ofHom e.invFun)
  hom_inv_id := by
    rw [← Functor.map_comp]
    have H : TopCat.Homotopy
        (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 X) := e.left_inv.some
    have h := H.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of k k) n
    change ((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map _ =
      ((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map (𝟙 X) at h
    exact h.trans (CategoryTheory.Functor.map_id _ X)
  inv_hom_id := by
    rw [← Functor.map_comp]
    have H : TopCat.Homotopy
        (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 Y) := e.right_inv.some
    have h := H.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of k k) n
    change ((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map _ =
      ((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map (𝟙 Y) at h
    exact h.trans (CategoryTheory.Functor.map_id _ Y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularHomologyIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularHomologyIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularHomologyIso ``Submission.DifferentialGeometry.Homology.singularHomologyIso


@[simp]
theorem singularHomologyIso_refl (X : TopCat.{u}) (n : ℕ) :
    singularHomologyIso k (ContinuousMap.HomotopyEquiv.refl X) n = Iso.refl _ := by
  apply Iso.ext
  exact CategoryTheory.Functor.map_id
    ((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)) X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularHomologyIso_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularHomologyIso_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularHomologyIso_refl ``Submission.DifferentialGeometry.Homology.singularHomologyIso_refl


@[simp]
theorem singularHomologyIso_symm (e : X ≃ₕ Y) (n : ℕ) :
    singularHomologyIso k e.symm n = (singularHomologyIso k e n).symm := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularHomologyIso_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularHomologyIso_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularHomologyIso_symm ``Submission.DifferentialGeometry.Homology.singularHomologyIso_symm


@[simp]
theorem singularHomologyIso_trans {Z : TopCat.{u}} (e : X ≃ₕ Y) (f : Y ≃ₕ Z) (n : ℕ) :
    singularHomologyIso k (e.trans f) n =
      singularHomologyIso k e n ≪≫ singularHomologyIso k f n := by
  apply Iso.ext
  exact CategoryTheory.Functor.map_comp
    ((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k))
      (TopCat.ofHom e.toFun) (TopCat.ofHom f.toFun)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularHomologyIso_trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularHomologyIso_trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularHomologyIso_trans ``Submission.DifferentialGeometry.Homology.singularHomologyIso_trans


theorem finiteHomologyType_iff_of_homotopyEquiv (e : X ≃ₕ Y) :
    finiteHomologyType k X ↔ finiteHomologyType k Y := by
  suffices h : ∀ {A B : TopCat.{u}}, A ≃ₕ B →
      finiteHomologyType k A → finiteHomologyType k B from ⟨h e, h e.symm⟩
  intro A B e hA
  constructor
  · intro n
    have := hA.1 n
    exact (singularHomologyIso k e n).toLinearEquiv.finiteDimensional
  · obtain ⟨N, hN⟩ := hA.2
    exact ⟨N, fun n hn ↦ (hN n hn).of_iso (singularHomologyIso k e n).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.finiteHomologyType_iff_of_homotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.finiteHomologyType_iff_of_homotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.finiteHomologyType_iff_of_homotopyEquiv ``Submission.DifferentialGeometry.Homology.finiteHomologyType_iff_of_homotopyEquiv


theorem finiteHomologyType_iff_of_homeomorph (e : X ≃ₜ Y) :
    finiteHomologyType k X ↔ finiteHomologyType k Y :=
  finiteHomologyType_iff_of_homotopyEquiv k e.toHomotopyEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.finiteHomologyType_iff_of_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.finiteHomologyType_iff_of_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.finiteHomologyType_iff_of_homeomorph ``Submission.DifferentialGeometry.Homology.finiteHomologyType_iff_of_homeomorph


theorem eulerChar_eq_of_homotopyEquiv (e : X ≃ₕ Y) :
    eulerChar k X = eulerChar k Y := by
  apply finsum_congr
  intro n
  rw [(singularHomologyIso k e n).toLinearEquiv.finrank_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.eulerChar_eq_of_homotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.eulerChar_eq_of_homotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.eulerChar_eq_of_homotopyEquiv ``Submission.DifferentialGeometry.Homology.eulerChar_eq_of_homotopyEquiv


theorem eulerChar_eq_of_homeomorph (e : X ≃ₜ Y) :
    eulerChar k X = eulerChar k Y :=
  eulerChar_eq_of_homotopyEquiv k e.toHomotopyEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.eulerChar_eq_of_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.eulerChar_eq_of_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.eulerChar_eq_of_homeomorph ``Submission.DifferentialGeometry.Homology.eulerChar_eq_of_homeomorph

theorem eulerChar_eq_sum (N : ℕ)
    (hN : ∀ n : ℕ, N < n →
      _root_.CategoryTheory.Limits.IsZero (((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X)) :
    eulerChar k X = ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * Module.finrank k
      (((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X) := by
  unfold eulerChar
  convert GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset
    (ComplexShape.down ℕ)
    (fun n ↦ ((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X)
    (Finset.range (N + 1)) ?_ using 1
  · simp [ComplexShape.χ]
  · rw [GradedObject.finrankSupport_subset_iff]
    intro n hn
    have hz := hN n (by simpa [Finset.mem_range] using hn)
    have := ModuleCat.subsingleton_of_isZero hz
    exact Module.finrank_zero_of_subsingleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.eulerChar_eq_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.eulerChar_eq_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.eulerChar_eq_sum ``Submission.DifferentialGeometry.Homology.eulerChar_eq_sum


theorem isZero_singularHomology_of_isEmpty [IsEmpty X] (n : ℕ) :
    IsZero (((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X) := by
  by_cases hn : n = 0
  · subst n
    have hz : _root_.CategoryTheory.Limits.IsZero (∐ fun _ : X ↦ ModuleCat.of k k) := by
      rw [IsZero.iff_id_eq_zero]
      apply Sigma.hom_ext
      intro x
      exact isEmptyElim x
    exact hz.of_iso (_root_.AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace
      (ModuleCat.{u} k) (ModuleCat.of k k) X)
  · exact _root_.AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{u} k) n (ModuleCat.of k k) X hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.isZero_singularHomology_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.isZero_singularHomology_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.isZero_singularHomology_of_isEmpty ``Submission.DifferentialGeometry.Homology.isZero_singularHomology_of_isEmpty

private def homologyZeroEquivPi [Fintype X] [TotallyDisconnectedSpace X] :
    ((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)).obj X ≃ₗ[k]
      (X → k) := by
  classical
  exact ((_root_.AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace (ModuleCat.{u} k)
    (ModuleCat.of k k) X).trans (ModuleCat.coprodIsoDirectSum
      (fun _ : X ↦ ModuleCat.of k k))).toLinearEquiv.trans
        (DirectSum.linearEquivFunOnFintype k X (fun _ ↦ k))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.homologyZeroEquivPi
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.homologyZeroEquivPi target :: scope.openDecls } }

theorem finiteHomologyType_of_finite_totallyDisconnected [Finite X] [TotallyDisconnectedSpace X] :
    finiteHomologyType k X := by
  let := Fintype.ofFinite X
  constructor
  · intro n
    by_cases hn : n = 0
    · subst n
      exact (homologyZeroEquivPi k (X := X)).symm.finiteDimensional
    · have := ModuleCat.subsingleton_of_isZero
        (_root_.AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
          (ModuleCat.{u} k) n (ModuleCat.of k k) X hn)
      infer_instance
  · exact ⟨0, fun n hn ↦ _root_.AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{u} k) n (ModuleCat.of k k) X hn.ne'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.finiteHomologyType_of_finite_totallyDisconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.finiteHomologyType_of_finite_totallyDisconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.finiteHomologyType_of_finite_totallyDisconnected ``Submission.DifferentialGeometry.Homology.finiteHomologyType_of_finite_totallyDisconnected

theorem eulerChar_of_finite_totallyDisconnected [Finite X] [TotallyDisconnectedSpace X] :
    eulerChar k X = Nat.card X := by
  let := Fintype.ofFinite X
  rw [eulerChar_eq_sum k 0 (fun n hn ↦
    _root_.AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{u} k) n (ModuleCat.of k k) X hn.ne')]
  simp [(homologyZeroEquivPi k (X := X)).finrank_eq, Nat.card_eq_fintype_card]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.eulerChar_of_finite_totallyDisconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.eulerChar_of_finite_totallyDisconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.eulerChar_of_finite_totallyDisconnected ``Submission.DifferentialGeometry.Homology.eulerChar_of_finite_totallyDisconnected


theorem finiteHomologyType_of_subsingleton [Subsingleton X] : finiteHomologyType k X :=
  finiteHomologyType_of_finite_totallyDisconnected k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.finiteHomologyType_of_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.finiteHomologyType_of_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.finiteHomologyType_of_subsingleton ``Submission.DifferentialGeometry.Homology.finiteHomologyType_of_subsingleton


@[simp]
theorem eulerChar_of_isEmpty [IsEmpty X] : eulerChar k X = 0 := by
  rw [eulerChar_of_finite_totallyDisconnected k]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.eulerChar_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.eulerChar_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.eulerChar_of_isEmpty ``Submission.DifferentialGeometry.Homology.eulerChar_of_isEmpty


@[simp]
theorem eulerChar_of_unique [Unique X] : eulerChar k X = 1 := by
  rw [eulerChar_of_finite_totallyDisconnected k]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.eulerChar_of_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.eulerChar_of_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.eulerChar_of_unique ``Submission.DifferentialGeometry.Homology.eulerChar_of_unique


theorem finiteHomologyType_of_contractible [ContractibleSpace X] : finiteHomologyType k X := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv X PUnit.{u + 1}
  exact (finiteHomologyType_iff_of_homotopyEquiv k
    (Y := TopCat.of PUnit.{u + 1}) e).mpr (finiteHomologyType_of_subsingleton k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.finiteHomologyType_of_contractible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.finiteHomologyType_of_contractible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.finiteHomologyType_of_contractible ``Submission.DifferentialGeometry.Homology.finiteHomologyType_of_contractible


theorem eulerChar_of_contractible [ContractibleSpace X] : eulerChar k X = 1 := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv X PUnit.{u + 1}
  exact (eulerChar_eq_of_homotopyEquiv k
    (Y := TopCat.of PUnit.{u + 1}) e).trans (eulerChar_of_unique k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.eulerChar_of_contractible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.eulerChar_of_contractible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.eulerChar_of_contractible ``Submission.DifferentialGeometry.Homology.eulerChar_of_contractible

end DifferentialGeometry.Homology
