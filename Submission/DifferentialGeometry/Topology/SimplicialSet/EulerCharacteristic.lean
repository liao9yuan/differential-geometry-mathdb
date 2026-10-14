import Submission.DifferentialGeometry.Topology.Homology.Algebra.EulerCharacteristic
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Dimension.Constructions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.DirectSum

universe u

namespace DifferentialGeometry.SSet

variable {k : Type u} [Field k] (X : _root_.SSet.{u}) (R : ModuleCat.{u} k)

private def normalizedChainComplexXIso (n : ℕ) :
    (X.normalizedChainComplex R).X n ≅ ModuleCat.of k (⨁ (_ : X.nonDegenerate n), R) := by
  classical
  exact (X.isColimitCofanNormalizedChainComplex R n).coconePointUniqueUpToIso
    (ModuleCat.coproductCoconeIsColimit (fun _ : X.nonDegenerate n => R))

run_cmd do
  let target := ``Submission.DifferentialGeometry.SSet.normalizedChainComplexXIso
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.SSet.normalizedChainComplexXIso target :: scope.openDecls } }

theorem finiteDimensional_normalizedChainComplex_X (n : ℕ)
    [Finite (X.nonDegenerate n)] [FiniteDimensional k R] :
    FiniteDimensional k ((X.normalizedChainComplex R).X n) := by
  classical
  let : Fintype (X.nonDegenerate n) := Fintype.ofFinite (X.nonDegenerate n)
  let e := (normalizedChainComplexXIso X R n).toLinearEquiv.trans
    (DirectSum.linearEquivFunOnFintype k (X.nonDegenerate n) (fun _ => R))
  exact e.symm.finiteDimensional

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.finiteDimensional_normalizedChainComplex_X then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.finiteDimensional_normalizedChainComplex_X"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.finiteDimensional_normalizedChainComplex_X ``Submission.DifferentialGeometry.SSet.finiteDimensional_normalizedChainComplex_X

theorem finrank_normalizedChainComplex_X (n : ℕ) [Finite (X.nonDegenerate n)] :
    Module.finrank k ((X.normalizedChainComplex R).X n) =
      Nat.card (X.nonDegenerate n) * Module.finrank k R := by
  classical
  let : Fintype (X.nonDegenerate n) := Fintype.ofFinite (X.nonDegenerate n)
  let e := (normalizedChainComplexXIso X R n).toLinearEquiv.trans
    (finsuppLEquivDirectSum k R (X.nonDegenerate n)).symm
  rw [e.finrank_eq, Module.finrank_finsupp]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.finrank_normalizedChainComplex_X then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.finrank_normalizedChainComplex_X"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.finrank_normalizedChainComplex_X ``Submission.DifferentialGeometry.SSet.finrank_normalizedChainComplex_X

theorem finiteDimensional_homology (n : ℕ)
    [Finite (X.nonDegenerate n)] [FiniteDimensional k R] :
    FiniteDimensional k (X.homology (C := ModuleCat.{u} k) R n) := by
  have := finiteDimensional_normalizedChainComplex_X X R n
  have := DifferentialGeometry.HomologicalComplex.finiteDimensional_homology (X.normalizedChainComplex R) n
  exact (isoOfQuasiIsoAt (X.toNormalizedChainComplex R) n).symm.toLinearEquiv.finiteDimensional

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.finiteDimensional_homology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.finiteDimensional_homology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.finiteDimensional_homology ``Submission.DifferentialGeometry.SSet.finiteDimensional_homology

theorem homologyEulerChar_chainComplex_eq_normalizedChainComplex :
    (X.chainComplex R).homologyEulerChar = (X.normalizedChainComplex R).homologyEulerChar := by
  unfold _root_.HomologicalComplex.homologyEulerChar GradedObject.eulerChar
  congr 1
  funext n
  congr 2
  exact (isoOfQuasiIsoAt (X.toNormalizedChainComplex R) n).toLinearEquiv.finrank_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.homologyEulerChar_chainComplex_eq_normalizedChainComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.homologyEulerChar_chainComplex_eq_normalizedChainComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.homologyEulerChar_chainComplex_eq_normalizedChainComplex ``Submission.DifferentialGeometry.SSet.homologyEulerChar_chainComplex_eq_normalizedChainComplex

theorem eulerChar_normalizedChainComplex_eq_homologyEulerChar
    [X.Finite] [FiniteDimensional k R] :
    (X.normalizedChainComplex R).eulerChar = (X.chainComplex R).homologyEulerChar := by
  have : ∀ n : ℕ, FiniteDimensional k ((X.normalizedChainComplex R).X n) :=
    fun n => finiteDimensional_normalizedChainComplex_X X R n
  rw [homologyEulerChar_chainComplex_eq_normalizedChainComplex]
  apply DifferentialGeometry.HomologicalComplex.eulerChar_eq_homologyEulerChar
  obtain ⟨d, _⟩ := X.hasDimensionLT_of_finite
  exact ⟨d, fun n hn => X.isZero_normalizedChainComplex_X_of_hasDimensionLT R n d hn.le⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.eulerChar_normalizedChainComplex_eq_homologyEulerChar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.eulerChar_normalizedChainComplex_eq_homologyEulerChar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.eulerChar_normalizedChainComplex_eq_homologyEulerChar ``Submission.DifferentialGeometry.SSet.eulerChar_normalizedChainComplex_eq_homologyEulerChar

variable (k)

theorem homologyEulerChar_eq_sum_card_nonDegenerate [X.Finite]
    (d : ℕ) [X.HasDimensionLT d] :
    (X.chainComplex (ModuleCat.of k k)).homologyEulerChar =
      ∑ n ∈ Finset.range d, (-1 : ℤ) ^ n * Nat.card (X.nonDegenerate n) := by
  rw [← eulerChar_normalizedChainComplex_eq_homologyEulerChar]
  have hs : GradedObject.finrankSupport (X.normalizedChainComplex (ModuleCat.of k k)).X ⊆
      Finset.range d := by
    rw [GradedObject.finrankSupport_subset_iff]
    intro n hn
    have := ModuleCat.subsingleton_of_isZero
      (X.isZero_normalizedChainComplex_X_of_hasDimensionLT (ModuleCat.of k k) n d
        (by simpa [Finset.mem_range] using hn))
    exact Module.finrank_zero_of_subsingleton
  rw [_root_.HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset _ _ hs]
  simp [finrank_normalizedChainComplex_X, ComplexShape.χ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.homologyEulerChar_eq_sum_card_nonDegenerate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.homologyEulerChar_eq_sum_card_nonDegenerate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.homologyEulerChar_eq_sum_card_nonDegenerate ``Submission.DifferentialGeometry.SSet.homologyEulerChar_eq_sum_card_nonDegenerate

theorem homologyEulerChar_eq_finsum_card_nonDegenerate [X.Finite] :
    (X.chainComplex (ModuleCat.of k k)).homologyEulerChar =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * Nat.card (X.nonDegenerate n) := by
  obtain ⟨d, _⟩ := X.hasDimensionLT_of_finite
  rw [homologyEulerChar_eq_sum_card_nonDegenerate (X := X) (k := k) d]
  symm
  apply finsum_eq_sum_of_support_subset
  intro n hn
  by_contra hnd
  have hdn : d ≤ n := by simpa [Finset.mem_range] using hnd
  have : IsEmpty (X.nonDegenerate n) := by
    rw [X.nonDegenerate_eq_empty_of_hasDimensionLT d n hdn]
    infer_instance
  simp only [Function.mem_support, Nat.card_of_isEmpty, Nat.cast_zero, _root_.MulZeroClass.mul_zero,
    ne_eq, not_true_eq_false] at hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.homologyEulerChar_eq_finsum_card_nonDegenerate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.homologyEulerChar_eq_finsum_card_nonDegenerate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.homologyEulerChar_eq_finsum_card_nonDegenerate ``Submission.DifferentialGeometry.SSet.homologyEulerChar_eq_finsum_card_nonDegenerate

theorem homologyEulerChar_eq_of_coefficients [X.Finite] (K : Type u) [Field K] :
    (X.chainComplex (ModuleCat.of k k)).homologyEulerChar =
      (X.chainComplex (ModuleCat.of K K)).homologyEulerChar := by
  rw [homologyEulerChar_eq_finsum_card_nonDegenerate,
    homologyEulerChar_eq_finsum_card_nonDegenerate]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.homologyEulerChar_eq_of_coefficients then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.homologyEulerChar_eq_of_coefficients"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.homologyEulerChar_eq_of_coefficients ``Submission.DifferentialGeometry.SSet.homologyEulerChar_eq_of_coefficients

end DifferentialGeometry.SSet
