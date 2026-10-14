import Submission.DifferentialGeometry.Topology.SimplicialSet.FiniteRealizationHomology
import Submission.DifferentialGeometry.Topology.SimplicialSet.EulerCharacteristic
import Submission.DifferentialGeometry.Topology.Homology.EulerCharacteristic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology

universe u

namespace DifferentialGeometry.SSet

variable (k : Type u) [Field k] (X : _root_.SSet.{u}) [X.Finite]

theorem finiteHomologyType_realization :
    DifferentialGeometry.Homology.finiteHomologyType k (_root_.SSet.toTop.obj X) := by
  constructor
  · intro n
    have := finiteDimensional_homology X (ModuleCat.of k k) n
    exact (realizationHomologyIso (ModuleCat.of k k) X n).toLinearEquiv.finiteDimensional
  · obtain ⟨d, hd⟩ := X.hasDimensionLT_of_finite
    exact ⟨d, fun n hn ↦
      (X.isZero_homology_of_hasDimensionLT (ModuleCat.of k k) n d hn.le).of_iso
        (realizationHomologyIso (ModuleCat.of k k) X n).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.finiteHomologyType_realization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.finiteHomologyType_realization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.finiteHomologyType_realization ``Submission.DifferentialGeometry.SSet.finiteHomologyType_realization

theorem eulerChar_realization_eq_homologyEulerChar :
    DifferentialGeometry.Homology.eulerChar k (_root_.SSet.toTop.obj X) =
      (X.chainComplex (ModuleCat.of k k)).homologyEulerChar := by
  apply finsum_congr
  intro n
  rw [(realizationHomologyIso (ModuleCat.of k k) X n).toLinearEquiv.finrank_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.eulerChar_realization_eq_homologyEulerChar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.eulerChar_realization_eq_homologyEulerChar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.eulerChar_realization_eq_homologyEulerChar ``Submission.DifferentialGeometry.SSet.eulerChar_realization_eq_homologyEulerChar

theorem eulerChar_realization_eq_sum_card_nonDegenerate (d : ℕ) [X.HasDimensionLT d] :
    DifferentialGeometry.Homology.eulerChar k (_root_.SSet.toTop.obj X) =
      ∑ n ∈ Finset.range d, (-1 : ℤ) ^ n * Nat.card (X.nonDegenerate n) := by
  rw [eulerChar_realization_eq_homologyEulerChar,
    homologyEulerChar_eq_sum_card_nonDegenerate (X := X) (k := k) d]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.eulerChar_realization_eq_sum_card_nonDegenerate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.eulerChar_realization_eq_sum_card_nonDegenerate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.eulerChar_realization_eq_sum_card_nonDegenerate ``Submission.DifferentialGeometry.SSet.eulerChar_realization_eq_sum_card_nonDegenerate

theorem eulerChar_realization_eq_finsum_card_nonDegenerate :
    DifferentialGeometry.Homology.eulerChar k (_root_.SSet.toTop.obj X) =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * Nat.card (X.nonDegenerate n) := by
  rw [eulerChar_realization_eq_homologyEulerChar,
    homologyEulerChar_eq_finsum_card_nonDegenerate]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.eulerChar_realization_eq_finsum_card_nonDegenerate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.eulerChar_realization_eq_finsum_card_nonDegenerate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.eulerChar_realization_eq_finsum_card_nonDegenerate ``Submission.DifferentialGeometry.SSet.eulerChar_realization_eq_finsum_card_nonDegenerate

theorem eulerChar_realization_eq_of_coefficients (K : Type u) [Field K] :
    DifferentialGeometry.Homology.eulerChar k (_root_.SSet.toTop.obj X) =
      DifferentialGeometry.Homology.eulerChar K (_root_.SSet.toTop.obj X) := by
  rw [eulerChar_realization_eq_finsum_card_nonDegenerate,
    eulerChar_realization_eq_finsum_card_nonDegenerate]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SSet.eulerChar_realization_eq_of_coefficients then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SSet.eulerChar_realization_eq_of_coefficients"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SSet.eulerChar_realization_eq_of_coefficients ``Submission.DifferentialGeometry.SSet.eulerChar_realization_eq_of_coefficients

end DifferentialGeometry.SSet
