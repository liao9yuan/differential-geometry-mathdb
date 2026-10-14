import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Endomorphism

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits
noncomputable section
universe u v
namespace DifferentialGeometry.HomologicalComplex
variable {k : Type u} [Ring k] {ι : Type*} {c : ComplexShape ι}
  (K : _root_.HomologicalComplex (ModuleCat.{v} k) c) (B : End K)


theorem homologyMap_pow_eq_id (H : Homotopy B (𝟙 K)) (N : ℕ) (n : ι) :
    _root_.HomologicalComplex.homologyMap (B ^ N) n = 𝟙 _ := by
  have hB : _root_.HomologicalComplex.homologyMap B n = 𝟙 _ :=
    (H.homologyMap_eq n).trans (_root_.HomologicalComplex.homologyMap_id K n)
  induction N with
  | zero => exact _root_.HomologicalComplex.homologyMap_id K n
  | succ N hN =>
    rw [pow_succ, End.mul_def, _root_.HomologicalComplex.homologyMap_comp, hN, hB,
      Category.id_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.homologyMap_pow_eq_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.homologyMap_pow_eq_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.homologyMap_pow_eq_id ``Submission.DifferentialGeometry.HomologicalComplex.homologyMap_pow_eq_id

theorem isZero_homology_of_locallyNilpotent (H : Homotopy B (𝟙 K))
    (hnil : ∀ n : ι, ∀ x : K.X n, ∃ N : ℕ, ((B ^ N).f n) x = 0) (n : ι) :
    IsZero (K.homology n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro a
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance a
  obtain ⟨N, hN⟩ := hnil n ((K.iCycles n) z)
  have hz : (_root_.HomologicalComplex.cyclesMap (B ^ N) n) z = 0 := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    have hh := ConcreteCategory.congr_hom (_root_.HomologicalComplex.cyclesMap_i (B ^ N) n) z
    change (K.iCycles n) ((_root_.HomologicalComplex.cyclesMap (B ^ N) n) z) =
      ((B ^ N).f n) ((K.iCycles n) z) at hh
    simpa only [map_zero] using hh.trans hN
  have hh := ConcreteCategory.congr_hom
    (_root_.HomologicalComplex.homologyπ_naturality (B ^ N) n) z
  rw [homologyMap_pow_eq_id K B H N n] at hh
  change (K.homologyπ n) z =
    (K.homologyπ n) ((_root_.HomologicalComplex.cyclesMap (B ^ N) n) z) at hh
  rw [hz, map_zero] at hh
  exact hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.isZero_homology_of_locallyNilpotent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.isZero_homology_of_locallyNilpotent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.isZero_homology_of_locallyNilpotent ``Submission.DifferentialGeometry.HomologicalComplex.isZero_homology_of_locallyNilpotent

end DifferentialGeometry.HomologicalComplex
