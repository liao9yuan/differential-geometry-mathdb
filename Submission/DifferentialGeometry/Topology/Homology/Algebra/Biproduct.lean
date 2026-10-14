import Submission.DifferentialGeometry.Topology.Homology.Algebra.FiniteType
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

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
variable {k : Type u} [Ring k]
  (K L : ChainComplex (ModuleCat.{v} k) ℕ)


def homologyBiprodIso (n : ℕ) :
    (K ⊞ L).homology n ≅ K.homology n ⊞ L.homology n := by
  let F := _root_.HomologicalComplex.homologyFunctor (ModuleCat.{v} k) (ComplexShape.down ℕ) n
  letI := _root_.CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts F
  exact F.mapBiprod K L

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.homologyBiprodIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.homologyBiprodIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.homologyBiprodIso ``Submission.DifferentialGeometry.HomologicalComplex.homologyBiprodIso


@[reassoc (attr := simp)]
theorem homologyBiprodIso_fst (n : ℕ) :
    (homologyBiprodIso K L n).hom ≫ biprod.fst =
      _root_.HomologicalComplex.homologyMap (biprod.fst : K ⊞ L ⟶ K) n :=
  by unfold homologyBiprodIso; exact biprod.lift_fst _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.homologyBiprodIso_fst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.homologyBiprodIso_fst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.homologyBiprodIso_fst ``Submission.DifferentialGeometry.HomologicalComplex.homologyBiprodIso_fst


@[reassoc (attr := simp)]
theorem homologyBiprodIso_snd (n : ℕ) :
    (homologyBiprodIso K L n).hom ≫ biprod.snd =
      _root_.HomologicalComplex.homologyMap (biprod.snd : K ⊞ L ⟶ L) n :=
  by unfold homologyBiprodIso; exact biprod.lift_snd _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.homologyBiprodIso_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.homologyBiprodIso_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.homologyBiprodIso_snd ``Submission.DifferentialGeometry.HomologicalComplex.homologyBiprodIso_snd

section Field
variable {k : Type u} [Field k] (K L : ChainComplex (ModuleCat.{v} k) ℕ)


theorem finiteHomologyType_biprod
    (hK : finiteHomologyType K) (hL : finiteHomologyType L) :
    finiteHomologyType (K ⊞ L) := by
  let S := ShortComplex.mk (biprod.inl : K ⟶ K ⊞ L) biprod.snd (by simp)
  exact finiteHomologyType_middle S
    (ShortComplex.Splitting.ofHasBinaryBiproduct K L).shortExact hK hL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.finiteHomologyType_biprod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.finiteHomologyType_biprod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.finiteHomologyType_biprod ``Submission.DifferentialGeometry.HomologicalComplex.finiteHomologyType_biprod

theorem homologyEulerChar_biprod
    (hK : finiteHomologyType K) (hL : finiteHomologyType L) :
    (K ⊞ L).homologyEulerChar = K.homologyEulerChar + L.homologyEulerChar := by
  have hKL := finiteHomologyType_biprod K L hK hL
  have := hK.1
  have := hL.1
  have := hKL.1
  let S := ShortComplex.mk (biprod.inl : K ⟶ K ⊞ L) biprod.snd (by simp)
  exact homologyEulerChar_additive S
    (ShortComplex.Splitting.ofHasBinaryBiproduct K L).shortExact hK.2 hKL.2 hL.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.homologyEulerChar_biprod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.homologyEulerChar_biprod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.homologyEulerChar_biprod ``Submission.DifferentialGeometry.HomologicalComplex.homologyEulerChar_biprod

end Field
end DifferentialGeometry.HomologicalComplex
