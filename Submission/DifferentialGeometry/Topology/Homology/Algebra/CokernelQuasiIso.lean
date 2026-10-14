import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits
noncomputable section
namespace DifferentialGeometry.HomologicalComplex
variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  {A K B L : _root_.HomologicalComplex C c}
  (i : A ⟶ K) (j : B ⟶ L)


abbrev cokernelSequence : _root_.CategoryTheory.ShortComplex (_root_.HomologicalComplex C c) :=
  ShortComplex.mk i (cokernel.π i) (cokernel.condition i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.cokernelSequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.cokernelSequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.cokernelSequence ``Submission.DifferentialGeometry.HomologicalComplex.cokernelSequence


theorem cokernelSequence_shortExact [_root_.CategoryTheory.Mono i] : (cokernelSequence i).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (_root_.CategoryTheory.Limits.cokernelIsCokernel i)
  mono_f := inferInstance
  epi_g := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.cokernelSequence_shortExact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.cokernelSequence_shortExact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.cokernelSequence_shortExact ``Submission.DifferentialGeometry.HomologicalComplex.cokernelSequence_shortExact

theorem quasiIso_cokernel_map [_root_.CategoryTheory.Mono i] [_root_.CategoryTheory.Mono j]
    (a : A ⟶ B) (b : K ⟶ L) (hab : i ≫ b = a ≫ j)
    (ha : QuasiIso a) (hb : QuasiIso b) : QuasiIso (cokernel.map i j a b hab) := by
  let φ : cokernelSequence i ⟶ cokernelSequence j := {
    τ₁ := a
    τ₂ := b
    τ₃ := cokernel.map i j a b hab
    comm₁₂ := hab.symm
    comm₂₃ := (cokernel.π_desc _ _ _).symm }
  exact _root_.HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
    (cokernelSequence_shortExact i) (cokernelSequence_shortExact j) ha hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.quasiIso_cokernel_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.quasiIso_cokernel_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.quasiIso_cokernel_map ``Submission.DifferentialGeometry.HomologicalComplex.quasiIso_cokernel_map

end DifferentialGeometry.HomologicalComplex
