import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Concrete cycle classes in the original categorical module homology -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

namespace DifferentialGeometry.Topology

variable {R : Type u} [Ring R]

/-- The actual homology class of a concrete cycle, in the original
categorical homology object. -/
def moduleHomologyClass (S : _root_.CategoryTheory.ShortComplex (ModuleCat.{v} R)) :
    LinearMap.ker S.g.hom →ₗ[R] S.homology :=
  S.homologyπ.hom.comp S.moduleCatCyclesIso.inv.hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.moduleHomologyClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.moduleHomologyClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.moduleHomologyClass ``Submission.DifferentialGeometry.Topology.moduleHomologyClass

/-- The original concrete cycle class is the SAME coset under the
canonical identification of categorical homology with cycles modulo boundaries. -/
theorem moduleHomologyClass_quotient (S : _root_.CategoryTheory.ShortComplex (ModuleCat.{v} R))
    (c : LinearMap.ker S.g.hom) :
    S.moduleCatHomologyIso.hom (moduleHomologyClass S c) =
      (LinearMap.range S.moduleCatToCycles).mkQ c := by
  change (S.moduleCatCyclesIso.inv ≫ S.homologyπ ≫ S.moduleCatHomologyIso.hom) c = _
  rw [S.moduleCatCyclesIso_inv_π_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.moduleHomologyClass_quotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.moduleHomologyClass_quotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.moduleHomologyClass_quotient ``Submission.DifferentialGeometry.Topology.moduleHomologyClass_quotient

/-- Every element of the original categorical homology has a concrete cycle representative. -/
theorem moduleHomologyClass_surjective (S : _root_.CategoryTheory.ShortComplex (ModuleCat.{v} R)) :
    Function.Surjective (moduleHomologyClass S) :=
  (ModuleCat.epi_iff_surjective (S.moduleCatCyclesIso.inv ≫ S.homologyπ)).mp inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.moduleHomologyClass_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.moduleHomologyClass_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.moduleHomologyClass_surjective ``Submission.DifferentialGeometry.Topology.moduleHomologyClass_surjective

/-- A concrete cycle has zero class exactly when it is an actual boundary. -/
theorem moduleHomologyClass_eq_zero_iff (S : _root_.CategoryTheory.ShortComplex (ModuleCat.{v} R))
    (c : LinearMap.ker S.g.hom) :
    moduleHomologyClass S c = 0 ↔ ∃ b : S.X₁, S.f b = c.val := by
  have hi := (ModuleCat.mono_iff_injective S.moduleCatHomologyIso.hom).mp inferInstance
  rw [← hi.eq_iff, moduleHomologyClass_quotient, map_zero]
  change (Submodule.Quotient.mk c : LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, Subtype.ext hb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.moduleHomologyClass_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.moduleHomologyClass_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.moduleHomologyClass_eq_zero_iff ``Submission.DifferentialGeometry.Topology.moduleHomologyClass_eq_zero_iff

/-- Equality of original homology classes is equivalent to an actual
chain bounding the difference of the same cycles. -/
theorem moduleHomologyClass_eq_iff (S : _root_.CategoryTheory.ShortComplex (ModuleCat.{v} R))
    (c d : LinearMap.ker S.g.hom) :
    moduleHomologyClass S c = moduleHomologyClass S d ↔
      ∃ b : S.X₁, S.f b = c.val - d.val := by
  rw [← sub_eq_zero, ← map_sub, moduleHomologyClass_eq_zero_iff]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.moduleHomologyClass_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.moduleHomologyClass_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.moduleHomologyClass_eq_iff ``Submission.DifferentialGeometry.Topology.moduleHomologyClass_eq_iff

end DifferentialGeometry.Topology
