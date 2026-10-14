import Submission.DifferentialGeometry.Topology.Homology.Naturality
import Submission.DifferentialGeometry.Topology.Morse.Strip.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.Submission.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.CategoryTheory.Limits
open scoped _root_.ContinuousMap

noncomputable section

universe u

namespace DifferentialGeometry.Topology

open _root_.Submission.DifferentialGeometry.Topology.SingularPair

def relHomologyVanishes (X : Type u) [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ n, _root_.CategoryTheory.Limits.IsZero (relativeHomology integerCoefficients (TopCat.of X) A n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.relHomologyVanishes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.relHomologyVanishes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.relHomologyVanishes ``Submission.DifferentialGeometry.Topology.relHomologyVanishes

theorem relHomologyVanishes.congr {X : Type u} [TopologicalSpace X] {B B' A A' : Set X}
    (hB : B = B') (hA : A = A') (h : relHomologyVanishes B (Subtype.val ⁻¹' A)) :
    relHomologyVanishes B' (Subtype.val ⁻¹' A') := by
  subst hB hA
  exact h

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.relHomologyVanishes
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.relHomologyVanishes.congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.relHomologyVanishes.congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.relHomologyVanishes.congr ``Submission.DifferentialGeometry.Topology.relHomologyVanishes.congr

def homeomorphPreimageVal {X : Type u} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) :
    (Subtype.val ⁻¹' A : Set B) ≃ₜ A where
  toFun x := ⟨x.1.1, x.2⟩
  invFun y := ⟨⟨y.1, hAB y.2⟩, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homeomorphPreimageVal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homeomorphPreimageVal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homeomorphPreimageVal ``Submission.DifferentialGeometry.Topology.homeomorphPreimageVal

theorem isHomotopyEquivInclusion.relHomologyVanishes {X : Type u} [TopologicalSpace X]
    {A B : Set X} (h : isHomotopyEquivInclusion A B) :
    relHomologyVanishes B (Subtype.val ⁻¹' A) := by
  have hAB : A ⊆ B := h.subset
  obtain ⟨e, he⟩ := h
  let e' : (Subtype.val ⁻¹' A : Set B) ≃ₕ B := (homeomorphPreimageVal hAB).toHomotopyEquiv.trans e
  have hincl : TopCat.ofHom e'.toFun = incl (TopCat.of B) (Subtype.val ⁻¹' A) := by
    ext x
    exact he _
  have hiso : ∀ n, _root_.CategoryTheory.IsIso (inclMap integerCoefficients (TopCat.of B) (Subtype.val ⁻¹' A) n) := fun n => by
    rw [inclMap_eq_singularHomologyMap, ← hincl]
    exact isIso_singularHomologyMap_of_homotopyEquiv integerCoefficients e' n
  have hπ : ∀ n, relπ integerCoefficients (TopCat.of B) (Subtype.val ⁻¹' A) n = 0 := fun n =>
    (les_exact₂ integerCoefficients _ _ n).epi_f_iff.1 (haveI := hiso n; inferInstance)
  have hδ : ∀ n, δ integerCoefficients (TopCat.of B) (Subtype.val ⁻¹' A) n = 0 := fun n =>
    (les_exact₁ integerCoefficients _ _ n).mono_g_iff.1 (haveI := hiso n; inferInstance)
  intro n
  cases n with
  | zero =>
    let : HasCoproducts.{u} (ModuleCat.{u} ℤ) := fun _ => inferInstance
    have : _root_.CategoryTheory.Epi (relπ integerCoefficients (TopCat.of B) (Subtype.val ⁻¹' A) 0) :=
      inferInstanceAs (_root_.CategoryTheory.Epi ((pair (TopCat.of B) (Subtype.val ⁻¹' A)).homologyπ integerCoefficients 0))
    exact IsZero.of_epi_eq_zero _ (hπ 0)
  | succ n => exact (les_exact₃ integerCoefficients _ _ n).isZero_X₂ (hπ (n + 1)) (hδ n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isHomotopyEquivInclusion.relHomologyVanishes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isHomotopyEquivInclusion.relHomologyVanishes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isHomotopyEquivInclusion.relHomologyVanishes ``Submission.DifferentialGeometry.Topology.isHomotopyEquivInclusion.relHomologyVanishes

end DifferentialGeometry.Topology

end
