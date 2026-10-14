import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.ModuleCat.Abelian

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
  {A K : ChainComplex (ModuleCat.{v} k) ℕ} (i : A ⟶ K)

def cokernelDescAt (n : ℕ) {M : ModuleCat.{v} k} (φ : K.X n ⟶ M) (hφ : i.f n ≫ φ = 0) :
    (_root_.CategoryTheory.Limits.cokernel i).X n ⟶ M :=
  (PreservesCokernel.iso (_root_.HomologicalComplex.eval _ _ n) i).hom ≫
    cokernel.desc (i.f n) φ hφ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.cokernelDescAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.cokernelDescAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.cokernelDescAt ``Submission.DifferentialGeometry.HomologicalComplex.cokernelDescAt


@[reassoc (attr := simp)]
theorem cokernel_π_descAt (n : ℕ) {M : ModuleCat.{v} k} (φ : K.X n ⟶ M) (hφ : i.f n ≫ φ = 0) :
    (cokernel.π i).f n ≫ cokernelDescAt i n φ hφ = φ := by
  exact (PreservesCokernel.π_iso_hom_assoc (_root_.HomologicalComplex.eval _ _ n) i
    (cokernel.desc ((_root_.HomologicalComplex.eval _ _ n).map i) φ hφ)).trans
      (cokernel.π_desc _ _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.cokernel_π_descAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.cokernel_π_descAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.cokernel_π_descAt ``Submission.DifferentialGeometry.HomologicalComplex.cokernel_π_descAt

variable (a : A ⟶ A) (b : K ⟶ K) (hab : i ≫ b = a ≫ i)


def cokernelEndomorphism : _root_.CategoryTheory.Limits.cokernel i ⟶ _root_.CategoryTheory.Limits.cokernel i := cokernel.map i i a b hab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.cokernelEndomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.cokernelEndomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.cokernelEndomorphism ``Submission.DifferentialGeometry.HomologicalComplex.cokernelEndomorphism


@[reassoc (attr := simp)]
theorem cokernel_π_endomorphism :
    cokernel.π i ≫ cokernelEndomorphism i a b hab = b ≫ cokernel.π i :=
  cokernel.π_desc _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.cokernel_π_endomorphism then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.cokernel_π_endomorphism"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.cokernel_π_endomorphism ``Submission.DifferentialGeometry.HomologicalComplex.cokernel_π_endomorphism

variable (H : Homotopy b (𝟙 K))
  (hA : ∀ n : ℕ, A.X n ⟶ A.X (n + 1))
  (hcompat : ∀ n, i.f n ≫ H.hom n (n + 1) = hA n ≫ i.f (n + 1))

include hcompat in
private theorem desc_condition (n : ℕ) :
    i.f n ≫ (H.hom n (n + 1) ≫ (cokernel.π i).f (n + 1)) = 0 := by
  rw [← Category.assoc, hcompat, Category.assoc]
  have h := _root_.HomologicalComplex.congr_hom (cokernel.condition i) (n + 1)
  simp only [_root_.HomologicalComplex.comp_f, _root_.HomologicalComplex.zero_f_apply] at h
  rw [h, _root_.CategoryTheory.Limits.comp_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.HomologicalComplex.desc_condition
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.HomologicalComplex.desc_condition target :: scope.openDecls } }

private def descHom (n : ℕ) : (_root_.CategoryTheory.Limits.cokernel i).X n ⟶ (_root_.CategoryTheory.Limits.cokernel i).X (n + 1) :=
  cokernelDescAt i n (H.hom n (n + 1) ≫ (cokernel.π i).f (n + 1))
    (desc_condition i b H hA hcompat n)

run_cmd do
  let target := ``Submission.DifferentialGeometry.HomologicalComplex.descHom
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.HomologicalComplex.descHom target :: scope.openDecls } }

private theorem projection_descHom (n : ℕ) :
    (cokernel.π i).f n ≫ descHom i b H hA hcompat n =
      H.hom n (n + 1) ≫ (cokernel.π i).f (n + 1) :=
  cokernel_π_descAt _ _ _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.HomologicalComplex.projection_descHom
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.HomologicalComplex.projection_descHom target :: scope.openDecls } }

def cokernelHomotopy : Homotopy (cokernelEndomorphism i a b hab) (𝟙 (_root_.CategoryTheory.Limits.cokernel i)) where
  hom n m := if h : n + 1 = m then
    descHom i b H hA hcompat n ≫ _root_.CategoryTheory.eqToHom (congrArg (_root_.CategoryTheory.Limits.cokernel i).X h) else 0
  zero n m hnm := by
    change ¬ n + 1 = m at hnm
    exact dif_neg hnm
  comm n := by
    have hπ : (cokernel.π i).f n ≫ (cokernelEndomorphism i a b hab).f n =
        b.f n ≫ (cokernel.π i).f n :=
      _root_.HomologicalComplex.congr_hom (cokernel_π_endomorphism i a b hab) n
    have hh := H.comm n
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at hh ⊢
      simp only [dif_pos rfl, _root_.CategoryTheory.eqToHom_refl, Category.comp_id,
        _root_.HomologicalComplex.id_f, zero_add] at hh ⊢
      apply (_root_.CategoryTheory.cancel_epi ((cokernel.π i).f 0)).mp
      rw [hπ, Preadditive.comp_add, Category.comp_id, ← Category.assoc,
        projection_descHom, Category.assoc, (cokernel.π i).comm, ← Category.assoc]
      exact congrArg (fun f ↦ f ≫ (cokernel.π i).f 0) hh |>.trans (by simp)
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at hh ⊢
      simp only [dif_pos rfl, _root_.CategoryTheory.eqToHom_refl, Category.comp_id,
        _root_.HomologicalComplex.id_f] at hh ⊢
      apply (_root_.CategoryTheory.cancel_epi ((cokernel.π i).f (n + 1))).mp
      rw [hπ]
      simp only [Preadditive.comp_add, Category.comp_id]
      rw [← Category.assoc ((cokernel.π i).f (n + 1)), (cokernel.π i).comm]
      rw [Category.assoc, projection_descHom]
      rw [← Category.assoc ((cokernel.π i).f (n + 1)), projection_descHom,
        Category.assoc, (cokernel.π i).comm]
      simpa only [Preadditive.add_comp, Category.assoc, Category.id_comp] using
        congrArg (fun f ↦ f ≫ (cokernel.π i).f (n + 1)) hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.cokernelHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.cokernelHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.cokernelHomotopy ``Submission.DifferentialGeometry.HomologicalComplex.cokernelHomotopy

end DifferentialGeometry.HomologicalComplex
