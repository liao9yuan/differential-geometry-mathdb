import Submission.DifferentialGeometry.Topology.Homology.Subdivision.Barycentric
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Tactic.Abel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.Simplicial

universe u

namespace DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)

local notation "K" => _root_.SSet.chainComplex (TopCat.toSSet.obj (TopCat.of E)) R
local notation "S" => SSet.chainComplexMap (affineStraightening (E := E)) R
local notation "B" => affineSubdivision (E := E) R
local notation "F" => (B - S)

private theorem straightening_f_idempotent (n : ℕ) : (S).f n ≫ (S).f n = (S).f n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, SSet.ι_chainComplexMap_f]
  change (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
      ((affineStraightening (E := E)).app (_root_.Opposite.op ⦋n⦌)
        (affineSingularSimplex (singularSimplexVertices σ))) = _
  rw [affineStraightening_affineSingularSimplex]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.straightening_f_idempotent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.straightening_f_idempotent target :: scope.openDecls } }

private theorem difference_f_straightening (n : ℕ) : (F).f n ≫ (S).f n = (F).f n := by
  rw [HomologicalComplex.sub_f_apply, Preadditive.sub_comp, affineSubdivision_f,
    affineSubdivisionMap_straightening, straightening_f_idempotent]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.difference_f_straightening
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.difference_f_straightening target :: scope.openDecls } }

private theorem difference_f_zero : (F).f 0 = 0 := by
  rw [HomologicalComplex.sub_f_apply, affineSubdivision_f, affineSubdivisionMap_zero,
    affineStraightening_f_zero, sub_self]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.difference_f_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.difference_f_zero target :: scope.openDecls } }


theorem affineCone_fills_cycle (p : E) {n : ℕ} {T : ModuleCat.{u} k}
    (z : T ⟶ (K).X (n + 1)) (hz : z ≫ (K).d (n + 1) n = 0)
    (haff : z ≫ (S).f (n + 1) = z) :
    z ≫ affineCone R p (n + 1) ≫ (K).d (n + 2) (n + 1) = z := by
  rw [eq_sub_of_add_eq (affineCone_boundary R p n), Preadditive.comp_sub, haff,
    ← Category.assoc, hz, _root_.CategoryTheory.Limits.zero_comp, sub_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineCone_fills_cycle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineCone_fills_cycle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineCone_fills_cycle ``Submission.DifferentialGeometry.Homology.affineCone_fills_cycle


def affineSubdivisionHomotopyMap (n : ℕ) : (K).X n ⟶ (K).X (n + 1) :=
  match n with
  | 0 => 0
  | n + 1 => Sigma.desc (fun σ ↦
      ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫ (F).f (n + 1) -
        (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫ (K).d (n + 1) n ≫
          affineSubdivisionHomotopyMap n) ≫ affineCone R (singularSimplexBarycenter σ) (n + 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSubdivisionHomotopyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSubdivisionHomotopyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSubdivisionHomotopyMap ``Submission.DifferentialGeometry.Homology.affineSubdivisionHomotopyMap


@[simp]
theorem affineSubdivisionHomotopyMap_zero : affineSubdivisionHomotopyMap (E := E) R 0 = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSubdivisionHomotopyMap_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSubdivisionHomotopyMap_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSubdivisionHomotopyMap_zero ``Submission.DifferentialGeometry.Homology.affineSubdivisionHomotopyMap_zero


@[reassoc]
theorem ι_affineSubdivisionHomotopyMap_succ (n : ℕ)
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n + 1⦌) :
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫
        affineSubdivisionHomotopyMap R (n + 1) =
      ((TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫ (F).f (n + 1) -
        (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫ (K).d (n + 1) n ≫
          affineSubdivisionHomotopyMap R n) ≫
        affineCone R (singularSimplexBarycenter σ) (n + 1) :=
  Sigma.ι_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.ι_affineSubdivisionHomotopyMap_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.ι_affineSubdivisionHomotopyMap_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.ι_affineSubdivisionHomotopyMap_succ ``Submission.DifferentialGeometry.Homology.ι_affineSubdivisionHomotopyMap_succ


theorem affineSubdivisionHomotopyMap_straightening (n : ℕ) :
    affineSubdivisionHomotopyMap (E := E) R n ≫ (S).f (n + 1) =
      affineSubdivisionHomotopyMap R n := by
  cases n with
  | zero => rw [affineSubdivisionHomotopyMap_zero, _root_.CategoryTheory.Limits.zero_comp]
  | succ n =>
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, ι_affineSubdivisionHomotopyMap_succ]
    simp only [Category.assoc, affineCone_straightening]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSubdivisionHomotopyMap_straightening then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSubdivisionHomotopyMap_straightening"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSubdivisionHomotopyMap_straightening ``Submission.DifferentialGeometry.Homology.affineSubdivisionHomotopyMap_straightening

private def homotopyPrev (n : ℕ) : (K).X n ⟶ (K).X n :=
  match n with
  | 0 => 0
  | n + 1 => (K).d (n + 1) n ≫ affineSubdivisionHomotopyMap R n

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.homotopyPrev
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.homotopyPrev target :: scope.openDecls } }

private theorem d_homotopyPrev (n : ℕ) : (K).d (n + 1) n ≫ homotopyPrev R n = 0 := by
  cases n with
  | zero => exact _root_.CategoryTheory.Limits.comp_zero
  | succ n =>
    change (K).d (n + 2) (n + 1) ≫
      ((K).d (n + 1) n ≫ affineSubdivisionHomotopyMap R n) = 0
    rw [← Category.assoc, (K).d_comp_d, _root_.CategoryTheory.Limits.zero_comp]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.d_homotopyPrev
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.d_homotopyPrev target :: scope.openDecls } }

private theorem affineSubdivisionHomotopyMap_comm_aux (n : ℕ) :
    (F).f n = homotopyPrev R n +
      affineSubdivisionHomotopyMap R n ≫ (K).d (n + 1) n := by
  induction n with
  | zero => simp only [homotopyPrev, affineSubdivisionHomotopyMap_zero,
      difference_f_zero, _root_.CategoryTheory.Limits.zero_comp, add_zero]
  | succ n hn =>
    change (F).f (n + 1) = (K).d (n + 1) n ≫ affineSubdivisionHomotopyMap R n +
      affineSubdivisionHomotopyMap R (n + 1) ≫ (K).d (n + 2) (n + 1)
    apply SSet.chainComplex_hom_ext
    intro σ
    simp only [Preadditive.comp_add]
    rw [← Category.assoc _ (affineSubdivisionHomotopyMap R (n + 1)),
      ι_affineSubdivisionHomotopyMap_succ, Category.assoc]
    let z : R ⟶ (K).X (n + 1) :=
      (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫ (F).f (n + 1) -
        (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫ (K).d (n + 1) n ≫
          affineSubdivisionHomotopyMap R n
    have hza : z ≫ (S).f (n + 1) = z := by
      dsimp only [z]
      simp only [Preadditive.sub_comp, Category.assoc, difference_f_straightening,
        affineSubdivisionHomotopyMap_straightening]
    have hzc : z ≫ (K).d (n + 1) n = 0 := by
      dsimp only [z]
      simp only [Preadditive.sub_comp, Category.assoc]
      rw [(F).comm, hn]
      simp only [Preadditive.comp_add]
      rw [d_homotopyPrev]
      simp only [_root_.CategoryTheory.Limits.comp_zero, zero_add, sub_self]
    rw [affineCone_fills_cycle R (singularSimplexBarycenter σ) z hzc hza]
    dsimp only [z]
    abel

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.affineSubdivisionHomotopyMap_comm_aux
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.affineSubdivisionHomotopyMap_comm_aux target :: scope.openDecls } }


theorem affineSubdivisionHomotopyMap_comm (n : ℕ) :
    (F).f (n + 1) = (K).d (n + 1) n ≫ affineSubdivisionHomotopyMap R n +
      affineSubdivisionHomotopyMap R (n + 1) ≫ (K).d (n + 2) (n + 1) :=
  affineSubdivisionHomotopyMap_comm_aux R (n + 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSubdivisionHomotopyMap_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSubdivisionHomotopyMap_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSubdivisionHomotopyMap_comm ``Submission.DifferentialGeometry.Homology.affineSubdivisionHomotopyMap_comm

def affineSubdivisionHomotopy : Homotopy (B) (S) where
  hom i j := if h : i + 1 = j then
    affineSubdivisionHomotopyMap R i ≫ _root_.CategoryTheory.eqToHom (congrArg (K).X h) else 0
  zero i j hij := by
    change ¬ i + 1 = j at hij
    exact dif_neg hij
  comm n := by
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dif_pos rfl, _root_.CategoryTheory.eqToHom_refl, Category.comp_id,
        affineSubdivisionHomotopyMap_zero, _root_.CategoryTheory.Limits.zero_comp, zero_add,
        affineSubdivision_f, affineSubdivisionMap_zero, affineStraightening_f_zero]
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dif_pos rfl, _root_.CategoryTheory.eqToHom_refl, Category.comp_id]
      exact sub_eq_iff_eq_add.mp (affineSubdivisionHomotopyMap_comm R n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSubdivisionHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSubdivisionHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSubdivisionHomotopy ``Submission.DifferentialGeometry.Homology.affineSubdivisionHomotopy


@[simp]
theorem affineSubdivisionHomotopy_hom (n : ℕ) :
    (affineSubdivisionHomotopy (E := E) R).hom n (n + 1) =
      affineSubdivisionHomotopyMap R n := by
  change (if h : n + 1 = n + 1 then
    affineSubdivisionHomotopyMap R n ≫ _root_.CategoryTheory.eqToHom (congrArg (K).X h) else 0) = _
  rw [dif_pos rfl, _root_.CategoryTheory.eqToHom_refl, Category.comp_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSubdivisionHomotopy_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSubdivisionHomotopy_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSubdivisionHomotopy_hom ``Submission.DifferentialGeometry.Homology.affineSubdivisionHomotopy_hom

end DifferentialGeometry.Homology
